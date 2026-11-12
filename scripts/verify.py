"""Audit declarations, export proofs, and replay a pinned source revision."""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "formal" / "object_language"
AUDIT = Path(os.environ.get("ERDOS597_AUDIT_DIR", str(ROOT / ".audit"))).resolve()
OUT = AUDIT / "external"
BIN = Path(os.environ.get("ERDOS597_LEAN_ROOT", r"F:\e597verify-runtime\lean-4.35.0-rc3")) / "bin"
EXPORT = OUT / "proof_terms.ndjson"
ALLOWED = ["propext", "Classical.choice", "Quot.sound"]
PRIMITIVES = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight",
    "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat", "String", "String.mk",
    "Char", "optParam", "autoParam", "semiOutParam", "outParam",
    "Quot", "Quot.mk", "Quot.lift", "Quot.ind",
]


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(64 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def write_record(name, value):
    (OUT / f"{name}.json").write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def executable(name):
    return BIN / (name + ".exe" if os.name == "nt" else name)


def source_binding():
    tracked = subprocess.check_output(["git", "ls-files"], cwd=ROOT, text=True).splitlines()
    files = {name: digest(ROOT / name) for name in tracked}
    for name in ["AxiomAudit.lean", "targets.json"]:
        files["audit/" + name] = digest(AUDIT / name)
    artifacts = []
    for directory in [PROJECT / ".lake/build/lib/lean", AUDIT]:
        paths = directory.rglob("*.olean*") if directory.name == "lean" else directory.glob("AxiomAudit.olean*")
        for path in sorted(paths):
            artifacts.append({"path": str(path), "length": path.stat().st_size, "sha256": digest(path)})
    lock = json.loads((PROJECT / "lake-manifest.json").read_text(encoding="utf-8"))
    dependencies = []
    for package in lock["packages"]:
        if package["type"] == "path":
            directory = (PROJECT / package["dir"]).resolve()
            prefix = directory.relative_to(ROOT).as_posix() + "/"
            dependencies.append({"name": package["name"], "directory": str(directory),
                "files": {name: files[name] for name in files if name.startswith(prefix)},
                "compiled_modules": [{"path": str(path), "length": path.stat().st_size, "sha256": digest(path)}
                    for path in sorted((directory / ".lake/build/lib/lean").rglob("*.olean*"))]})
        else:
            directory = PROJECT / ".lake/packages" / package["name"].strip("«»")
            actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=directory, text=True).strip()
            if actual != package["rev"]:
                raise RuntimeError("Dependency revision mismatch for " + package["name"])
            status = subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"], cwd=directory, text=True)
            if status:
                raise RuntimeError("Tracked dependency files are modified for " + package["name"])
            dependencies.append({"name": package["name"], "revision": actual, "tracked_files_clean": True})
    return {"commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "git_status": subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True),
        "git_remotes": subprocess.check_output(["git", "remote", "-v"], cwd=ROOT, text=True),
        "files": files, "compiled_modules": artifacts, "local_dependencies": dependencies}


def environment():
    env = os.environ.copy()
    env.pop("LEAN_SRC_PATH", None)
    lock = json.loads((PROJECT / "lake-manifest.json").read_text(encoding="utf-8"))
    env["LEAN_PATH"] = os.pathsep.join([
        str(AUDIT), str(PROJECT / ".lake/build/lib/lean"),
        *(str((PROJECT / item["dir"] if item["type"] == "path" else
               PROJECT / ".lake/packages" / item["name"].strip("«»")) / ".lake/build/lib/lean")
          for item in lock["packages"]),
    ])
    scratch = AUDIT / "scratch"
    scratch.mkdir(exist_ok=True)
    env.update(TEMP=str(scratch), TMP=str(scratch), LEAN_ABORT_ON_PANIC="1",
               MATHLIB_CACHE_DIR=str(AUDIT / "cache/compressed_archives"), LEAN_NUM_THREADS="1")
    return env


def run(name, args, cwd=PROJECT):
    log = OUT / f"{name}.log"
    record = {"command": args, "cwd": str(cwd), "status": "running",
              "started_utc": datetime.now(timezone.utc).isoformat(),
              "binary_sha256": digest(Path(args[0]))}
    start = time.monotonic()
    with log.open("wb") as stream:
        process = subprocess.Popen(args, cwd=cwd, env=environment(), stdout=stream,
                                   stderr=subprocess.STDOUT)
        record["pid"] = process.pid
        write_record(name, record)
        process.wait()
    record.update(status="completed", exit_code=process.returncode,
                  seconds=round(time.monotonic() - start, 3), log=str(log),
                  log_sha256=digest(log), log_length=log.stat().st_size)
    write_record(name, record)
    print(json.dumps({"name": name, **record}), flush=True)
    return record


def audit():
    before = source_binding()
    if before["git_status"]:
        raise RuntimeError("A clean source pin is required")
    result = run("axiom_audit", [str(executable("lean")), "-t", "0", "-j", "1", "-o",
                                str(AUDIT / "AxiomAudit.olean"), str(AUDIT / "AxiomAudit.lean")], AUDIT)
    if result["exit_code"]:
        raise RuntimeError("The declaration audit did not compile")
    text = Path(result["log"]).read_text(encoding="utf-8", errors="replace")
    parsed = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text))
    targets = json.loads((AUDIT / "targets.json").read_text(encoding="utf-8"))["targets"]
    entries = []
    for target in targets:
        name = target["declaration"]
        if name in parsed:
            axioms = [value.strip() for value in parsed[name].split(",") if value.strip()]
        elif f"'{name}' does not depend on any axioms" in text:
            axioms = []
        else:
            raise RuntimeError("Missing axiom audit for " + name)
        if not set(axioms) <= set(ALLOWED):
            raise RuntimeError("Unapproved dependency in " + name)
        entries.append({**target, "axioms": axioms})
    # The audit module is newly built, so compare source files separately here.
    after = source_binding()
    unchanged = (before["files"] == after["files"] and before["commit"] == after["commit"]
                 and not after["git_status"])
    record = {"targets": entries, "source_before": before, "source_after": after,
              "source_unchanged": unchanged, "all_standard_axioms": True,
              "claimed_scope": "Both original Erdos 597 clauses and the two-hub target refinement",
              "audit": result}
    write_record("axioms", record)
    if not unchanged:
        raise RuntimeError("Source changed during audit")


def export_proofs():
    checked = json.loads((OUT / "axioms.json").read_text(encoding="utf-8"))
    before = source_binding()
    if not checked["all_standard_axioms"] or before != checked["source_after"]:
        raise RuntimeError("The current source-bound declaration audit is required")
    names = [item["declaration"] for item in checked["targets"]]
    export_roots = ["Erdos597Object.Verification.exportRoot"]
    command = [str(executable("leanexport")), "AxiomAudit", "--", *export_roots, *ALLOWED, *PRIMITIVES]
    start = time.monotonic()
    record = {"command": command, "targets": names, "export_roots": export_roots,
              "allowed_axioms": ALLOWED,
              "additional_builtins": PRIMITIVES, "source_before": before,
              "started_utc": datetime.now(timezone.utc).isoformat(), "status": "running",
              "binary_sha256": digest(executable("leanexport"))}
    with EXPORT.open("wb") as output, (OUT / "export_stderr.log").open("wb") as errors:
        process = subprocess.Popen(command, cwd=PROJECT, env=environment(), stdout=output, stderr=errors)
        record["pid"] = process.pid
        write_record("export", record)
        process.wait()
    after = source_binding()
    record.update(status="completed", exit_code=process.returncode,
                  seconds=round(time.monotonic() - start, 3), source_after=after,
                  source_unchanged=before == after, export=str(EXPORT),
                  export_length=EXPORT.stat().st_size, export_sha256=digest(EXPORT),
                  stderr_sha256=digest(OUT / "export_stderr.log"))
    write_record("export", record)
    print(json.dumps({key: record[key] for key in ["status", "exit_code", "seconds",
          "source_unchanged", "export_length", "export_sha256"]}), flush=True)
    if process.returncode or before != after:
        raise RuntimeError("The proof export or source binding failed")


def replay():
    exported = json.loads((OUT / "export.json").read_text(encoding="utf-8"))
    if exported["export_sha256"] != digest(EXPORT) or source_binding() != exported["source_after"]:
        raise RuntimeError("The completed source-bound export is required")
    write_record("nanoda_config", {
        "export_file_path": str(EXPORT), "use_stdin": False, "permitted_axioms": ALLOWED,
        "unpermitted_axiom_hard_error": True, "num_threads": 1,
        "nat_extension": True, "string_extension": True, "print_success_message": True,
    })
    commands = [
        ("lean_paranoid", [str(executable("leanchecker-paranoid")), "--silent", "--from-export", str(EXPORT)]),
        ("lean4lean", [str(executable("lean4lean")), "--import", str(EXPORT)]),
        ("nanoda", [str(executable("nanoda_bin")), str(OUT / "nanoda_config.json")]),
        ("con_leche", [str(executable("con-leche")), "--verified", "--jobs=1", "--progress=10000", str(EXPORT)]),
        ("con_ron", [str(executable("con-ron")), "--verified", "--jobs=1", "--progress=10000", str(EXPORT)]),
        ("lean_default_export", [str(executable("leanchecker")), "--silent", "--from-export", str(EXPORT)]),
    ]
    results = [run(name, command, OUT) for name, command in commands]
    record = {"utc": datetime.now(timezone.utc).isoformat(), "checks": results,
              "export_sha256": digest(EXPORT), "source_unchanged": source_binding() == exported["source_after"],
              "all_completed_successfully": all(r["exit_code"] == 0 for r in results),
              "claimed_scope": "Both original Erdos 597 clauses and the two-hub target refinement",
              "verifier_sha256": digest(Path(__file__))}
    write_record("results", record)
    print(json.dumps({key: value for key, value in record.items() if key != "checks"}), flush=True)
    if not record["source_unchanged"] or not record["all_completed_successfully"]:
        raise RuntimeError("A proof checker or source binding failed")


if __name__ == "__main__":
    OUT.mkdir(parents=True, exist_ok=True)
    phase = sys.argv[1] if len(sys.argv) > 1 else "all"
    if phase in {"audit", "all"}:
        audit()
    if phase in {"export", "all"}:
        export_proofs()
    if phase in {"check", "all"}:
        replay()
