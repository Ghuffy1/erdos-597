"""Re-elaborate every tracked local Lean source in dependency order."""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from graphlib import TopologicalSorter

root = Path(__file__).resolve().parents[1]
audit = Path(os.environ.get("ERDOS597_AUDIT_DIR", str(root / ".audit"))).resolve()
runtime = Path(os.environ.get("ERDOS597_LEAN_ROOT", r"F:\e597verify-runtime\lean-4.35.0-rc3"))
binary = runtime / "bin" / ("lean.exe" if os.name == "nt" else "lean")
audit.mkdir(parents=True, exist_ok=True)
logs = audit / "source_checks"
logs.mkdir(exist_ok=True)
scratch = audit / "scratch"
scratch.mkdir(exist_ok=True)

tracked = subprocess.check_output(["git", "ls-files", "*.lean"], cwd=root, text=True).splitlines()
sources = {}
for name in tracked:
    if not name.startswith("formal/"):
        continue
    path = root / name
    project = root / Path(*path.relative_to(root).parts[:2])
    module = ".".join(path.relative_to(project).with_suffix("").parts)
    if module in sources:
        raise RuntimeError("Duplicate local module: " + module)
    sources[module] = (path, project)

graph = {}
for module, (path, project) in sources.items():
    imports = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = re.match(r"^(?:public\s+)?import\s+(.+)", line)
        if match:
            imports.extend(match.group(1).split("--", 1)[0].split())
    graph[module] = set(imports).intersection(sources)
order = list(TopologicalSorter(graph).static_order())

manifest = json.loads((root / "formal/object_language/lake-manifest.json").read_text(encoding="utf-8"))
object_project = root / "formal/object_language"
environment = os.environ.copy()
environment.pop("LEAN_SRC_PATH", None)
environment["LEAN_PATH"] = os.pathsep.join([
    str(object_project / ".lake/build/lib/lean"),
    *(str((object_project / package["dir"] if package["type"] == "path" else
           object_project / ".lake/packages" / package["name"].strip("«»")) /
          ".lake/build/lib/lean") for package in manifest["packages"]),
])
environment.update(TEMP=str(scratch), TMP=str(scratch), LEAN_NUM_THREADS="1",
                   MATHLIB_CACHE_DIR=str(audit / "cache/compressed_archives"))
record_path = audit / "source_checks.json"
record = {"commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
          "started_utc": datetime.now(timezone.utc).isoformat(),
          "method": "sequential source elaboration in local import dependency order",
          "module_count": len(order), "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
          "checks": [], "status": "running"}
previous = {}
if record_path.exists():
    saved = json.loads(record_path.read_text(encoding="utf-8"))
    if saved.get("commit") == record["commit"]:
        previous = {item["module"]: item for item in saved["checks"] if item["exit_code"] == 0}
limit = int(sys.argv[1]) if len(sys.argv) > 1 else len(order)
for module in order[:limit]:
    path, project = sources[module]
    relative = path.relative_to(project)
    output = project / ".lake/build/lib/lean" / relative.with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    old = previous.get(module)
    if (old and old["source_sha256"] == hashlib.sha256(path.read_bytes()).hexdigest()
            and output.exists() and old["output_sha256"] == hashlib.sha256(output.read_bytes()).hexdigest()):
        record["checks"].append(old)
        continue
    command = [str(binary), "-t", "0", "-j", "1", "-o", str(output), str(relative)]
    log = logs / (module + ".log")
    start = time.monotonic()
    with log.open("wb") as stream:
        result = subprocess.run(command, cwd=project, env=environment,
                                stdout=stream, stderr=subprocess.STDOUT, timeout=600)
    item = {"module": module, "source": path.relative_to(root).as_posix(), "command": command,
            "exit_code": result.returncode, "seconds": round(time.monotonic() - start, 3),
            "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest()}
    if result.returncode == 0:
        item["output_sha256"] = hashlib.sha256(output.read_bytes()).hexdigest()
    record["checks"].append(item)
    record_path.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"module": module, "index": len(record["checks"]),
                      "total": len(order), "exit_code": result.returncode, "seconds": item["seconds"]}), flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
record["completed_utc"] = datetime.now(timezone.utc).isoformat()
record["status"] = "completed" if limit >= len(order) else "bounded_pilot_completed"
record_path.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
