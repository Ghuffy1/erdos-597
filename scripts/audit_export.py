"""Inspect the exported proof closure without relying on a checker's summary."""

from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import sys


root = Path(__file__).resolve().parents[1]
audit = Path(os.environ.get("ERDOS597_AUDIT_DIR", str(root / ".audit"))).resolve()
directory = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else audit / "external"
export_record = json.loads((directory / "export.json").read_text(encoding="utf-8"))
if export_record.get("exit_code") != 0:
    raise RuntimeError("The proof export must have completed successfully")
manifest_path = directory.parent / "targets.json"
manifest = json.loads(manifest_path.read_text(encoding="utf-8")) if manifest_path.exists() else {}
roles = {item["declaration"]: item.get("role", "theorem") for item in manifest.get("targets", [])}
names = {0: ""}
declarations = {}
counts = Counter()
unsafe = []
digest = hashlib.sha256()
metadata = None
lines = 0
with (directory / "proof_terms.ndjson").open("rb") as stream:
    for line in stream:
        digest.update(line)
        entry = json.loads(line)
        lines += 1
        counts.update(entry.keys())
        if "meta" in entry:
            metadata = entry["meta"]
        if "in" in entry:
            node = entry.get("str", entry.get("num"))
            suffix = node["str"] if "str" in entry else str(node["i"])
            prefix = names[node["pre"]]
            names[entry["in"]] = prefix + "." + suffix if prefix else suffix
        for kind in ["def", "thm", "opaque", "axiom", "quot"]:
            if kind in entry:
                value = entry[kind]
                name = names[value["name"]]
                declarations[name] = {"kind": kind, "type": value["type"]}
                if value.get("isUnsafe") or value.get("safety", "safe") != "safe":
                    unsafe.append(name)
        if "inductive" in entry:
            for group in ["types", "ctors", "recs"]:
                for value in entry["inductive"][group]:
                    name = names[value["name"]]
                    declarations[name] = {"kind": group, "type": value["type"]}
                    if value.get("isUnsafe"):
                        unsafe.append(name)

targets = {name: declarations.get(name) for name in export_record["targets"]}
axioms = sorted(name for name, value in declarations.items() if value["kind"] == "axiom")
# Definition targets may be inductive structure types. Their constructors and
# recursors are part of the exported closure checked by the kernel checkers.
success = (digest.hexdigest() == export_record["export_sha256"]
           and all(value and value["kind"] in
                   ({"def", "opaque", "types"} if roles.get(name) == "definition" else {"thm"})
                   for name, value in targets.items())
           and axioms == sorted(export_record["allowed_axioms"]) and not unsafe)
result = {
    "utc": datetime.now(timezone.utc).isoformat(), "export_sha256": digest.hexdigest(),
    "metadata": metadata, "json_lines": lines, "record_counts": dict(counts),
    "declarations": len(declarations), "target_count": len(targets), "targets": targets,
    "axioms": axioms, "unsafe_declarations": unsafe, "passed": success,
}
(directory / "structure_audit.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps({key: value for key, value in result.items() if key not in {"targets", "record_counts"}}))
if not success:
    raise RuntimeError("Export declaration or safety check failed")
