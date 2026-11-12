"""Run one pinned build or entry-point check and retain its evidence."""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time


root = Path(__file__).resolve().parents[1]
project = root / "formal" / "object_language"
output = Path(os.environ.get("ERDOS597_AUDIT_DIR", str(root / ".audit"))).resolve()
output.mkdir(parents=True, exist_ok=True)
if len(sys.argv) < 3:
    raise SystemExit("Usage: run_check.py NAME build | NAME --direct LEAN_ARGUMENTS")
name = sys.argv[1]
arguments = sys.argv[2:]
binary = Path(os.environ.get("ERDOS597_LEAN_ROOT", r"F:\e597verify-runtime\lean-4.35.0-rc3")) / "bin" / ("lake.exe" if os.name == "nt" else "lake")
if not binary.is_file():
    raise FileNotFoundError(f"F: Lean toolchain is unavailable: {binary}")
environment = os.environ.copy()
environment.pop("LEAN_PATH", None)
environment.pop("LEAN_SRC_PATH", None)
scratch = output / "scratch"
cache = output / "cache" / "compressed_archives"
scratch.mkdir(exist_ok=True)
cache.mkdir(parents=True, exist_ok=True)
environment.update(TEMP=str(scratch), TMP=str(scratch), MATHLIB_CACHE_DIR=str(cache),
                   MATHLIB_NO_CACHE_ON_UPDATE="1", LEAN_NUM_THREADS="1")
if arguments and arguments[0] == "--direct":
    lock = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8"))
    environment["LEAN_PATH"] = os.pathsep.join([
        str(project / ".lake" / "build" / "lib" / "lean"),
        *(str((project / item["dir"] if item["type"] == "path" else
               project / ".lake" / "packages" / item["name"].strip("«»")) /
              ".lake" / "build" / "lib" / "lean") for item in lock["packages"]),
    ])
    command = [str(binary.with_name("lean.exe" if os.name == "nt" else "lean")), "-t", "0", *arguments[1:]]
else:
    command = [str(binary), *arguments]
record = {"command": command, "cwd": str(project), "started_utc": datetime.now(timezone.utc).isoformat()}
start = time.monotonic()
log = output / f"{name}.log"
with log.open("wb") as stream:
    process = subprocess.Popen(command, cwd=project, env=environment, stdout=stream, stderr=subprocess.STDOUT)
    record.update({"pid": process.pid, "status": "running"})
    (output / f"{name}.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    try:
        process.wait(timeout=1800)
        record["status"] = "completed"
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait()
        record["status"] = "timeout"
record.update({"exit_code": process.returncode, "seconds": round(time.monotonic() - start, 3),
               "log": str(log), "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest()})
(output / f"{name}.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
print(json.dumps(record), flush=True)
sys.exit(process.returncode)
