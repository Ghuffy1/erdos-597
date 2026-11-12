# Reproduction

Start with a checkout that preserves the committed line endings.

```text
git -c core.autocrlf=false clone https://github.com/Ghuffy1/erdos-597.git
cd erdos-597
git checkout 279825a39739918a2553880a32ec9ab1dee1f780
```

The exact toolchain is **Lean 4.35.0-rc3**. Both projects contain
`lean-toolchain`, `lakefile.toml` and complete `lake-manifest.json` lockfiles.
The principal project is `formal/object_language`. Its adjacent local dependency
is `formal/single_file_conditional`.

On the prepared Windows workspace, use the direct pinned executable and keep
the checkout, temporary directory and caches on F:.

```powershell
$env:ERDOS597_LEAN_ROOT = 'F:\e597verify-runtime\lean-4.35.0-rc3'
$env:ERDOS597_AUDIT_DIR = 'F:\erdos597-audit'
python scripts/prepare_audit.py
python scripts/run_check.py normal_build build
python scripts/check_sources.py
python scripts/run_check.py solution_entry --direct -j 1 -o .lake/build/lib/lean/Erdos597Object/Solution.olean Erdos597Object/Solution.lean
python scripts/verify.py all
python scripts/audit_export.py "$env:ERDOS597_AUDIT_DIR/external"
```

`prepare_audit.py` enumerates all 1,763 declarations and definitions in the
reviewed development and generates the declaration/axiom checks.
`check_sources.py` re-elaborates every tracked local Lean source in local-import
dependency order, using one compiler process and one thread at a time. It retains
per-module logs and source/output hashes. Public dependency objects come from
the pinned dependency build. The standard `lake build` can prepare those objects.
`verify.py` checks the pinned source state, audits transitive axioms, exports
the proof terms and runs six sequential checker modes when the matching tools
are available in the selected runtime. Missing tools or failed checks cause
failure and must be reported. `audit_export.py` inspects the exported declaration
graph for unexpected axioms or unsafe declarations.

For a source build with the usual pinned toolchain installation, the core
commands are also

```text
cd formal/object_language
lake build
lake env lean Erdos597Object/Solution.lean
```

The default build includes the entry point and every project module. The local
dependency path is relative and requires no original private workspace path.
Public dependency revisions must match the lockfiles. The available checked
cache may be reused only with its content/revision provenance retained.

The verification report identifies the exact selected proof commit, the commands
actually executed, cache reuse, export hashes and checker results. A previous
revision's successful result is not a report for a changed proof revision.
