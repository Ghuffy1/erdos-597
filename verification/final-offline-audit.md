# Final offline submission audit

The final local audit completed on 2026-11-12T21:01:33.887709+00:00 and passed. It
concerns proof commit `279825a39739918a2553880a32ec9ab1dee1f780`. The audited checkout was
`fa7fdcba6400539108c5b4a3ba6e15e25417f828`. All formal source hashes agree with the
selected proof. The manuscript's six pages were reread and visually inspected.
Its authors, correspondence addresses, embedded fonts and AI acknowledgment
passed the checks.

The previously completed normal Lake build has exit code 0
and a recorded duration of 253.5 seconds. Its source equivalence
was rechecked for this submission. All eight subsequent source edits were
comment-only and had already been re-elaborated successfully. A final full-
rehash pilot was stopped after 647 seconds of disk I/O contention. The audit
therefore reused the completed build and checked a fresh complete proof export.
The [build log](final-offline-build.txt) preserves the completed build's output
with local workspace prefixes normalized.

A fresh declaration audit checked all 1,763 targets with only `Classical.choice`,
`Quot.sound` and `propext`. The freshly exported proof has SHA-256
`6c2f6186d682841bb5f6c89656dce9b67e72763cd9450ea1e42f05b1ac151d69`. It exactly matches the export accepted by all six
recorded checker modes, whose results were reused after binary and log-hash
verification. The structural audit again found all targets and zero unsafe
declarations.

The independent internal mathematical reread passed both original clauses and
the bipartite refinement. The paper's fixed-finite-target independence proof and
the formal universal finite-sentence endpoint are identified separately in the
[scope record](../STATEMENT.md). The [detailed verification report](report.md)
retains the earlier evidence and trust limitations. Nanoda's one pretty-printer
diagnostic accompanies zero typechecker errors.

The final review also checked repository metadata, source pins, third-party
notices, file sizes, links, privacy and the catalog-only submission patch.
Original contributions retain reserved rights. Repository review routing is
assigned to its owner, Ghuffy1. The four authors retain equal contribution
credit. Each person's later claim, identity and representative authorization
remain subject to the prize process. JSP acceptance and first priority remain
pending independent review.

[Machine-readable audit](final-offline-audit.json)
