# Verification report for Erdős 597

## Selected source and conclusion

This report concerns proof commit `279825a39739918a2553880a32ec9ab1dee1f780` on branch `main` of the prepared
Ghuffy1/erdos-597 repository. It is added in a later evidence commit. The
manuscript, mathematical declarations, toolchain pins and source manifest are
selected from the proof commit. Public release and JSP acceptance remain pending.

The completed checks support both original clauses of Erdős 597 and the
bipartite, connected, diameter-at-most-three refinement. The source-correspondence
review is an internal AI-assisted review. Independent human mathematical review,
individual contribution/identity verification and prize priority remain for JSP.

## Mathematical scope

| Requirement | Source endpoint | Review result |
| --- | --- | --- |
| Unrestricted universal assertion, exact ordinals and both forbidden subgraphs | `Solution.unrestricted_clause_false` | Negation of the original universal assertion |
| Finite K4-free targets, arbitrary finite carriers and weak graph copies | `AssertionInterpretation.finiteAssertion_set_iff_original` and `FiniteCodeBridge.finite_universal_iff_fin_codes` | Complete interpretation bridge |
| Negative ZFC model | `NegativePartitionModel.models_negative` | Constructed Boolean-valued model |
| Positive ZFC model | `PositivePartitionModel.final_models_finite_assertion` | Constructed Boolean-valued model |
| Finite-sentence syntactic independence | `Solution.finite_clause_independent` | Both unprovability directions |
| Consistency-qualified formulation | `Solution.finite_clause_relatively_independent` | Relative independence |
| Stronger unrestricted target | `Solution.bipartite_diameter_three_counterexample` | Exact aleph-one size, bipartite, connected, all pairwise distances at most three |

All `Solution` names have namespace prefix `Erdos597Object`. The blue-copy
convention is injective and edge preserving. Red sets have the inherited ordinal
order type. The model endpoints carry no external CH, MA, CCC, density or assumed
conditional-derivation premise. The metatheory uses ordinary classical Lean.
[Statement and full names](../STATEMENT.md)

The paper also proves independence for a fixed finite target. The formal
first-order independence endpoint concerns the universal finite sentence.
[Manuscript](../paper/Erdos_597_Proof.pdf)

## Build and source correspondence

The preserved complete project build succeeded on 12 November 2026 in
253.5 seconds with 3,508 Lake jobs. Its source commit was
`3b7088e5e679a99a565a088b42fe84070762faa0`, with adjacent dependency commit
`27621648668ed3444ef3833bb1250305d04af75d`. That complete development supplied
the preparation's verified build cache. The two locked source projects contain
250 Lean source files and 257 total source/configuration/license files.

Repackaging introduced eight comment-only updates, comprising five prominent
third-party modification notices and three explanatory status corrections.
Token comparison after removal of comments verifies that the mathematical
source content agrees with the checked development. Each of the eight updated
files was re-elaborated successfully in the prepared checkout. A five-file
single-thread pilot and six additional source checks are retained. Public
dependency commits and clean tracked state were checked against the lockfile.
[Source manifest](source-manifest.json) · [Comment updates](comment-only-changes.json)

The preparation reuses the complete verified build for unchanged mathematical
sources. Fresh clean whole-project rebuild status is **not repeated during
repackaging**. The reproducible full build and optional complete sequential
source-check commands are supplied for independent reproduction. The pilot
showed roughly 18–20 seconds for each of its four smaller modules, so replaying all
250 identical mathematical sources was deferred under the bounded-compute policy.
[Preserved build record](prior-build.json) · [Build log](logs/prior-full-build.txt)

## Declaration and axiom checks

A freshly compiled audit checks and prints every selected declaration and its
transitive axioms. All 1,763 targets are present.
The target inventory contains 1,443 theorem declarations and 320 definitions.
The only observed axiom names are `Classical.choice`, `Quot.sound` and `propext`.
The source commit and tracked-file hashes agree before and after the audit.
[Audit source](AxiomAudit.lean) · [Target manifest](targets.json) ·
[Axiom results](axioms.json) · [Complete audit output](logs/axiom-audit.txt)

## Export and checker results

The freshly generated proof export has 121,521,760 bytes.
Its SHA-256 is `6c2f6186d682841bb5f6c89656dce9b67e72763cd9450ea1e42f05b1ac151d69`.
The structural audit found 20,351 declarations,
all 1,763 selected targets and zero unsafe
declarations. The standard axiom list exactly matches the permitted list.

The six completed checker results were reused after verifying byte identity
of the newly generated export, matching checker binaries, original log hashes
and successful exit statuses. The original runs are timestamped in the
individual records. This reuse follows the bounded-compute instruction.

| Checker mode | Exit code | Recorded seconds |
| --- | --- | --- |
| leanchecker-paranoid | 0 | 54.407 |
| lean4lean | 0 | 75.875 |
| nanoda_bin | 0 | 11.484 |
| con-leche | 0 | 38.703 |
| con-ron | 0 | 44.422 |
| leanchecker | 0 | 37.578 |

Nanoda reports zero typechecker errors and one pretty-printer diagnostic,
`Unable to print axioms`. The diagnostic and successful process status are
retained together. The checker binaries, exported artifact and standard axioms
form part of the trust record. This method uses a local Windows environment
with pinned trusted tools and reviewed caches. An isolated virtual-machine
execution of the optional JSP skill is outside the claimed checks.
[Results](results.json) · [Structural audit](structure_audit.json) ·
[Tool identities](tools.json) · [Compressed export](proof_terms.ndjson.gz)

The compressed export round trip was verified against the uncompressed hash.
Each packaged raw evidence record has a hash in the evidence index. Workspace path
prefixes in text records are normalized to `<repository>`, `<audit>`,
`<prior-workspace>`, `<prior-audit>` and `<toolchain>`. Original raw records remain
in the private preparation workspace. The export bytes retain their original
content. [Evidence index](evidence-index.json)

## Submission status

The current proposed mapping is JSP-000484 / Erdős 597, corroborated by the
historical catalog and supplied for exact-statement acceptance. The catalog
patch and individual claim drafts remain private. The user selected Ghuffy1 as
owner and lead submitter, with four equal contributors. The legacy original-
repository requirement needs clarification for the three additional formalization
claimants. Each person must make and confirm their own claim and identity.

The literature review credits the prior constructions and positive partition
theorem, records full-text access gaps, and leaves first priority unverified.
Public release, mathematical acceptance, candidate notice, the role-specific
14-day review and recipient confirmation remain external stages.
[Prior work](../RELATED_WORK.md) · [Authorship](../AUTHORS.md)
