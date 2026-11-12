# Original statement and coverage

The original source is [Erdős 597](https://www.erdosproblems.com/597) and
P. Erdős, *Some problems on finite and infinite graphs*, Contemporary Mathematics
65 (1987), printed page 224. The paper is available from the
[Erdős archive](https://users.renyi.hu/~p_erdos/1987-28.pdf).

Write Ω = ω₁² and B = ω₁·ω. The relation Ω → (B,H)² says that every red-blue
coloring of pairs of Ω has a red set of inherited order type B or an injective,
edge-preserving blue copy of H. Additional blue edges are permitted, and the
blue copy has no order-preservation requirement.

The unrestricted question quantifies over graphs on at most aleph-one vertices
that contain neither K4 nor a complete bipartite graph with both sides
countably infinite. The second question restricts the target to finite graphs.

| Original requirement | Formal endpoint or bridge | Result |
| --- | --- | --- |
| Unrestricted target class, cardinality bound, both forbidden subgraphs and exact ordinal relation | `Erdos597Object.Solution.unrestricted_clause_false` | The universal assertion is false |
| Finite K4-free targets with the original weak-copy convention | `Erdos597Object.AssertionInterpretation.finiteAssertion_set_iff_original` | Exact correspondence of the first-order sentence with the original finite assertion |
| Failure of the finite assertion in a model of ZFC | `Erdos597Object.NegativePartitionModel.models_negative` | Constructed negative Boolean-valued model |
| Truth of the finite assertion in a model of ZFC | `Erdos597Object.PositivePartitionModel.final_models_finite_assertion` | Constructed positive Boolean-valued model |
| Both first-order nonprovability directions | `Erdos597Object.Solution.finite_clause_independent` | Full finite-target independence |
| Consistency-qualified formulation | `Erdos597Object.Solution.finite_clause_relatively_independent` | Relative independence |
| Additional bipartite, connected, diameter-at-most-three target | `Erdos597Object.Solution.bipartite_diameter_three_counterexample` | Stronger unrestricted counterexample |

The finite assertion is formalized in the first-order language of set theory.
The final model-theoretic endpoints require no external CH, Martin-axiom,
chain-condition, density, or assumed conditional-derivation premise.
The ambient metatheory uses Lean's ordinary classical foundations. The exact
transitive axiom audit is supplied with the verification evidence.

The paper's Theorem 1.1 covers the unrestricted question. Theorem 1.2 and
Corollary 1.3 cover the finite question, including the fixed finite target.
The supplementary historical biclique discussion from working notes is outside
the submitted theorem scope and supplies no premise of these proofs.

JSP-000484 is the catalog correspondence documented in [SUBMISSION.md](SUBMISSION.md).
The historical entry at
[7be685ccb752500ddb47b714db8948e5666a4ce1](https://github.com/TheJustinSunPrize/awards/blob/7be685ccb752500ddb47b714db8948e5666a4ce1/problems/catalog-0401-0500.md#JSP-000484)
corroborates the ordinal-partition mapping. The renumbering history and adjacent
numbered problems provide further support. The original source above and the
formal correspondence remain part of JSP's mathematical review.
