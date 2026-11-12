import Erdos597Object.NegativePartitionModel
import Erdos597Object.BipartiteTarget

/-! Verified entry point for the two original clauses of Erdos problem 597.

The unrestricted counterexample and finite-target independence are stated below.
The source bundle contains their complete dependencies and original-work credits.
The accompanying manuscript presents the two original clauses and this refinement.
-/

namespace Erdos597Object.Solution

open Cardinal Ordinal Erdos597
open Flypitch Flypitch.fol
open scoped Cardinal Ordinal

theorem unrestricted_clause_false :
    ¬ ∀ (W : Type) (G : SimpleGraph W), #W ≤ ℵ₁ → G.CliqueFree 4 →
      (¬ ∃ A B : Set W, Disjoint A B ∧ A.Infinite ∧ B.Infinite ∧
        ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) →
      OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : Nat)) ((ω₁ : Ordinal.{0}) * ω) G :=
  Erdos597.erdos_597_disproved

theorem finite_clause_independent :
    (¬ (Flypitch.ZFC.ZFC ⊢' finiteAssertion)) ∧
      (¬ (Flypitch.ZFC.ZFC ⊢' (∼finiteAssertion))) :=
  NegativePartitionModel.full_finite_independence

theorem finite_clause_relatively_independent : relativeFiniteIndependence :=
  NegativePartitionModel.relative_finite_independence

theorem bipartite_diameter_three_counterexample :
    ∃ (W : Type) (G : SimpleGraph W), #W = ℵ₁ ∧ G.Colorable 2 ∧ G.Connected ∧
      (∀ x y, ∃ p : G.Walk x y, p.length ≤ 3) ∧
      G.CliqueFree 4 ∧ ¬ HasInfiniteBiclique G ∧
      ¬ OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : Nat))
        ((ω₁ : Ordinal.{0}) * ω) G :=
  BipartiteTarget.counterexample

end Erdos597Object.Solution
