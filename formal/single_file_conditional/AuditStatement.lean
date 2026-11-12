import Erdos597

/-!
# Independent pair-coloring formulation

This challenge expresses the original relation using symmetric Boolean colors,
red homogeneous sets, and injective blue edge maps. It does not use the
submitted definition of `OrdinalGraphRamsey` in its statement.
-/

open Cardinal Ordinal Set Function
open scoped Cardinal Ordinal

namespace Erdos597Audit

abbrev Omega := ((ω₁ : Ordinal.{0}) ^ (2 : ℕ)).ToType

def PairPartition {W : Type} (G : SimpleGraph W) : Prop :=
  ∀ color : Omega → Omega → Bool,
    (∀ x y, color x y = color y x) →
    (∃ S : Set Omega, typeLT S = (ω₁ : Ordinal.{0}) * ω ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → color x y = false) ∨
    (∃ f : W ↪ Omega, ∀ x y, G.Adj x y → color (f x) (f y) = true)

theorem tree_pair_partition_failure : ¬ PairPartition Erdos597.branchingTree := by
  classical
  intro h
  let color : Omega → Omega → Bool := fun x y => decide (Erdos597.blueSquare.Adj x y)
  have hsym : ∀ x y, color x y = color y x := by
    intro x y
    simp only [color, decide_eq_decide]
    exact Erdos597.blueSquare.adj_comm x y
  rcases h color hsym with ⟨S, htype, hred⟩ | ⟨f, hblue⟩
  · apply Erdos597.blueSquare_no_red_block
    refine ⟨S, ?_, htype⟩
    intro x hx y hy hne
    apply (SimpleGraph.compl_adj _ _ _).mpr
    refine ⟨hne, ?_⟩
    have hc := hred x hx y hy hne
    exact of_decide_eq_false hc
  · apply Erdos597.blueSquare_no_tree
    refine ⟨f, f.injective, ?_⟩
    intro x y hxy
    exact of_decide_eq_true (hblue x y hxy)

theorem original_pair_assertion_disproved :
    ¬ ∀ (W : Type) (G : SimpleGraph W), #W ≤ ℵ₁ →
      (∀ A : Finset W, A.card = 4 → ¬ G.IsClique (A : Set W)) →
      (¬ ∃ A B : Set W, Disjoint A B ∧ A.Infinite ∧ B.Infinite ∧
        ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) → PairPartition G := by
  intro h
  apply tree_pair_partition_failure
  apply h Erdos597.TreeVertex Erdos597.branchingTree Erdos597.branchingTree_card.le
  · intro A hA hclique
    exact Erdos597.branchingTree_cliqueFree A ⟨hclique, hA⟩
  · exact Erdos597.branchingTree_no_biclique

end Erdos597Audit


/-! # Equivalence with the independently stated Boolean pair-coloring problem -/

open Cardinal Ordinal Set Function
open scoped Cardinal Ordinal

namespace Erdos597Audit

theorem pair_partition_to_graph {W : Type} {G : SimpleGraph W}
    (h : PairPartition G) :
    Erdos597.OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ))
      ((ω₁ : Ordinal.{0}) * ω) G := by
  classical
  intro red blue hcomp
  let color : Omega → Omega → Bool := fun x y => decide (blue.Adj x y)
  have hsym : ∀ x y, color x y = color y x := by
    intro x y
    simp only [color, decide_eq_decide]
    exact blue.adj_comm x y
  rcases h color hsym with ⟨S, htype, hred⟩ | ⟨f, hblue⟩
  · left
    refine ⟨S, ?_, htype⟩
    intro x hx y hy hne
    rw [← hcomp.symm.compl_eq]
    apply (SimpleGraph.compl_adj _ _ _).mpr
    exact ⟨hne, of_decide_eq_false (hred x hx y hy hne)⟩
  · right
    refine ⟨f, f.injective, ?_⟩
    intro x y hxy
    exact of_decide_eq_true (hblue x y hxy)

theorem graph_partition_to_pair {W : Type} {G : SimpleGraph W}
    (h : Erdos597.OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ))
      ((ω₁ : Ordinal.{0}) * ω) G) : PairPartition G := by
  intro color hsym
  let blue : SimpleGraph Omega := {
    Adj := fun x y => x ≠ y ∧ color x y = true
    symm := ⟨fun x y h => ⟨h.1.symm, (hsym y x).trans h.2⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩
  }
  rcases h blueᶜ blue isCompl_compl.symm with ⟨S, hred, htype⟩ | ⟨f, hf, hblue⟩
  · left
    refine ⟨S, htype, ?_⟩
    intro x hx y hy hne
    have hnot := ((SimpleGraph.compl_adj _ _ _).mp (hred hx hy hne)).2
    cases hc : color x y with
    | false => rfl
    | true => exact False.elim (hnot ⟨hne, hc⟩)
  · right
    exact ⟨⟨f, hf⟩, fun x y hxy => (hblue x y hxy).2⟩

theorem pair_partition_iff_graph {W : Type} (G : SimpleGraph W) :
    PairPartition G ↔ Erdos597.OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ))
      ((ω₁ : Ordinal.{0}) * ω) G :=
  ⟨pair_partition_to_graph, graph_partition_to_pair⟩

end Erdos597Audit


/-! # Independent Boolean-coloring check of the finite negative assertion -/

open Set Function Cardinal Ordinal
open scoped Cardinal Ordinal

namespace Erdos597FiniteAudit

theorem finite_pair_assertion_fails_under_CH
    (hCH : (2 : Cardinal.{0}) ^ ℵ₀ = ℵ₁) :
    ¬ ∀ (W : Type) [Fintype W] (G : SimpleGraph W),
      (∀ A : Finset W, A.card = 4 → ¬ G.IsClique (A : Set W)) →
      Erdos597Audit.PairPartition G := by
  intro h
  apply Erdos597.finite_universal_fails_under_CH hCH
  intro W inst G hG
  apply Erdos597Audit.pair_partition_to_graph
  apply h W G
  intro A hcard hclique
  exact hG A ⟨hclique, hcard⟩

end Erdos597FiniteAudit


/-! # The positive theorem for the independent pair-coloring statement -/

namespace Erdos597Audit

theorem finite_pair_partition_under_MA (hMA : Erdos597.MartinAxiomAlephOne)
    (W : Type) [Fintype W] (G : SimpleGraph W) : PairPartition G :=
  graph_partition_to_pair (Erdos597.finite_partition_under_MA hMA W G)

end Erdos597Audit
