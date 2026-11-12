import Erdos597
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The two-hub refinement of the unrestricted Erdős 597 counterexample. -/

namespace Erdos597Object.BipartiteTarget

open Cardinal Ordinal Erdos597 Set Function
open scoped Cardinal Ordinal

abbrev Vertex := TreeVertex ⊕ Fin 2

def color : Vertex → Fin 2
  | .inl t => treeColoring t
  | .inr c => c

def graph : SimpleGraph Vertex where
  Adj x y := match x, y with
    | .inl s, .inl t => branchingTree.Adj s t
    | _, _ => color x ≠ color y
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact h.symm
    · exact Ne.symm h
    · exact Ne.symm h
    · exact Ne.symm h⟩
  loopless := ⟨by
    intro x h
    cases x
    · exact branchingTree.loopless.irrefl _ h
    · exact h rfl⟩

theorem cardinality : #Vertex = ℵ₁ := by
  rw [Vertex, Cardinal.mk_sum, branchingTree_card, Cardinal.mk_fintype]
  simp only [Cardinal.lift_id, Fintype.card_fin]
  apply Cardinal.add_eq_left
  · exact Cardinal.aleph0_le_aleph 1
  · exact Cardinal.natCast_le_aleph0.trans (Cardinal.aleph0_le_aleph 1)

def coloring : graph.Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk color (by
    intro x y h
    cases x <;> cases y
    · exact treeColoring.valid h
    · exact h
    · exact h
    · exact h)

theorem cliqueFree : graph.CliqueFree 4 :=
  (show graph.Colorable 2 from ⟨coloring⟩).cliqueFree (by decide)

theorem old_preimage_infinite {A : Set Vertex} (hA : A.Infinite) :
    (Sum.inl ⁻¹' A : Set TreeVertex).Infinite := by
  intro hfinite
  apply hA
  apply ((hfinite.image Sum.inl).union (Set.finite_range (Sum.inr : Fin 2 → Vertex))).subset
  intro x hx
  cases x with
  | inl t => exact Or.inl ⟨t, hx, rfl⟩
  | inr c => exact Or.inr ⟨c, rfl⟩

theorem no_biclique : ¬ HasInfiniteBiclique graph := by
  rintro ⟨A, B, hdisjoint, hA, hB, hedge⟩
  apply branchingTree_no_biclique
  refine ⟨Sum.inl ⁻¹' A, Sum.inl ⁻¹' B, ?_,
    old_preimage_infinite hA, old_preimage_infinite hB, ?_⟩
  · exact hdisjoint.preimage Sum.inl
  · intro s hs t ht
    exact hedge (.inl s) hs (.inl t) ht

theorem no_weakCopy : ¬ HasWeakCopy graph nestedGraph := by
  rintro ⟨f, hf, hedge⟩
  apply branchingTree_no_weakCopy
  exact ⟨fun t => f (.inl t), hf.comp Sum.inl_injective,
    fun s t h => hedge (.inl s) (.inl t) h⟩

theorem adj_hub (x : Vertex) (c : Fin 2) :
    graph.Adj x (.inr c) ↔ color x ≠ c := by
  cases x <;> rfl

theorem short_walk (x y : Vertex) : ∃ p : graph.Walk x y, p.length ≤ 3 := by
  by_cases h : color x = color y
  · have hflip : color x ≠ (color x).rev := by
      generalize color x = c
      fin_cases c <;> decide
    have hx : graph.Adj x (.inr (color x).rev) := (adj_hub _ _).mpr hflip
    have hy : graph.Adj y (.inr (color x).rev) := by
      apply (adj_hub _ _).mpr
      simpa only [← h] using hflip
    exact ⟨.cons hx (.cons hy.symm .nil), by simp⟩
  · have hx : graph.Adj x (.inr (color y)) := (adj_hub _ _).mpr h
    have hh : graph.Adj (.inr (color y)) (.inr (color x)) := Ne.symm h
    have hy : graph.Adj y (.inr (color x)) := (adj_hub _ _).mpr (Ne.symm h)
    exact ⟨.cons hx (.cons hh (.cons hy.symm .nil)), by simp⟩

theorem connected : graph.Connected := by
  refine (SimpleGraph.connected_iff_exists_forall_reachable graph).mpr ⟨.inr 0, ?_⟩
  intro y
  obtain ⟨p, _⟩ := short_walk (.inr 0) y
  exact ⟨p⟩

theorem partition_failure :
    ¬ OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : Nat))
      ((ω₁ : Ordinal.{0}) * ω) graph := by
  intro h
  rcases h blueSquareᶜ blueSquare isCompl_compl.symm with hred | hblue
  · exact blueSquare_no_red_block hred
  · apply no_weakCopy
    rcases hblue with ⟨f, hf, hedge⟩
    exact ⟨fun x => squareIso (f x), squareIso.injective.comp hf, hedge⟩

theorem counterexample :
    ∃ (W : Type) (G : SimpleGraph W), #W = ℵ₁ ∧ G.Colorable 2 ∧ G.Connected ∧
      (∀ x y, ∃ p : G.Walk x y, p.length ≤ 3) ∧
      G.CliqueFree 4 ∧ ¬ HasInfiniteBiclique G ∧
      ¬ OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : Nat))
        ((ω₁ : Ordinal.{0}) * ω) G :=
  ⟨Vertex, graph, cardinality, ⟨coloring⟩, connected, short_walk,
    cliqueFree, no_biclique, partition_failure⟩

end Erdos597Object.BipartiteTarget
