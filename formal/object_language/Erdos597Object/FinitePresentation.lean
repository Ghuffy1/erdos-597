import Erdos597Object.SetInterpretation

set_option backward.isDefEq.respectTransparency false

/-! Exact correspondence between finite graphs and their set-coded presentations. -/

namespace Erdos597Object.FinitePresentation

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open Erdos597Object.SetCodes Erdos597Object.SetInterpretation

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

noncomputable section

def decode (n : ℕ) (edges : ZFSet.{0})
    (h : graphValue setStructure (naturalSet n) edges) : SimpleGraph (Fin n) where
  Adj i j := ZFSet.pair (naturalSet i.val) (naturalSet j.val) ∈ edges
  symm := ⟨by
    intro i j hij
    have hi := (mem_naturalSet _ _).mpr ⟨i.val, i.isLt, rfl⟩
    have hj := (mem_naturalSet _ _).mpr ⟨j.val, j.isLt, rfl⟩
    exact ((graphValue_set _ _).mp h).2.2 _ hi _ hj |>.mp hij⟩
  loopless := ⟨by
    intro i hii
    exact ((graphValue_set _ _).mp h).2.1 _
      ((mem_naturalSet _ _).mpr ⟨i.val, i.isLt, rfl⟩) hii⟩

theorem edgeSet_decode (n : ℕ) (edges : ZFSet.{0})
    (h : graphValue setStructure (naturalSet n) edges) :
    edgeSet (decode n edges h) = edges := by
  apply ZFSet.ext
  intro entry
  constructor
  · intro hentry
    obtain ⟨⟨⟨i, j⟩, hij⟩, rfl⟩ := ZFSet.mem_range.mp hentry
    exact hij
  · intro hentry
    obtain ⟨a, ha, b, hb, rfl⟩ := ((graphValue_set _ _).mp h).1 entry hentry
    obtain ⟨i, hi, rfl⟩ := (mem_naturalSet a n).mp ha
    obtain ⟨j, hj, rfl⟩ := (mem_naturalSet b n).mp hb
    exact ZFSet.mem_range.mpr ⟨⟨(⟨i, hi⟩, ⟨j, hj⟩), hentry⟩, rfl⟩

theorem decode_edgeSet {n : ℕ} (G : SimpleGraph (Fin n)) :
    decode n (edgeSet G) (edgeSet_graph G) = G := by
  ext i j
  exact pair_mem_edgeSet G i j

theorem decode_cliqueFree_iff (n : ℕ) (edges : ZFSet.{0})
    (h : graphValue setStructure (naturalSet n) edges) :
    (decode n edges h).CliqueFree 4 ↔
      cliqueFreeFourValue setStructure (naturalSet n) edges := by
  rw [← edgeSet_cliqueFree_iff, edgeSet_decode]

theorem finite_graph_quantifier_iff (P : ℕ → ZFSet.{0} → Prop) :
    (∀ n edges, graphValue setStructure (naturalSet n) edges →
      cliqueFreeFourValue setStructure (naturalSet n) edges → P n edges) ↔
    (∀ n (G : SimpleGraph (Fin n)), G.CliqueFree 4 → P n (edgeSet G)) := by
  constructor
  · intro h n G hG
    exact h n (edgeSet G) (edgeSet_graph G) ((edgeSet_cliqueFree_iff G).mpr hG)
  · intro h n edges hgraph hfree
    have hG := (decode_cliqueFree_iff n edges hgraph).mpr hfree
    simpa only [edgeSet_decode] using h n (decode n edges hgraph) hG

theorem encoded_graph_and_clique_free {n : ℕ} (G : SimpleGraph (Fin n)) :
    boolean_realize_bounded_formula (S := setStructure)
      (naturalSet n :: edgeSet G :: [])
      (bd_and (graph (var0 : Term 2) (var0 : Term 1).lift1)
        (cliqueFreeFour (var0 : Term 2) (var0 : Term 1).lift1)) [] ↔
      G.CliqueFree 4 := by
  simp only [Flypitch.fol.bfol.boolean_realize_bounded_formula_and,
    realize_graph, realize_cliqueFreeFour,
    Flypitch.fol.bfol.boolean_realize_bounded_term_lift1, realize_var0]
  exact and_iff_right (edgeSet_graph G) |>.trans (edgeSet_cliqueFree_iff G)

end

end Erdos597Object.FinitePresentation
