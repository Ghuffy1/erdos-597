import Erdos597Object.BooleanRedRows

set_option backward.isDefEq.respectTransparency false

/-! Restrict a graph name to an induced subgraph on a smaller domain. -/

namespace Erdos597Object.BooleanInducedGraphs

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanFunctionBridge BooleanGraphNeighborhoods

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def restrictGraph (domain relation : bSet B) : bSet B :=
  bSet.binary_inter relation (bSet.prod domain domain)

theorem restricted_edge (domain relation x y : bSet B) :
    edgeValue (V B) (restrictGraph domain relation) x y =
      edgeValue (V B) relation x y ⊓ ((x ∈ᴮ domain) ⊓ (y ∈ᴮ domain)) := by
  apply le_antisymm
  · obtain ⟨hrelation, hproduct⟩ := (bSet.mem_binary_inter_iff).mp
      (show edgeValue (V B) (restrictGraph domain relation) x y ≤
        bSet.pair x y ∈ᴮ bSet.binary_inter relation (bSet.prod domain domain) from le_rfl)
    obtain ⟨hx, hy⟩ := bSet.mem_prod_iff.mp hproduct
    exact le_inf hrelation (le_inf hx hy)
  · apply bSet.mem_binary_inter_iff.mpr
    exact ⟨inf_le_left, bSet.mem_prod_iff.mpr
      ⟨inf_le_right.trans inf_le_left, inf_le_right.trans inf_le_right⟩⟩

theorem restricted_subset (domain relation : bSet B) :
    (⊤ : B) ≤ restrictGraph domain relation ⊆ᴮ relation := bSet.binary_inter_subset_left

theorem restricted_symmetry (context : B) (small large relation x y : bSet B)
    (hsub : context ≤ small ⊆ᴮ large)
    (hgraph : context ≤ graphValue (V B) large relation)
    (hx : context ≤ x ∈ᴮ small) (hy : context ≤ y ∈ᴮ small) :
    context ⊓ edgeValue (V B) (restrictGraph small relation) x y ≤
      edgeValue (V B) (restrictGraph small relation) y x := by
  rw [restricted_edge small relation y x]
  have hsym := graph_symmetry context large relation x y hgraph
    (bSet.mem_of_mem_subset' hsub hx) (bSet.mem_of_mem_subset' hsub hy)
  refine le_inf ?_ (le_inf (inf_le_left.trans hy) (inf_le_left.trans hx))
  exact (le_inf inf_le_left
    (inf_le_right.trans ((restricted_edge small relation x y).le.trans inf_le_left))).trans hsym

theorem restricted_graph (context : B) (small large relation : bSet B)
    (hsub : context ≤ small ⊆ᴮ large)
    (hgraph : context ≤ graphValue (V B) large relation) :
    context ≤ graphValue (V B) small (restrictGraph small relation) := by
  apply le_inf
  · rw [relationBetween_eq_subset_prod]
    exact le_top.trans bSet.binary_inter_subset_right
  · apply le_inf
    · apply le_iInf
      intro x
      apply lattice.bv_imp_intro
      let part := context ⊓ (x ∈ᴮ small)
      have hx : part ≤ x ∈ᴮ large := bSet.mem_of_mem_subset' (inf_le_left.trans hsub) inf_le_right
      have hloop := lattice.bv_context_apply
        ((inf_le_left.trans (hgraph.trans (inf_le_right.trans inf_le_left))).trans (iInf_le _ x)) hx
      exact hloop.trans (compl_le_compl ((restricted_edge small relation x x).le.trans inf_le_left))
    · apply le_iInf
      intro x
      apply lattice.bv_imp_intro
      apply le_iInf
      intro y
      apply lattice.bv_imp_intro
      let part := (context ⊓ (x ∈ᴮ small)) ⊓ (y ∈ᴮ small)
      have hsubPart : part ≤ small ⊆ᴮ large := (inf_le_left.trans inf_le_left).trans hsub
      have hgraphPart : part ≤ graphValue (V B) large relation :=
        (inf_le_left.trans inf_le_left).trans hgraph
      have hx : part ≤ x ∈ᴮ small := inf_le_left.trans inf_le_right
      have hy : part ≤ y ∈ᴮ small := inf_le_right
      exact le_inf
        (lattice.le_imp_iff.mpr (restricted_symmetry part small large relation x y hsubPart hgraphPart hx hy))
        (lattice.le_imp_iff.mpr (restricted_symmetry part small large relation y x hsubPart hgraphPart hy hx))

end Erdos597Object.BooleanInducedGraphs
