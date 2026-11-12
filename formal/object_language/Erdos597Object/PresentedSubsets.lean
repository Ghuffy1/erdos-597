import Erdos597Object.PresentedFilters

set_option backward.isDefEq.respectTransparency false

/-! Subsets of a presented set use the same labels, with membership weights. -/

namespace Erdos597Object.PresentedSubsets

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections PresentedPosets PresentedFilters

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem member_restricted_weights (element : I → bSet B) (weight : I → B)
    (subset x : bSet B) :
    (x ∈ᴮ weightedSet element (fun i => weight i ⊓ (element i ∈ᴮ subset))) =
      (x ∈ᴮ weightedSet element weight) ⊓ (x ∈ᴮ subset) := by
  rw [member_weightedSet, member_weightedSet, iSup_inf_eq]
  apply iSup_congr
  intro i
  apply le_antisymm
  · have hx : weight i ⊓ (element i ∈ᴮ subset) ⊓ (x =ᴮ element i) ≤ x ∈ᴮ subset :=
      (le_inf (bSet.bv_symm inf_le_right) (inf_le_left.trans inf_le_right)).trans
        (bSet.B_ext_mem_left subset (element i) x)
    exact le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right) hx
  · have hi : weight i ⊓ (x =ᴮ element i) ⊓ (x ∈ᴮ subset) ≤ element i ∈ᴮ subset :=
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
        (bSet.B_ext_mem_left subset x (element i))
    exact le_inf (le_inf (inf_le_left.trans inf_le_left) hi) (inf_le_left.trans inf_le_right)

theorem subset_presentation (context : B) (domain subset : bSet B)
    (element : I → bSet B) (weight : I → B)
    (heq : context ≤ domain =ᴮ weightedSet element weight)
    (hsubset : context ≤ subsetValue (V B) subset domain) :
    context ≤ subset =ᴮ weightedSet element (fun i => weight i ⊓ (element i ∈ᴮ subset)) := by
  rw [subsetValue_bSet] at hsubset
  apply bSet.subset_ext
  · apply bSet.subset_unfold'.mpr
    apply le_iInf
    intro x
    apply lattice.bv_imp_intro
    rw [member_restricted_weights]
    have hmember : context ⊓ (x ∈ᴮ subset) ≤ x ∈ᴮ domain :=
      bSet.mem_of_mem_subset' (inf_le_left.trans hsubset) inf_le_right
    have hweight : context ⊓ (x ∈ᴮ subset) ≤ x ∈ᴮ weightedSet element weight :=
      (le_inf (inf_le_left.trans heq) hmember).trans
        (bSet.B_ext_mem_right x domain (weightedSet element weight))
    exact le_inf hweight inf_le_right
  · apply bSet.subset_intro
    intro i
    exact inf_le_right.trans inf_le_right

theorem denseSet_ext (domain relation : bSet B) :
    bSet.B_ext (fun subset => denseValue (V B) domain relation subset) := by
  unfold denseValue subsetValue
  apply bSet.B_ext_inf
  · exact bSet.B_ext_iInf fun x =>
      bSet.B_ext_sup (bSet.B_ext_compl (bSet.B_ext_mem_right x)) (bSet.B_ext_const _)
  · exact bSet.B_ext_iInf fun x => bSet.B_ext_sup (bSet.B_ext_const _)
      (bSet.B_ext_iSup fun y => bSet.B_ext_inf (bSet.B_ext_mem_right y) (bSet.B_ext_const _))

theorem dense_presentation (context : B) (domain relation subset : bSet B)
    (element : I → bSet B) (weight : I → B)
    (heq : context ≤ domain =ᴮ weightedSet element weight)
    (hdense : context ≤ denseValue (V B) domain relation subset) :
    context ≤ denseValue (V B) domain relation
      (weightedSet element (fun i => weight i ⊓ (element i ∈ᴮ subset))) := by
  have hsubset := hdense.trans inf_le_left
  have hpresent := subset_presentation context domain subset element weight heq hsubset
  exact context_le_congr (bSet.bv_symm hpresent) _ (denseSet_ext domain relation) hdense

theorem dense_coefficients (context : B) (domain relation subset : bSet B)
    (element : I → bSet B) (weight : I → B)
    (hvalid : ∀ i, weight i ≤ context ∧ weight i ≤ element i ∈ᴮ domain)
    (heq : context ≤ domain =ᴮ weightedSet element weight)
    (hdense : context ≤ denseValue (V B) domain relation subset) (j : I) :
    weight j ≤ ⨆ i, (weight i ⊓ (element i ∈ᴮ subset)) ⊓
      (weight i ⊓ weight j ⊓ edgeValue (V B) relation (element i) (element j)) := by
  have hpresent := dense_presentation context domain relation subset element weight heq hdense
  have himp := ((hvalid j).1.trans (hpresent.trans inf_le_right)).trans (iInf_le _ (element j))
  have hex := lattice.bv_context_apply himp (hvalid j).2
  change weight j ≤ ⨆ x : bSet B,
    (x ∈ᴮ weightedSet element (fun i => weight i ⊓ (element i ∈ᴮ subset))) ⊓
      edgeValue (V B) relation x (element j) at hex
  rw [weighted_bounded_exists element (fun i => weight i ⊓ (element i ∈ᴮ subset)) _
    (edge_left_ext relation (element j))] at hex
  calc
    weight j ≤ weight j ⊓ (⨆ i, (weight i ⊓ (element i ∈ᴮ subset)) ⊓
        edgeValue (V B) relation (element i) (element j)) := le_inf le_rfl hex
    _ = ⨆ i, weight j ⊓ ((weight i ⊓ (element i ∈ᴮ subset)) ⊓
        edgeValue (V B) relation (element i) (element j)) := inf_iSup_eq _ _
    _ = _ := by
      apply iSup_congr
      intro i
      simp only [inf_assoc, inf_left_comm, inf_comm, inf_left_idem]

end Erdos597Object.PresentedSubsets
