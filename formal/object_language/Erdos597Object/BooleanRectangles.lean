import Erdos597Object.BooleanUncountableRamsey

set_option backward.isDefEq.respectTransparency false

/-! Uncountable subset refinements and empty rectangles in Boolean-valued graphs. -/

namespace Erdos597Object.BooleanRectangles

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanUncountableRamsey

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def largeSubset (domain subset : bSet B) : B :=
  (subset ⊆ᴮ domain) ⊓ (injectsIntoValue (V B) subset bSet.omega)ᶜ

noncomputable def rectangleEdge (relation left right : bSet B) : B :=
  ⨆ x : bSet B, (x ∈ᴮ left) ⊓ ⨆ y : bSet B, (y ∈ᴮ right) ⊓ edgeValue (V B) relation x y

noncomputable def emptyRectangle (relation left right : bSet B) : B :=
  (rectangleEdge relation left right)ᶜ

theorem largeSubset_domain_ext (subset : bSet B) :
    bSet.B_ext (fun domain => largeSubset domain subset) :=
  bSet.B_ext_inf (bSet.B_ext_subset_right subset) (bSet.B_ext_const _)

theorem largeSubset_ext (domain : bSet B) :
    bSet.B_ext (fun subset => largeSubset domain subset) := by
  have hcountable : bSet.B_ext (fun subset : bSet B => injectsIntoValue (V B) subset bSet.omega) := by
    simp_rw [BooleanFunctionBridge.injectsInto_eq_injects_into]
    exact bSet.B_ext_injects_into_left
  exact bSet.B_ext_inf (bSet.B_ext_subset_left domain) (bSet.B_ext_compl hcountable)

theorem largeSubset_refl (context : B) (domain : bSet B)
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ) :
    context ≤ largeSubset domain domain := le_inf bSet.subset_self hlarge

theorem largeSubset_mono (context : B) (small large subset : bSet B)
    (hsubset : context ≤ small ⊆ᴮ large) :
    context ⊓ largeSubset small subset ≤ largeSubset large subset := by
  exact le_inf (subset_trans (inf_le_right.trans inf_le_left) (inf_le_left.trans hsubset))
    (inf_le_right.trans inf_le_right)

theorem largeSubset_trans (context : B) (large middle small : bSet B)
    (hmiddle : context ≤ largeSubset large middle) (hsmall : context ≤ largeSubset middle small) :
    context ≤ largeSubset large small :=
  le_inf (subset_trans (hsmall.trans inf_le_left) (hmiddle.trans inf_le_left))
    (hsmall.trans inf_le_right)

theorem rectangleEdge_left_ext (relation right : bSet B) :
    bSet.B_ext (fun left => rectangleEdge relation left right) :=
  bSet.B_ext_iSup fun x => bSet.B_ext_inf (bSet.B_ext_mem_right x) (bSet.B_ext_const _)

theorem rectangleEdge_right_ext (relation left : bSet B) :
    bSet.B_ext (fun right => rectangleEdge relation left right) :=
  bSet.B_ext_iSup fun _ => bSet.B_ext_inf (bSet.B_ext_const _)
    (bSet.B_ext_iSup fun y => bSet.B_ext_inf (bSet.B_ext_mem_right y) (bSet.B_ext_const _))

theorem emptyRectangle_left_ext (relation right : bSet B) :
    bSet.B_ext (fun left => emptyRectangle relation left right) :=
  bSet.B_ext_compl (rectangleEdge_left_ext relation right)

theorem emptyRectangle_right_ext (relation left : bSet B) :
    bSet.B_ext (fun right => emptyRectangle relation left right) :=
  bSet.B_ext_compl (rectangleEdge_right_ext relation left)

theorem rectangleEdge_mono (context : B) (relation left right largeLeft largeRight : bSet B)
    (hleft : context ≤ left ⊆ᴮ largeLeft) (hright : context ≤ right ⊆ᴮ largeRight) :
    context ⊓ rectangleEdge relation left right ≤ rectangleEdge relation largeLeft largeRight := by
  unfold rectangleEdge
  simp only [inf_iSup_eq]
  apply iSup_le
  intro x
  apply iSup_le
  intro y
  apply le_iSup_of_le x
  apply le_iSup_of_le y
  apply le_inf
  · exact bSet.mem_of_mem_subset' (inf_le_left.trans hleft) (inf_le_right.trans inf_le_left)
  · exact le_inf
      (bSet.mem_of_mem_subset' (inf_le_left.trans hright)
        (inf_le_right.trans (inf_le_right.trans inf_le_left)))
      (inf_le_right.trans (inf_le_right.trans inf_le_right))

theorem emptyRectangle_mono (context : B) (relation left right largeLeft largeRight : bSet B)
    (hleft : context ≤ left ⊆ᴮ largeLeft) (hright : context ≤ right ⊆ᴮ largeRight) :
    context ⊓ emptyRectangle relation largeLeft largeRight ≤ emptyRectangle relation left right := by
  apply le_compl_iff_disjoint_right.mpr
  rw [disjoint_iff]
  apply bot_unique
  have hedge : context ⊓ emptyRectangle relation largeLeft largeRight ⊓
      rectangleEdge relation left right ≤ rectangleEdge relation largeLeft largeRight :=
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans
      (rectangleEdge_mono context relation left right largeLeft largeRight hleft hright)
  exact (le_inf hedge (inf_le_left.trans inf_le_right)).trans_eq inf_compl_eq_bot

theorem emptyRectangle_spec (relation left right : bSet B) :
    emptyRectangle relation left right =
      ⨅ x : bSet B, lattice.imp (x ∈ᴮ left)
        (⨅ y : bSet B, lattice.imp (y ∈ᴮ right) (edgeValue (V B) relation x y)ᶜ) := by
  simp only [emptyRectangle, rectangleEdge, compl_iSup, compl_inf, lattice.imp]

theorem emptyRectangle_no_edge (context : B) (relation left right x y : bSet B)
    (hrectangle : context ≤ emptyRectangle relation left right)
    (hx : context ≤ x ∈ᴮ left) (hy : context ≤ y ∈ᴮ right) :
    context ≤ (edgeValue (V B) relation x y)ᶜ := by
  rw [emptyRectangle_spec] at hrectangle
  have hleft := lattice.bv_context_apply (hrectangle.trans (iInf_le _ x)) hx
  exact lattice.bv_context_apply (hleft.trans (iInf_le _ y)) hy

theorem rectangleEdge_witness (context : B) (relation left right : bSet B)
    (hedge : context ≤ rectangleEdge relation left right) :
    ∃ x y : bSet B, context ≤ x ∈ᴮ left ∧ context ≤ y ∈ᴮ right ∧
      context ≤ edgeValue (V B) relation x y := by
  obtain ⟨x, hx⟩ := bSet.exists_convert hedge
    (bSet.B_ext_inf (bSet.B_ext_mem_left left)
      (bSet.B_ext_iSup fun y => bSet.B_ext_inf (bSet.B_ext_const _) (edge_left_ext relation y)))
  obtain ⟨y, hy⟩ := bSet.exists_convert (hx.trans inf_le_right)
    (bSet.B_ext_inf (bSet.B_ext_mem_left right) (edge_right_ext relation x))
  exact ⟨x, y, hx.trans inf_le_left, hy.trans inf_le_left, hy.trans inf_le_right⟩

end Erdos597Object.BooleanRectangles
