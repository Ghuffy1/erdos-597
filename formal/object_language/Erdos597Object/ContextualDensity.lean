import Erdos597Object.PresentedSubsets

set_option backward.isDefEq.respectTransparency false

/-! Density coefficients below a context, without imposing that context on every member weight. -/

namespace Erdos597Object.ContextualDensity

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections PresentedSubsets

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem dense_coefficients (context : B) (domain relation subset : bSet B)
    (element : I → bSet B) (weight : I → B)
    (hmembers : ∀ i, weight i ≤ element i ∈ᴮ domain)
    (heq : context ≤ domain =ᴮ weightedSet element weight)
    (hdense : context ≤ denseValue (V B) domain relation subset) (j : I) :
    context ⊓ weight j ≤ ⨆ i, (weight i ⊓ (element i ∈ᴮ subset)) ⊓
      (weight i ⊓ weight j ⊓ edgeValue (V B) relation (element i) (element j)) := by
  have hpresent := dense_presentation context domain relation subset element weight heq hdense
  have himp := ((inf_le_left : context ⊓ weight j ≤ context).trans
    (hpresent.trans inf_le_right)).trans (iInf_le _ (element j))
  have hex := lattice.bv_context_apply himp (inf_le_right.trans (hmembers j))
  change context ⊓ weight j ≤ ⨆ x : bSet B,
    (x ∈ᴮ weightedSet element (fun i => weight i ⊓ (element i ∈ᴮ subset))) ⊓
      edgeValue (V B) relation x (element j) at hex
  rw [weighted_bounded_exists element (fun i => weight i ⊓ (element i ∈ᴮ subset)) _
    (edge_left_ext relation (element j))] at hex
  calc
    context ⊓ weight j ≤ weight j ⊓ (⨆ i, (weight i ⊓ (element i ∈ᴮ subset)) ⊓
        edgeValue (V B) relation (element i) (element j)) := le_inf inf_le_right hex
    _ = ⨆ i, weight j ⊓ ((weight i ⊓ (element i ∈ᴮ subset)) ⊓
        edgeValue (V B) relation (element i) (element j)) := inf_iSup_eq _ _
    _ = _ := by
      apply iSup_congr
      intro i
      simp only [inf_assoc, inf_left_comm, inf_comm, inf_left_idem]

end Erdos597Object.ContextualDensity
