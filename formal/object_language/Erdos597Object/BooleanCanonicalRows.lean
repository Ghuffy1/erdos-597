import Erdos597Object.BooleanOrderedMixedRows
import Erdos597Object.BooleanIndependentRows

set_option backward.isDefEq.respectTransparency false

/-! Ordered separation for the actual canonical ordinal rows. -/

namespace Erdos597Object.BooleanCanonicalRows

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanFiniteGraphs BooleanInjections CanonicalDomains CanonicalRelations
open BooleanIndependentRows BooleanRowOrder

variable {B I J : Type} [CompleteBooleanAlgebra B]

theorem allBefore_of_labels (context : B) (order : bSet B)
    (left : I → bSet B) (right : J → bSet B)
    (hlabels : ∀ i j, context ≤ edgeValue (V B) order (left i) (right j)) :
    context ≤ allBefore order (labelDomain left) (labelDomain right) := by
  apply allBefore_intro
  intro x y
  change context ⊓ ((x ∈ᴮ weightedSet left (fun _ => ⊤)) ⊓
    (y ∈ᴮ weightedSet right (fun _ => ⊤))) ≤ _
  rw [member_weightedSet, member_weightedSet]
  simp only [top_inf_eq, iSup_inf_eq, inf_iSup_eq]
  apply iSup_le
  intro j
  apply iSup_le
  intro i
  have hleft : context ⊓ ((x =ᴮ left i) ⊓ (y =ᴮ right j)) ≤
      edgeValue (V B) order x (right j) :=
    (le_inf (bSet.bv_symm (inf_le_right.trans inf_le_left))
      (inf_le_left.trans (hlabels i j))).trans (edge_left_ext order (right j) (left i) x)
  exact (le_inf (bSet.bv_symm (inf_le_right.trans inf_le_right)) hleft).trans
    (edge_right_ext order x (right j) y)

theorem rowLabel_before {r s : ℕ} (hrs : r < s) (a b : Erdos597.One) :
    (⊤ : B) ≤ edgeValue (V B) blockOrder (rowLabel r a) (rowLabel s b) := by
  change (⊤ : B) ≤ edgeValue (V B) (lexOrderName blockLabel)
    (blockLabel (r, oneLabelsEquiv a)) (blockLabel (s, oneLabelsEquiv b))
  rw [lexOrderName_edge blockLabel blockLabel_discrete]
  apply le_iSup_of_le (bSet.ofNat r)
  apply le_iSup_of_le (OmegaOneLabels.element (oneLabelsEquiv a))
  apply le_iSup_of_le (bSet.ofNat s)
  apply le_iSup_of_le (OmegaOneLabels.element (oneLabelsEquiv b))
  exact le_inf bSet.bv_refl (le_inf bSet.bv_refl (le_sup_of_le_left (bSet.ofNat_mem_of_lt hrs)))

theorem rowDomain_before {r s : ℕ} (hrs : r < s) :
    (⊤ : B) ≤ allBefore blockOrder (rowDomain r) (rowDomain s) :=
  allBefore_of_labels ⊤ blockOrder (rowLabel r) (rowLabel s) (rowLabel_before hrs)

theorem subrows_before (context : B) (domain : ℕ → bSet B)
    (hsubset : ∀ r, context ≤ domain r ⊆ᴮ rowDomain r) (r s : ℕ) (hrs : r < s) :
    context ≤ allBefore blockOrder (domain r) (domain s) :=
  allBefore_restrict context blockOrder (rowDomain r) (rowDomain s) (domain r) (domain s)
    (hsubset r) (hsubset s) (le_top.trans (rowDomain_before hrs))

end Erdos597Object.BooleanCanonicalRows
