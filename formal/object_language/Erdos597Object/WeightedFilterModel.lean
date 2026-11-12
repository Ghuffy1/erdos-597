import Erdos597Object.BooleanPosetModel

set_option backward.isDefEq.respectTransparency false

/-! The first-order filter and dense-family formulas for labelled Boolean coefficients. -/

namespace Erdos597Object.WeightedFilterModel

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanIteration BooleanSets BooleanAntichains BooleanPosetCoding BooleanPosetModel

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem orderFilterValue_of_weights (P : BooleanPoset B I) (weight : I → B)
    (hsubset : ∀ i, weight i ≤ P.member i) (hcover : (⨆ i, weight i) = ⊤)
    (hup : ∀ i j, weight i ⊓ P.leValue i j ≤ weight j)
    (hdir : ∀ i j, weight i ⊓ weight j ≤
      ⨆ k, weight k ⊓ (P.leValue k i ⊓ P.leValue k j)) :
    ⊤ ≤ orderFilterValue (V B) (domainName P checkLabel) (orderName P checkLabel)
      (weightedSet checkLabel weight) := by
  let filter : bSet B := weightedSet checkLabel weight
  have hdiscrete : ∀ i j : I, i ≠ j →
      (checkLabel (B := B) i =ᴮ checkLabel j) = ⊥ :=
    fun _ _ h => checkLabel_discrete h
  have hedgeLeft (y : bSet B) : bSet.B_ext
      (fun x => edgeValue (V B) (orderName P checkLabel) x y) := by
    change bSet.B_ext (fun x => bSet.pair x y ∈ᴮ orderName P checkLabel)
    exact bSet.B_ext_pair_mem_left
  have hedgeRight (x : bSet B) : bSet.B_ext
      (fun y => edgeValue (V B) (orderName P checkLabel) x y) := by
    change bSet.B_ext (fun y => bSet.pair x y ∈ᴮ orderName P checkLabel)
    exact bSet.B_ext_pair_mem_right
  have hsub : ⊤ ≤ subsetValue (V B) filter (domainName P checkLabel) := by
    rw [weighted_subset_value]
    apply le_iInf
    intro i
    rw [domainName_member P checkLabel hdiscrete]
    exact (lattice.imp_eq_top_iff.mpr (hsubset i)).ge
  have hnonempty : ⊤ ≤ nonemptyValue (V B) filter := by
    rw [← hcover]
    apply iSup_le
    intro i
    exact (weight_le_member checkLabel weight i).trans
      (le_iSup (fun x : bSet B => memberValue (V B) x filter) (checkLabel i))
  simp only [orderFilterValue, memberValue_bSet, sup_assoc]
  refine le_inf hsub (le_inf hnonempty (le_inf ?_ ?_))
  · change ⊤ ≤ ⨅ x : bSet B, lattice.imp (x ∈ᴮ filter)
      (⨅ y : bSet B, lattice.imp (y ∈ᴮ domainName P checkLabel)
        (lattice.imp (edgeValue (V B) (orderName P checkLabel) x y) (y ∈ᴮ filter)))
    have hext : bSet.B_ext (fun x : bSet B =>
        ⨅ y : bSet B, lattice.imp (y ∈ᴮ domainName P checkLabel)
          (lattice.imp (edgeValue (V B) (orderName P checkLabel) x y) (y ∈ᴮ filter))) :=
      bSet.B_ext_iInf fun y => bSet.B_ext_imp (bSet.B_ext_const _)
        (bSet.B_ext_imp (hedgeLeft y) (bSet.B_ext_const _))
    rw [weighted_bounded_forall checkLabel weight _ hext]
    apply le_iInf
    intro i
    apply lattice.bv_imp_intro
    simp only [top_inf_eq]
    change weight i ≤ ⨅ y : bSet B, lattice.imp (y ∈ᴮ weightedSet checkLabel P.member)
      (lattice.imp (edgeValue (V B) (orderName P checkLabel) (checkLabel i) y) (y ∈ᴮ filter))
    rw [weighted_bounded_forall checkLabel P.member _
      (bSet.B_ext_imp (hedgeRight (checkLabel i)) (bSet.B_ext_mem_left filter))]
    apply le_iInf
    intro j
    apply lattice.bv_imp_intro
    apply lattice.bv_imp_intro
    rw [orderName_edge P checkLabel hdiscrete,
      member_weightedSet_discrete checkLabel hdiscrete weight]
    exact (inf_le_inf inf_le_left le_rfl).trans (hup i j)
  · change ⊤ ≤ ⨅ x : bSet B, lattice.imp (x ∈ᴮ filter)
      (⨅ y : bSet B, lattice.imp (y ∈ᴮ filter)
        (Erdos597Object.compatibleValue (V B) filter (orderName P checkLabel) x y))
    rw [weighted_forall_two checkLabel weight _
      (compatible_left_ext filter (orderName P checkLabel))
      (compatible_right_ext filter (orderName P checkLabel))]
    apply le_iInf
    intro i
    apply lattice.bv_imp_intro
    simp only [top_inf_eq]
    apply le_iInf
    intro j
    apply lattice.bv_imp_intro
    unfold Erdos597Object.compatibleValue
    change weight i ⊓ weight j ≤ ⨆ z : bSet B,
      (z ∈ᴮ weightedSet checkLabel weight) ⊓
        (edgeValue (V B) (orderName P checkLabel) z (checkLabel i) ⊓
          edgeValue (V B) (orderName P checkLabel) z (checkLabel j))
    rw [weighted_bounded_exists checkLabel weight _
      (compatibleWitness_ext (orderName P checkLabel) (checkLabel i) (checkLabel j))]
    simp only [orderName_edge P checkLabel hdiscrete]
    exact hdir i j

theorem intersection_value (left right : I → B) :
    (⨆ x : bSet B, (x ∈ᴮ weightedSet checkLabel left) ⊓
      (x ∈ᴮ weightedSet checkLabel right)) = ⨆ i, left i ⊓ right i := by
  rw [weighted_bounded_exists checkLabel left _ (bSet.B_ext_mem_left _)]
  apply iSup_congr
  intro i
  rw [member_weightedSet_discrete checkLabel (fun _ _ h => checkLabel_discrete h)]

theorem meetsFamilyValue_of_weights {D : Type} (weight : I → B) (dense : D → I → B)
    (hmeets : ∀ d, (⨆ i, weight i ⊓ dense d i) = ⊤) :
    ⊤ ≤ meetsFamilyValue (V B) (weightedSet checkLabel weight)
      (weightedSet (fun d => weightedSet checkLabel (dense d)) (fun _ => ⊤)) := by
  unfold meetsFamilyValue
  change ⊤ ≤ ⨅ d : bSet B, lattice.imp
    (d ∈ᴮ weightedSet (fun d => weightedSet checkLabel (dense d)) (fun _ => ⊤))
    (⨆ x : bSet B, (x ∈ᴮ weightedSet checkLabel weight) ⊓ (x ∈ᴮ d))
  rw [weighted_bounded_forall _ _ _
    (bSet.B_ext_iSup fun x => bSet.B_ext_inf (bSet.B_ext_const _) (bSet.B_ext_mem_right x))]
  apply le_iInf
  intro d
  apply lattice.bv_imp_intro
  simp only [top_inf_eq, intersection_value, hmeets]
  exact le_rfl

theorem dense_coefficients (P : BooleanPoset B I) (dense : I → B)
    (hdense : ⊤ ≤ denseValue (V B) (domainName P checkLabel) (orderName P checkLabel)
      (weightedSet checkLabel dense)) :
    ∀ j, P.member j ≤ ⨆ i, dense i ⊓ P.leValue i j := by
  intro j
  have hbound := (hdense.trans inf_le_right).trans
    (iInf_le _ (checkLabel (B := B) j))
  change ⊤ ≤ lattice.imp (checkLabel j ∈ᴮ domainName P checkLabel)
    (⨆ x : bSet B, (x ∈ᴮ weightedSet checkLabel dense) ⊓
      edgeValue (V B) (orderName P checkLabel) x (checkLabel j)) at hbound
  rw [domainName_member P checkLabel (fun _ _ h => checkLabel_discrete h)] at hbound
  have h := lattice.imp_eq_top_iff.mp (top_unique hbound)
  have hedge : bSet.B_ext
      (fun x => edgeValue (V B) (orderName P checkLabel) x (checkLabel j)) := by
    change bSet.B_ext (fun x => bSet.pair x (checkLabel j) ∈ᴮ orderName P checkLabel)
    exact bSet.B_ext_pair_mem_left
  rw [weighted_bounded_exists checkLabel dense _ hedge] at h
  simpa only [orderName_edge P checkLabel (fun _ _ h => checkLabel_discrete h)] using! h

end Erdos597Object.WeightedFilterModel
