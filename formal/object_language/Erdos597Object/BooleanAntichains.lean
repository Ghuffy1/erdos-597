import Erdos597Object.BooleanFunctionFibres

set_option backward.isDefEq.respectTransparency false

/-! Weighted antichains in the first-order Boolean-valued set model. -/

namespace Erdos597Object.BooleanAntichains

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open scoped Flypitch.bSet
open Erdos597Object.BooleanSets

variable {B : Type} [CompleteBooleanAlgebra B]

theorem compatibleWitness_ext (order x y : bSet B) :
    bSet.B_ext (fun z => edgeValue (V B) order z x ⊓ edgeValue (V B) order z y) :=
  bSet.B_ext_inf bSet.B_ext_pair_mem_left bSet.B_ext_pair_mem_left

theorem compatible_left_ext (conditions order y : bSet B) :
    bSet.B_ext (fun x => Erdos597Object.compatibleValue (V B) conditions order x y) := by
  unfold Erdos597Object.compatibleValue
  apply bSet.B_ext_iSup
  intro z
  exact bSet.B_ext_inf (bSet.B_ext_const _)
    (bSet.B_ext_inf bSet.B_ext_pair_mem_right (bSet.B_ext_const _))

theorem compatible_right_ext (conditions order x : bSet B) :
    bSet.B_ext (fun y => Erdos597Object.compatibleValue (V B) conditions order x y) := by
  unfold Erdos597Object.compatibleValue
  apply bSet.B_ext_iSup
  intro z
  exact bSet.B_ext_inf (bSet.B_ext_const _)
    (bSet.B_ext_inf (bSet.B_ext_const _) bSet.B_ext_pair_mem_right)

theorem antichainInner_ext (conditions order family : bSet B) :
    bSet.B_ext (fun x => ⨅ y : bSet B, lattice.imp (y ∈ᴮ family)
      ((x =ᴮ y) ⊔ (Erdos597Object.compatibleValue (V B) conditions order x y)ᶜ)) := by
  apply bSet.B_ext_iInf
  intro y
  exact bSet.B_ext_imp (bSet.B_ext_const _)
    (bSet.B_ext_sup (bSet.B_ext_eq_left y)
      (bSet.B_ext_compl (compatible_left_ext conditions order y)))

theorem weighted_subset_value {I : Type} (element : I → bSet B) (weight : I → B)
    (conditions : bSet B) :
    subsetValue (V B) (weightedSet element weight) conditions =
      ⨅ i, lattice.imp (weight i) (element i ∈ᴮ conditions) :=
  weighted_bounded_forall element weight (fun x => x ∈ᴮ conditions) (bSet.B_ext_mem_left conditions)

theorem weighted_antichain_value {I : Type} (element : I → bSet B) (weight : I → B)
    (conditions order : bSet B) :
    antichainValue (V B) conditions order (weightedSet element weight) =
      subsetValue (V B) (weightedSet element weight) conditions ⊓
        ⨅ i, lattice.imp (weight i)
          (⨅ j, lattice.imp (weight j) ((element i =ᴮ element j) ⊔
            (Erdos597Object.compatibleValue (V B) conditions order (element i) (element j))ᶜ)) := by
  simp only [antichainValue, memberValue_bSet, eqValue_bSet, sup_assoc]
  change _ ⊓ (⨅ x : bSet B, lattice.imp (x ∈ᴮ weightedSet element weight)
    (⨅ y : bSet B, lattice.imp (y ∈ᴮ weightedSet element weight)
      ((x =ᴮ y) ⊔ (Erdos597Object.compatibleValue (V B) conditions order x y)ᶜ))) = _
  rw [weighted_bounded_forall element weight _
    (antichainInner_ext conditions order (weightedSet element weight))]
  congr 1
  apply iInf_congr
  intro i
  congr 1
  exact weighted_bounded_forall element weight _
    (bSet.B_ext_sup (bSet.B_ext_eq_right (element i))
      (bSet.B_ext_compl (compatible_right_ext conditions order (element i))))

theorem weighted_antichain {I : Type} (element : I → bSet B) (weight : I → B)
    (conditions order : bSet B)
    (hmembers : ∀ i, weight i ≤ element i ∈ᴮ conditions)
    (hincompatible : ∀ i j, i ≠ j → weight i ⊓ weight j ⊓
      Erdos597Object.compatibleValue (V B) conditions order (element i) (element j) = ⊥) :
    ⊤ ≤ antichainValue (V B) conditions order (weightedSet element weight) := by
  rw [weighted_antichain_value, weighted_subset_value]
  apply le_inf
  · apply le_iInf
    intro i
    apply lattice.bv_imp_intro
    simpa only [top_inf_eq] using hmembers i
  · apply le_iInf
    intro i
    apply lattice.bv_imp_intro
    simp only [top_inf_eq]
    apply le_iInf
    intro j
    apply lattice.bv_imp_intro
    by_cases hij : i = j
    · subst j
      simp
    · apply le_sup_of_le_right
      rw [le_compl_iff_disjoint_right, disjoint_iff]
      exact hincompatible i j hij

end Erdos597Object.BooleanAntichains
