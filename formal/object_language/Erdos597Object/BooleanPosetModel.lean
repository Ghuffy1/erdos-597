import Erdos597Object.BooleanCCCBridge

set_option backward.isDefEq.respectTransparency false

/-! The encoded Boolean-valued poset satisfies the first-order partial-order formula. -/

namespace Erdos597Object.BooleanPosetModel

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open scoped Flypitch.bSet
open Erdos597Object.BooleanSets Erdos597Object.BooleanIteration
open Erdos597Object.BooleanPosetCoding

variable {B I : Type} [CompleteBooleanAlgebra B]

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

theorem weighted_forall_two (element : I → bSet B) (weight : I → B)
    (body : bSet B → bSet B → B)
    (hleft : ∀ y, bSet.B_ext (fun x => body x y))
    (hright : ∀ x, bSet.B_ext (body x)) :
    (⨅ x : bSet B, lattice.imp (x ∈ᴮ weightedSet element weight)
      (⨅ y : bSet B, lattice.imp (y ∈ᴮ weightedSet element weight) (body x y))) =
      ⨅ i, lattice.imp (weight i) (⨅ j, lattice.imp (weight j) (body (element i) (element j))) := by
  have hinner : bSet.B_ext (fun x => ⨅ y : bSet B,
      lattice.imp (y ∈ᴮ weightedSet element weight) (body x y)) :=
    bSet.B_ext_iInf fun y => bSet.B_ext_imp (bSet.B_ext_const _) (hleft y)
  rw [weighted_bounded_forall element weight _ hinner]
  apply iInf_congr
  intro i
  congr 1
  exact weighted_bounded_forall element weight (body (element i)) (hright (element i))

theorem weighted_forall_three (element : I → bSet B) (weight : I → B)
    (body : bSet B → bSet B → bSet B → B)
    (hfirst : ∀ y z, bSet.B_ext (fun x => body x y z))
    (hsecond : ∀ x z, bSet.B_ext (fun y => body x y z))
    (hthird : ∀ x y, bSet.B_ext (body x y)) :
    (⨅ x : bSet B, lattice.imp (x ∈ᴮ weightedSet element weight)
      (⨅ y : bSet B, lattice.imp (y ∈ᴮ weightedSet element weight)
        (⨅ z : bSet B, lattice.imp (z ∈ᴮ weightedSet element weight) (body x y z)))) =
      ⨅ i, lattice.imp (weight i) (⨅ j, lattice.imp (weight j)
        (⨅ k, lattice.imp (weight k) (body (element i) (element j) (element k)))) := by
  have hleft : ∀ y, bSet.B_ext (fun x => ⨅ z : bSet B,
      lattice.imp (z ∈ᴮ weightedSet element weight) (body x y z)) :=
    fun y => bSet.B_ext_iInf fun z => bSet.B_ext_imp (bSet.B_ext_const _) (hfirst y z)
  have hright : ∀ x, bSet.B_ext (fun y => ⨅ z : bSet B,
      lattice.imp (z ∈ᴮ weightedSet element weight) (body x y z)) :=
    fun x => bSet.B_ext_iInf fun z => bSet.B_ext_imp (bSet.B_ext_const _) (hsecond x z)
  rw [weighted_forall_two element weight _ hleft hright]
  apply iInf_congr
  intro i
  congr 1
  apply iInf_congr
  intro j
  congr 1
  exact weighted_bounded_forall element weight _ (hthird (element i) (element j))

def reflexiveBody (order x : bSet B) : B := edgeValue (V B) order x x

def antisymmetricBody (order x y : bSet B) : B :=
  lattice.imp (edgeValue (V B) order x y ⊓ edgeValue (V B) order y x) (x =ᴮ y)

def transitiveBody (order x y z : bSet B) : B :=
  lattice.imp (edgeValue (V B) order x y ⊓ edgeValue (V B) order y z)
    (edgeValue (V B) order x z)

theorem reflexiveBody_ext (order : bSet B) : bSet.B_ext (reflexiveBody order) := by
  intro x y
  change (x =ᴮ y) ⊓ (bSet.pair x x ∈ᴮ order) ≤ bSet.pair y y ∈ᴮ order
  exact bSet.subst_congr_mem_left'
    (bSet.pair_congr inf_le_left inf_le_left) inf_le_right

theorem antisymmetricBody_left_ext (order y : bSet B) :
    bSet.B_ext (fun x => antisymmetricBody order x y) :=
  bSet.B_ext_imp (bSet.B_ext_inf bSet.B_ext_pair_mem_left bSet.B_ext_pair_mem_right)
    (bSet.B_ext_eq_left y)

theorem antisymmetricBody_right_ext (order x : bSet B) :
    bSet.B_ext (antisymmetricBody order x) :=
  bSet.B_ext_imp (bSet.B_ext_inf bSet.B_ext_pair_mem_right bSet.B_ext_pair_mem_left)
    (bSet.B_ext_eq_right x)

theorem transitiveBody_first_ext (order y z : bSet B) :
    bSet.B_ext (fun x => transitiveBody order x y z) :=
  bSet.B_ext_imp (bSet.B_ext_inf bSet.B_ext_pair_mem_left (bSet.B_ext_const _))
    bSet.B_ext_pair_mem_left

theorem transitiveBody_second_ext (order x z : bSet B) :
    bSet.B_ext (fun y => transitiveBody order x y z) :=
  bSet.B_ext_imp (bSet.B_ext_inf bSet.B_ext_pair_mem_right bSet.B_ext_pair_mem_left)
    (bSet.B_ext_const _)

theorem transitiveBody_third_ext (order x y : bSet B) :
    bSet.B_ext (transitiveBody order x y) :=
  bSet.B_ext_imp (bSet.B_ext_inf (bSet.B_ext_const _) bSet.B_ext_pair_mem_right)
    bSet.B_ext_pair_mem_right

theorem relationBetween_coded (P : BooleanPoset B I) (element : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (element i =ᴮ element j) = ⊥) :
    ⊤ ≤ relationBetweenValue (V B) (domainName P element)
      (domainName P element) (orderName P element) := by
  have hext : bSet.B_ext (fun entry : bSet B =>
      ⨆ x : bSet B, (x ∈ᴮ domainName P element) ⊓
        ⨆ y : bSet B, (y ∈ᴮ domainName P element) ⊓ (entry =ᴮ bSet.pair x y)) :=
    bSet.B_ext_iSup fun x => bSet.B_ext_inf (bSet.B_ext_const _)
      (bSet.B_ext_iSup fun y => bSet.B_ext_inf (bSet.B_ext_const _)
        (bSet.B_ext_eq_left (bSet.pair x y)))
  change ⊤ ≤ ⨅ entry : bSet B, lattice.imp
    (entry ∈ᴮ weightedSet (pairLabels element) (fun ij => P.leValue ij.1 ij.2))
    (⨆ x : bSet B, (x ∈ᴮ domainName P element) ⊓
      ⨆ y : bSet B, (y ∈ᴮ domainName P element) ⊓ (entry =ᴮ bSet.pair x y))
  rw [weighted_bounded_forall (pairLabels element) _ _ hext]
  apply le_iInf
  intro ij
  apply lattice.bv_imp_intro
  simp only [top_inf_eq]
  apply le_iSup_of_le (element ij.1)
  apply le_inf
  · rw [domainName_member P element hdiscrete]
    exact (P.le_members ij.1 ij.2).trans inf_le_left
  · apply le_iSup_of_le (element ij.2)
    apply le_inf
    · rw [domainName_member P element hdiscrete]
      exact (P.le_members ij.1 ij.2).trans inf_le_right
    · exact bSet.bv_refl

theorem partialOrderValue_coded (P : BooleanPoset B I) (element : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (element i =ᴮ element j) = ⊥) :
    ⊤ ≤ partialOrderValue (V B) (domainName P element) (orderName P element) := by
  simp only [partialOrderValue, memberValue_bSet, eqValue_bSet, sup_assoc]
  refine le_inf (relationBetween_coded P element hdiscrete) (le_inf ?_ (le_inf ?_ ?_))
  · change ⊤ ≤ ⨅ x : bSet B, lattice.imp (x ∈ᴮ weightedSet element P.member)
      (reflexiveBody (orderName P element) x)
    rw [weighted_bounded_forall element P.member _ (reflexiveBody_ext _)]
    apply le_iInf
    intro i
    apply lattice.bv_imp_intro
    simp only [top_inf_eq]
    change P.member i ≤ edgeValue (V B) (orderName P element) (element i) (element i)
    rw [orderName_edge P element hdiscrete]
    exact P.reflexive i
  · change ⊤ ≤ ⨅ x : bSet B, lattice.imp (x ∈ᴮ weightedSet element P.member)
      (⨅ y : bSet B, lattice.imp (y ∈ᴮ weightedSet element P.member)
        (antisymmetricBody (orderName P element) x y))
    rw [weighted_forall_two element P.member _
      (antisymmetricBody_left_ext _) (antisymmetricBody_right_ext _)]
    have hbody : ∀ i j, antisymmetricBody (orderName P element) (element i) (element j) = ⊤ := by
      intro i j
      by_cases hij : i = j
      · subst j
        simp [antisymmetricBody, lattice.imp]
      · unfold antisymmetricBody
        rw [orderName_edge P element hdiscrete, orderName_edge P element hdiscrete,
          P.antisymmetric i j hij, hdiscrete i j hij]
        simp [lattice.imp]
    simp [hbody, lattice.imp]
  · change ⊤ ≤ ⨅ x : bSet B, lattice.imp (x ∈ᴮ weightedSet element P.member)
      (⨅ y : bSet B, lattice.imp (y ∈ᴮ weightedSet element P.member)
        (⨅ z : bSet B, lattice.imp (z ∈ᴮ weightedSet element P.member)
          (transitiveBody (orderName P element) x y z)))
    rw [weighted_forall_three element P.member _
      (transitiveBody_first_ext _) (transitiveBody_second_ext _) (transitiveBody_third_ext _)]
    have hbody : ∀ i j k, transitiveBody (orderName P element)
        (element i) (element j) (element k) = ⊤ := by
      intro i j k
      unfold transitiveBody
      rw [orderName_edge P element hdiscrete, orderName_edge P element hdiscrete,
        orderName_edge P element hdiscrete]
      exact lattice.imp_eq_top_iff.mpr (P.transitive i j k)
    simp [hbody, lattice.imp]

theorem partialOrderValue_checkLabels (P : BooleanPoset B I) :
    ⊤ ≤ partialOrderValue (V B) (domainName P checkLabel) (orderName P checkLabel) :=
  partialOrderValue_coded P checkLabel (fun _ _ h => checkLabel_discrete h)

theorem partialOrder_formula_value (P : BooleanPoset B I) (element : I → bSet B) :
    boolean_realize_bounded_formula (S := V B)
      (orderName P element :: domainName P element :: []) (partialOrder var1 var0) [] =
        partialOrderValue (V B) (domainName P element) (orderName P element) := by
  rw [realize_partialOrder]
  simp [var0, var1]

theorem partialOrder_check_formula (P : BooleanPoset B I) :
    ⊤ ≤ boolean_realize_bounded_formula (S := V B)
      (orderName P checkLabel :: domainName P checkLabel :: []) (partialOrder var1 var0) [] := by
  rw [partialOrder_formula_value]
  exact partialOrderValue_checkLabels P

end Erdos597Object.BooleanPosetModel
