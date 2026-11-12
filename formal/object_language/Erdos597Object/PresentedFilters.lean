import Erdos597Object.ContextualCCC

set_option backward.isDefEq.respectTransparency false

/-! Filter witnesses transported from weighted presentations to the original names. -/

namespace Erdos597Object.PresentedFilters

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanAntichains BooleanPosetModel PresentedPosets PresentedCompatibility

variable {B I D : Type} [CompleteBooleanAlgebra B]

theorem context_le_congr {context : B} {x y : bSet B}
    (heq : context ≤ x =ᴮ y) (predicate : bSet B → B) (hext : bSet.B_ext predicate)
    (h : context ≤ predicate y) : context ≤ predicate x := by
  calc
    context = context ⊓ predicate y := (inf_eq_left.mpr h).symm
    _ = context ⊓ predicate x := (context_predicate_congr heq predicate hext).symm
    _ ≤ predicate x := inf_le_right

theorem orderFilter_from_weights (context : B) (domain relation : bSet B)
    (element : I → bSet B) (weight values : I → B)
    (heq : context ≤ domain =ᴮ weightedSet element weight)
    (hmembers : ∀ i, values i ≤ element i ∈ᴮ domain)
    (hcover : context ≤ ⨆ i, values i)
    (hup : ∀ i j, values i ⊓ weight j ⊓
      edgeValue (V B) relation (element i) (element j) ≤ values j)
    (hdir : ∀ i j, values i ⊓ values j ≤ ⨆ k, values k ⊓
      (edgeValue (V B) relation (element k) (element i) ⊓
        edgeValue (V B) relation (element k) (element j))) :
    context ≤ orderFilterValue (V B) domain relation (weightedSet element values) := by
  let filter := weightedSet element values
  have hsub : context ≤ subsetValue (V B) filter domain := by
    rw [weighted_subset_value]
    apply le_iInf
    intro i
    exact lattice.le_imp_iff.mpr (inf_le_right.trans (hmembers i))
  have hnonempty : context ≤ nonemptyValue (V B) filter := by
    simpa only [filter, weighted_nonempty] using hcover
  simp only [orderFilterValue, memberValue_bSet, sup_assoc]
  refine le_inf hsub (le_inf hnonempty (le_inf ?_ ?_))
  · change context ≤ ⨅ x : bSet B, lattice.imp (x ∈ᴮ filter)
      (⨅ y : bSet B, lattice.imp (y ∈ᴮ domain)
        (lattice.imp (edgeValue (V B) relation x y) (y ∈ᴮ filter)))
    have hext : bSet.B_ext (fun x : bSet B =>
        ⨅ y : bSet B, lattice.imp (y ∈ᴮ domain)
          (lattice.imp (edgeValue (V B) relation x y) (y ∈ᴮ filter))) :=
      bSet.B_ext_iInf fun y => bSet.B_ext_imp (bSet.B_ext_const _)
        (bSet.B_ext_imp (edge_left_ext relation y) (bSet.B_ext_const _))
    rw [weighted_bounded_forall element values _ hext]
    apply le_iInf
    intro i
    apply lattice.bv_imp_intro
    apply context_le_congr (inf_le_left.trans heq)
      (fun target => ⨅ y : bSet B, lattice.imp (y ∈ᴮ target)
        (lattice.imp (edgeValue (V B) relation (element i) y) (y ∈ᴮ filter)))
    · exact bSet.B_ext_iInf fun y =>
        bSet.B_ext_imp (bSet.B_ext_mem_right y) (bSet.B_ext_const _)
    · rw [weighted_bounded_forall element weight _
        (bSet.B_ext_imp (edge_right_ext relation (element i)) (bSet.B_ext_mem_left filter))]
      apply le_iInf
      intro j
      apply lattice.bv_imp_intro
      apply lattice.bv_imp_intro
      exact ((inf_le_inf (inf_le_inf inf_le_right le_rfl) le_rfl).trans (hup i j)).trans
        (weight_le_member element values j)
  · change context ≤ ⨅ x : bSet B, lattice.imp (x ∈ᴮ filter)
      (⨅ y : bSet B, lattice.imp (y ∈ᴮ filter)
        (Erdos597Object.compatibleValue (V B) filter relation x y))
    rw [weighted_forall_two element values _
      (compatible_left_ext filter relation) (compatible_right_ext filter relation)]
    apply le_iInf
    intro i
    apply lattice.bv_imp_intro
    apply le_iInf
    intro j
    apply lattice.bv_imp_intro
    unfold Erdos597Object.compatibleValue
    change context ⊓ values i ⊓ values j ≤ ⨆ z : bSet B,
      (z ∈ᴮ weightedSet element values) ⊓
        (edgeValue (V B) relation z (element i) ⊓ edgeValue (V B) relation z (element j))
    rw [weighted_bounded_exists element values _
      (compatibleWitness_ext relation (element i) (element j))]
    exact (inf_le_inf inf_le_right le_rfl).trans (hdir i j)

theorem meetsFamily_from_weights (context : B) (family : bSet B)
    (element : I → bSet B) (values : I → B)
    (denseSet : D → bSet B) (familyWeight : D → B)
    (heq : context ≤ family =ᴮ weightedSet denseSet familyWeight)
    (hmeets : ∀ d, context ⊓ familyWeight d ≤
      ⨆ i, values i ⊓ (element i ∈ᴮ denseSet d)) :
    context ≤ meetsFamilyValue (V B) (weightedSet element values) family := by
  apply context_le_congr heq
    (fun target => meetsFamilyValue (V B) (weightedSet element values) target)
  · unfold meetsFamilyValue
    exact bSet.B_ext_iInf fun d =>
      bSet.B_ext_sup (bSet.B_ext_compl (bSet.B_ext_mem_right d)) (bSet.B_ext_const _)
  · unfold meetsFamilyValue
    change context ≤ ⨅ d : bSet B, lattice.imp
      (d ∈ᴮ weightedSet denseSet familyWeight)
      (⨆ x : bSet B, (x ∈ᴮ weightedSet element values) ⊓ (x ∈ᴮ d))
    rw [weighted_bounded_forall denseSet familyWeight _
      (bSet.B_ext_iSup fun x => bSet.B_ext_inf (bSet.B_ext_const _) (bSet.B_ext_mem_right x))]
    apply le_iInf
    intro d
    apply lattice.bv_imp_intro
    rw [weighted_bounded_exists element values _ (bSet.B_ext_mem_left (denseSet d))]
    exact hmeets d

end Erdos597Object.PresentedFilters
