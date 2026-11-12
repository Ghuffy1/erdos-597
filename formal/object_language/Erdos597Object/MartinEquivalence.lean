import Erdos597Object.PosetEncoding
import Erdos597Object.AssertionInterpretation

set_option backward.isDefEq.respectTransparency false

/-! Match the set-theoretic Martin-axiom sentence to the axiom used in the proof. -/

namespace Erdos597Object.MartinEquivalence

open Cardinal Ordinal Flypitch.fol.bfol
open scoped Cardinal Ordinal
open Erdos597Object.SetInterpretation Erdos597Object.SetFunctions
open Erdos597Object.MartinInSets Erdos597Object.MartinTransport
open Erdos597Object.SetSubsets Erdos597Object.SetPosets Erdos597Object.PosetEncoding
open Erdos597Object.OriginalPartition Erdos597Object.AssertionInterpretation

noncomputable section

theorem martinAxiom_value_of_original (hMA : Erdos597.MartinAxiomAlephOne) :
    martinAxiomAlephOneValue setStructure := by
  rw [martinAxiomAlephOneValue_set, martinAxiomAtValue_set]
  intro conditions order family hnonempty horder hccc hfamily hdense
  letI orderInstance : PartialOrder (Members conditions) := decodedPartialOrder horder
  letI : Preorder (Members conditions) := orderInstance.toPreorder
  letI : LE (Members conditions) := orderInstance.toLE
  letI : LT (Members conditions) := orderInstance.toLT
  let I := Members family
  let D : I → Set (Members conditions) := fun i => membersSubset conditions i.val
  have hI : #(Shrink.{0} I) ≤ ℵ₁ :=
    (injectsInto_omegaOne_iff family).mp hfamily
  have hD : ∀ i x, ∃ y ∈ D i, y ≤ x := by
    intro i
    exact denseValue_membersSubset horder (hdense i.val i.property)
  obtain ⟨p, hp⟩ := (nonemptyValue_set _).mp hnonempty
  obtain ⟨F, _, hF⟩ := small_martin_axiom hMA (Members conditions)
    ((countableChainConditionValue_iff horder).mp hccc) I hI D hD ⟨p, hp⟩
  refine ⟨subsetCode conditions (F : Set (Members conditions)), orderFilterValue_of_filter horder F, ?_⟩
  rw [meetsFamilyValue_set]
  intro denseSet hmem
  obtain ⟨q, hqF, hqD⟩ := hF ⟨denseSet, hmem⟩
  exact ⟨q.val, (member_mem_subsetCode _ _ _).mpr hqF, hqD⟩

theorem original_of_martinAxiom_value (hMA : martinAxiomAlephOneValue setStructure) :
    Erdos597.MartinAxiomAlephOne := by
  rw [martinAxiomAlephOneValue_set, martinAxiomAtValue_set] at hMA
  apply unbased_to_based
  intro P inst hP hccc I hI D hD
  let conditions := typeCode P
  let order := orderCode P
  have horder : partialOrderValue setStructure conditions order := orderCode_partialOrder P
  letI orderInstance : PartialOrder (Members conditions) := decodedPartialOrder horder
  letI : Preorder (Members conditions) := orderInstance.toPreorder
  letI : LE (Members conditions) := orderInstance.toLE
  letI : LT (Members conditions) := orderInstance.toLT
  let e : P ≃o Members conditions := typeOrderIso P
  let D' : I → Set (Members conditions) := fun i => e.symm ⁻¹' D i
  have hD' : ∀ i x, ∃ y ∈ D' i, y ≤ x := by
    intro i x
    obtain ⟨y, hyD, hyx⟩ := hD i (e.symm x)
    exact ⟨e y, by simpa [D'] using hyD, by simpa using e.monotone hyx⟩
  have hnonempty : nonemptyValue setStructure conditions := by
    rw [nonemptyValue_set]
    exact ⟨(e hP.some).val, (e hP.some).property⟩
  have hcccValue : countableChainConditionValue setStructure conditions order :=
    (countableChainConditionValue_iff horder).mpr
      (ccc_map_orderIso e ((ccc_original_iff P).mpr hccc))
  have hdense : ∀ denseSet ∈ familyCode D', denseValue setStructure conditions order denseSet := by
    intro denseSet hmem
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hmem
    exact (denseValue_subsetCode_iff horder (D' i)).mpr (hD' i)
  obtain ⟨filter, hfilter, hmeets⟩ := hMA conditions order (familyCode D') hnonempty horder
    hcccValue (familyCode_injectsInto_omegaOne D' hI) hdense
  let F := filterOfValue horder hfilter
  refine ⟨pullbackFilter e F, ?_⟩
  intro i
  obtain ⟨x, hxF, hxD⟩ := (meetsFamilyValue_set _ _).mp hmeets
    (subsetCode conditions (D' i)) (familyIndex D' i).property
  have hx : x ∈ conditions := ((orderFilterValue_set _ _ _).mp hfilter).1 hxF
  let q : Members conditions := ⟨x, hx⟩
  refine ⟨e.symm q, ?_, ?_⟩
  · simpa only [mem_pullbackFilter, e.apply_symm_apply, F, mem_filterOfValue] using hxF
  · exact (member_mem_subsetCode conditions (D' i) q).mp hxD

theorem martinAxiom_sentence_iff_original :
    boolean_realize_sentence setStructure martinAxiomAlephOne ↔ Erdos597.MartinAxiomAlephOne := by
  rw [realize_martinAxiomAlephOne]
  exact ⟨original_of_martinAxiom_value, martinAxiom_value_of_original⟩

theorem positiveConditional_set : boolean_realize_sentence setStructure positiveConditional := by
  unfold positiveConditional boolean_realize_sentence
  rw [boolean_realize_bounded_formula_imp]
  simp only [Flypitch.lattice.imp, sup_Prop_eq]
  change (¬ boolean_realize_sentence setStructure martinAxiomAlephOne) ∨
    boolean_realize_sentence setStructure finiteAssertion
  classical
  simp only [or_iff_not_imp_left, not_not]
  intro h
  exact finiteAssertion_under_MA (martinAxiom_sentence_iff_original.mp h)

end

end Erdos597Object.MartinEquivalence
