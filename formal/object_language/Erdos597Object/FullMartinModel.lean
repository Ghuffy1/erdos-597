import Erdos597Object.UpwardClosure
import Erdos597Object.OmegaOneLabels

set_option backward.isDefEq.respectTransparency false

/-! The full Martin-axiom sentence in the constructed Boolean-valued model. -/

namespace Erdos597Object.FullMartinModel

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanIteration BooleanSets BooleanInjections ScheduledIteration

theorem family_filter_exists (context : ScheduledIteration.finalAlgebra)
    (domain relation family : bSet ScheduledIteration.finalAlgebra)
    (denseSet : Labels → bSet ScheduledIteration.finalAlgebra)
    (active : Labels → ScheduledIteration.finalAlgebra)
    (hnonempty : context ≤ nonemptyValue (V ScheduledIteration.finalAlgebra) domain)
    (horder : context ≤ partialOrderValue (V ScheduledIteration.finalAlgebra) domain relation)
    (hccc : context ≤ countableChainConditionValue (V ScheduledIteration.finalAlgebra) domain relation)
    (hfamily : context ≤ family =ᴮ weightedSet denseSet active)
    (hactive : ∀ d, active d ≤ context)
    (hdense : ∀ d, active d ≤ denseValue (V ScheduledIteration.finalAlgebra) domain relation (denseSet d)) :
    context ≤ ⨆ filter : bSet ScheduledIteration.finalAlgebra,
      orderFilterValue (V ScheduledIteration.finalAlgebra) domain relation filter ⊓
        meetsFamilyValue (V ScheduledIteration.finalAlgebra) filter family := by
  haveI : Infinite Labels := Cardinal.infinite_iff.mpr (by
    rw [labels_card]
    exact Cardinal.aleph0_le_aleph 1)
  obtain ⟨seed, hseed⟩ := PosetNameWitnesses.exists_seed domain hnonempty
  have hDenseAll : ∀ d, context ⊓ active d ≤ denseValue (V ScheduledIteration.finalAlgebra)
      domain relation (denseSet d) := fun d => inf_le_right.trans (hdense d)
  let e : Labels ≃ IndexedHull.Labels Labels := Classical.choice (Cardinal.eq.mp
    (labels_card.trans (IndexedHull.labels_card_eq labels_card).symm))
  let element : Labels → bSet ScheduledIteration.finalAlgebra :=
    fun i => BooleanNameHull.name context domain relation seed hseed active denseSet hDenseAll (e i)
  have hmember : ∀ i, context ≤ element i ∈ᴮ domain := fun i =>
    BooleanNameHull.name_member context domain relation seed hseed active denseSet hDenseAll (e i)
  have hcommon : ∀ i j, ∃ k, context ⊓ Erdos597Object.compatibleValue
      (V ScheduledIteration.finalAlgebra) domain relation (element i) (element j) ≤
      edgeValue (V ScheduledIteration.finalAlgebra) relation (element k) (element i) ⊓
        edgeValue (V ScheduledIteration.finalAlgebra) relation (element k) (element j) := by
    intro i j
    obtain ⟨k, hk⟩ := BooleanNameHull.name_common context domain relation seed hseed active denseSet hDenseAll (e i) (e j)
    refine ⟨e.symm k, ?_⟩
    simpa only [element, e.apply_symm_apply] using! hk
  have hdenseClosed : ∀ d j, ∃ k, context ⊓ active d ≤
      (element k ∈ᴮ denseSet d) ⊓ edgeValue (V ScheduledIteration.finalAlgebra) relation (element k) (element j) := by
    intro d j
    obtain ⟨k, hk⟩ := BooleanNameHull.name_dense context domain relation seed hseed active denseSet hDenseAll d (e j)
    refine ⟨e.symm k, ?_⟩
    simpa only [element, e.apply_symm_apply] using! hk
  let weight := SeparatedNames.weight context element
  have hvalid : ∀ i, weight i ≤ context ∧ weight i ≤ element i ∈ᴮ domain :=
    fun i => ⟨SeparatedNames.weight_le_context context element i,
      (SeparatedNames.weight_le_context context element i).trans (hmember i)⟩
  have hseparate := SeparatedNames.weights_separated context element
  have hcovered := SeparatedNames.weight_cover_each context element
  let P := PresentedPosets.ofNames context domain relation element weight hvalid hseparate horder
  let dense : Labels → Labels → ScheduledIteration.finalAlgebra :=
    fun d i => weight i ⊓ (element i ∈ᴮ denseSet d)
  have hP : BooleanCountableChainCondition P :=
    HullCoefficients.booleanCCC context domain relation element weight hvalid hseparate horder hcovered hcommon hccc
  have hDensity : ∀ d j, active d ⊓ P.member j ≤ ⨆ i, dense d i ⊓ P.leValue i j := by
    intro d j
    exact HullCoefficients.dense_coefficients context domain relation element weight
      (fun i => (hvalid i).1) hcovered active denseSet hdenseClosed d j
  obtain ⟨value, hvalue, hcover, _, hdir, hmeets⟩ :=
    ContextualMartinModel.contextual_coefficients context P active dense hP
      (SeparatedNames.weights_cover context element) hactive (fun _ _ => inf_le_left) hDensity
  have hValueContext : ∀ i, value i ≤ context := fun i => (hvalue i).trans (hvalid i).1
  have hValueMember : ∀ i, value i ≤ element i ∈ᴮ domain := fun i => (hvalue i).trans (hvalid i).2
  have hDirRaw : ∀ i j, value i ⊓ value j ≤ ⨆ k, value k ⊓
      (edgeValue (V ScheduledIteration.finalAlgebra) relation (element k) (element i) ⊓
        edgeValue (V ScheduledIteration.finalAlgebra) relation (element k) (element j)) := by
    intro i j
    exact (hdir i j).trans (iSup_mono fun k =>
      inf_le_inf le_rfl (inf_le_inf inf_le_right inf_le_right))
  let filter := weightedSet domain.func (UpwardClosure.weight domain relation element value)
  have hFilter : context ≤ orderFilterValue (V ScheduledIteration.finalAlgebra) domain relation filter :=
    UpwardClosure.orderFilter_value domain relation element value hValueContext hValueMember horder hcover hDirRaw
  have hMeets : context ≤ meetsFamilyValue (V ScheduledIteration.finalAlgebra) filter family := by
    apply PresentedFilters.meetsFamily_from_weights context family domain.func _ denseSet active hfamily
    intro d
    apply inf_le_right.trans
    apply UpwardClosure.meets_value domain relation (denseSet d) element value hValueContext hValueMember horder
    exact (hmeets d).trans (iSup_mono fun i => inf_le_inf le_rfl inf_le_right)
  exact le_iSup_of_le filter (le_inf hFilter hMeets)

theorem filter_exists (context : ScheduledIteration.finalAlgebra)
    (kappa domain relation family : bSet ScheduledIteration.finalAlgebra)
    (hkappa : context ≤ omegaOneValue (V ScheduledIteration.finalAlgebra) kappa)
    (hnonempty : context ≤ nonemptyValue (V ScheduledIteration.finalAlgebra) domain)
    (horder : context ≤ partialOrderValue (V ScheduledIteration.finalAlgebra) domain relation)
    (hccc : context ≤ countableChainConditionValue (V ScheduledIteration.finalAlgebra) domain relation)
    (hfamily : context ≤ injectsIntoValue (V ScheduledIteration.finalAlgebra) family kappa)
    (hdense : context ≤ ⨅ subset : bSet ScheduledIteration.finalAlgebra,
      lattice.imp (subset ∈ᴮ family) (denseValue (V ScheduledIteration.finalAlgebra) domain relation subset)) :
    context ≤ ⨆ filter : bSet ScheduledIteration.finalAlgebra,
      orderFilterValue (V ScheduledIteration.finalAlgebra) domain relation filter ⊓
        meetsFamilyValue (V ScheduledIteration.finalAlgebra) filter family := by
  have hinjects := OmegaOneLabels.injection_of_omegaOne ScheduledIteration.finalAlgebra.ccc kappa family hkappa hfamily
  obtain ⟨denseSet, active, hvalid, _, heq⟩ := presentation_of_injection family OmegaOneLabels.element
    OmegaOneLabels.element_discrete hinjects
  apply family_filter_exists context domain relation family denseSet active hnonempty horder hccc heq
    (fun d => (hvalid d).1)
  intro d
  exact lattice.bv_context_apply (((hvalid d).1.trans hdense).trans (iInf_le _ (denseSet d))) (hvalid d).2

theorem martin_at (context : ScheduledIteration.finalAlgebra) (kappa : bSet ScheduledIteration.finalAlgebra)
    (hkappa : context ≤ omegaOneValue (V ScheduledIteration.finalAlgebra) kappa) :
    context ≤ martinAxiomAtValue (V ScheduledIteration.finalAlgebra) kappa := by
  unfold martinAxiomAtValue
  apply le_iInf
  intro domain
  apply le_iInf
  intro relation
  apply le_iInf
  intro family
  apply lattice.bv_imp_intro
  apply filter_exists _ kappa domain relation family
  · exact inf_le_left.trans hkappa
  · exact inf_le_right.trans inf_le_left
  · exact inf_le_right.trans (inf_le_right.trans inf_le_left)
  · exact inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  · exact inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
  · exact inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))

theorem final_martin : ⊤ ≤ martinAxiomAlephOneValue (V ScheduledIteration.finalAlgebra) := by
  unfold martinAxiomAlephOneValue
  apply le_iInf
  intro kappa
  apply lattice.bv_imp_intro
  exact martin_at _ kappa inf_le_right

theorem final_martin_sentence :
    ⊤ ≤ Flypitch.fol.bfol.boolean_realize_sentence (V ScheduledIteration.finalAlgebra) martinAxiomAlephOne := by
  rw [realize_martinAxiomAlephOne]
  exact final_martin

end Erdos597Object.FullMartinModel
