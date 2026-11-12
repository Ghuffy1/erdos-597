import Erdos597Object.RelabeledFilters
import Erdos597Object.OutsideRestriction
import Erdos597Object.ContextualDensity

set_option backward.isDefEq.respectTransparency false

/-! Meet contextual dense requirements and transport their filter to arbitrary presented names. -/

namespace Erdos597Object.ContextualMartinModel

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet Cardinal
open BooleanIteration BooleanSets BooleanPosetCoding ScheduledIteration
open ContextCompletion PosetRelabeling CodedDensity

theorem contextual_coefficients (context : ScheduledIteration.finalAlgebra)
    (P : BooleanPoset ScheduledIteration.finalAlgebra Labels)
    (active : Labels → ScheduledIteration.finalAlgebra)
    (dense : Labels → Labels → ScheduledIteration.finalAlgebra)
    (hP : BooleanCountableChainCondition P)
    (hcover : (⨆ i, P.member i) = context)
    (hactive : ∀ d, active d ≤ context)
    (hsubset : ∀ d i, dense d i ≤ P.member i)
    (hdense : ∀ d j, active d ⊓ P.member j ≤ ⨆ i, dense d i ⊓ P.leValue i j) :
    ∃ weight : Labels → ScheduledIteration.finalAlgebra,
      (∀ i, weight i ≤ P.member i) ∧
      context ≤ (⨆ i, weight i) ∧
      (∀ i j, weight i ⊓ P.leValue i j ≤ weight j) ∧
      (∀ i j, weight i ⊓ weight j ≤ ⨆ k, weight k ⊓ (P.leValue k i ⊓ P.leValue k j)) ∧
      (∀ d, active d ≤ ⨆ i, weight i ⊓ dense d i) := by
  haveI : Infinite Labels := Cardinal.infinite_iff.mpr (by
    rw [labels_card]
    exact Cardinal.aleph0_le_aleph 1)
  let wide := withOutside context P
  let wideDense : Labels → Option Labels → ScheduledIteration.finalAlgebra :=
    fun d => outsideDense context (active d) P (dense d)
  let e : Labels ≃ Option Labels := (optionEquiv Labels).symm
  let Q := relabel e wide
  let Qdense : Labels → Labels → ScheduledIteration.finalAlgebra := fun d j => wideDense d (e j)
  have hQccc : MartinTransport.CountableChainCondition (Condition Q) :=
    relabel_ccc ScheduledIteration.finalAlgebra.ccc e wide (withOutside_booleanCCC context P hP)
  have hQcover : (⨆ i, Q.member i) = ⊤ :=
    (relabel_members e wide).trans (withOutside_cover context P hcover)
  have hQdense : ∀ d, ⊤ ≤ denseValue (V ScheduledIteration.finalAlgebra)
      (domainName Q checkLabel) (orderName Q checkLabel) (weightedSet checkLabel (Qdense d)) := by
    intro d
    apply denseValue_of_coefficients Q (Qdense d)
    · intro j
      exact outsideDense_subset context (active d) P (dense d) (hsubset d) (e j)
    · exact relabel_dense e wide (wideDense d) (outsideDense_dense context (active d) P (dense d) (hdense d))
  obtain ⟨weight, hweight, htotal, hup, hdir, hmeets⟩ :=
    FilterCoefficients.final_coefficients Q Qdense hQccc hQcover hQdense
  obtain ⟨wideWeight, hwide, hwideTotal, hwideUp, hwideDir, hwideMeets⟩ :=
    RelabeledFilters.pull_coefficients e wide wideDense weight hweight htotal hup hdir hmeets
  refine ⟨fun i => wideWeight (some i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hwide (some i)
  · exact OutsideRestriction.restricted_cover context P wideWeight hwide hwideTotal
  · exact OutsideRestriction.restricted_upward context P wideWeight hwideUp
  · exact OutsideRestriction.restricted_directed context P wideWeight hwideDir
  · intro d
    exact OutsideRestriction.restricted_meets context (active d) P wideWeight (dense d)
      (hactive d) (hwideMeets d)

theorem presented_filter_exists (context : ScheduledIteration.finalAlgebra)
    (domain relation family : bSet ScheduledIteration.finalAlgebra)
    (element : Labels → bSet ScheduledIteration.finalAlgebra)
    (weight : Labels → ScheduledIteration.finalAlgebra)
    (denseSet : Labels → bSet ScheduledIteration.finalAlgebra)
    (familyWeight : Labels → ScheduledIteration.finalAlgebra)
    (hvalid : ∀ i, weight i ≤ context ∧ weight i ≤ element i ∈ᴮ domain)
    (hseparate : ∀ i j, i ≠ j → weight i ⊓ weight j ⊓ (element i =ᴮ element j) = ⊥)
    (horder : context ≤ partialOrderValue (V ScheduledIteration.finalAlgebra) domain relation)
    (heq : context ≤ domain =ᴮ weightedSet element weight)
    (hcover : (⨆ i, weight i) = context)
    (hccc : context ≤ countableChainConditionValue (V ScheduledIteration.finalAlgebra) domain relation)
    (hfamily : context ≤ family =ᴮ weightedSet denseSet familyWeight)
    (hactive : ∀ d, familyWeight d ≤ context)
    (hdense : ∀ d, familyWeight d ≤ denseValue (V ScheduledIteration.finalAlgebra) domain relation (denseSet d)) :
    context ≤ ⨆ filter : bSet ScheduledIteration.finalAlgebra,
      orderFilterValue (V ScheduledIteration.finalAlgebra) domain relation filter ⊓
        meetsFamilyValue (V ScheduledIteration.finalAlgebra) filter family := by
  let P := PresentedPosets.ofNames context domain relation element weight hvalid hseparate horder
  let dense : Labels → Labels → ScheduledIteration.finalAlgebra :=
    fun d i => weight i ⊓ (element i ∈ᴮ denseSet d)
  have hP : BooleanCountableChainCondition P :=
    ContextualCCC.ofNames_booleanCCC context domain relation element weight hvalid hseparate horder heq hccc
  have hDensity : ∀ d j, familyWeight d ⊓ P.member j ≤ ⨆ i, dense d i ⊓ P.leValue i j := by
    intro d j
    exact ContextualDensity.dense_coefficients (familyWeight d) domain relation (denseSet d)
      element weight (fun i => (hvalid i).2) ((hactive d).trans heq) (hdense d) j
  obtain ⟨value, hvalue, hValueCover, hValueUp, hValueDir, hValueMeets⟩ :=
    contextual_coefficients context P familyWeight dense hP hcover hactive (fun _ _ => inf_le_left) hDensity
  have hfilter : context ≤ orderFilterValue (V ScheduledIteration.finalAlgebra) domain relation
      (weightedSet element value) := by
    apply PresentedFilters.orderFilter_from_weights context domain relation element weight value heq
      (fun i => (hvalue i).trans (hvalid i).2) hValueCover
    · intro i j
      have hi : value i ⊓ weight j ⊓ edgeValue (V ScheduledIteration.finalAlgebra) relation
          (element i) (element j) ≤ value i := inf_le_left.trans inf_le_left
      exact (le_inf hi (le_inf (le_inf (hi.trans (hvalue i)) (inf_le_left.trans inf_le_right))
        inf_le_right)).trans (hValueUp i j)
    · intro i j
      exact (hValueDir i j).trans (iSup_mono fun k =>
        inf_le_inf le_rfl (inf_le_inf inf_le_right inf_le_right))
  have hmeets : context ≤ meetsFamilyValue (V ScheduledIteration.finalAlgebra) (weightedSet element value) family := by
    apply PresentedFilters.meetsFamily_from_weights context family element value denseSet familyWeight hfamily
    intro d
    exact inf_le_right.trans ((hValueMeets d).trans
      (iSup_mono fun i => inf_le_inf le_rfl inf_le_right))
  exact le_iSup_of_le (weightedSet element value) (le_inf hfilter hmeets)

end Erdos597Object.ContextualMartinModel
