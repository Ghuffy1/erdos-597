import Erdos597Object.SuccessorBridge
import Erdos597Object.BooleanCodeTransport

set_option backward.isDefEq.respectTransparency false

/-! The final algebra meets every fixed-label coded Martin requirement. -/

namespace Erdos597Object.CodedMartinModel

open Set Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open CanonicalIteration IterationSystems ScheduledIteration IterationPrefixes
open IterationNameTransport AlgebraTransport BooleanSets BooleanPosetCoding

set_option maxHeartbeats 1600000 in
theorem final_coded_martin
    (P : BooleanIteration.BooleanPoset ScheduledIteration.finalAlgebra Labels)
    (dense : Labels → Labels → ScheduledIteration.finalAlgebra)
    (hccc : MartinTransport.CountableChainCondition (BooleanIteration.Condition P))
    (hcover : (⨆ a, P.member a) = ⊤)
    (hdense : ∀ d, ⊤ ≤ denseValue (V ScheduledIteration.finalAlgebra)
      (domainName P checkLabel) (orderName P checkLabel) (weightedSet checkLabel (dense d))) :
    ⊤ ≤ ⨆ filter : bSet ScheduledIteration.finalAlgebra,
      orderFilterValue (V ScheduledIteration.finalAlgebra)
        (domainName P checkLabel) (orderName P checkLabel) filter ⊓
      meetsFamilyValue (V ScheduledIteration.finalAlgebra) filter
        (weightedSet (fun d => weightedSet checkLabel (dense d)) (fun _ => ⊤)) := by
  obtain ⟨i, Q, earlierDense, hQ, hEarlier⟩ :=
    CanonicalIteration.final_poset_family_captured ScheduledIteration.next
      labels_card.le labels_card.le P dense
  change mapPoset (ScheduledCoverage.finalEmbedding i) Q = P at hQ
  change ∀ d a, ScheduledCoverage.finalEmbedding i (earlierDense d a) = dense d a at hEarlier
  have hQccc : MartinTransport.CountableChainCondition
      (BooleanIteration.Condition (mapPoset (ScheduledCoverage.finalEmbedding i) Q)) :=
    Eq.mpr (congrArg (fun R : BooleanIteration.BooleanPoset ScheduledIteration.finalAlgebra Labels =>
      MartinTransport.CountableChainCondition
      (BooleanIteration.Condition R)) hQ) hccc
  have hQcover : (⨆ a, (mapPoset (ScheduledCoverage.finalEmbedding i) Q).member a) = ⊤ :=
    (congrArg (fun R : BooleanIteration.BooleanPoset ScheduledIteration.finalAlgebra Labels =>
      ⨆ a : Labels, R.member a) hQ).trans hcover
  obtain ⟨j, hij, hRccc, hRcover, _, hselected⟩ :=
    ScheduledCoverage.eventually_selected i ⊥ Q earlierDense hQccc hQcover
  let R := mapPoset (ScheduledIteration.system.map i j hij) Q
  let stageDense : Labels → Labels → ScheduledIteration.system.obj j :=
    fun d a => ScheduledIteration.system.map i j hij (earlierDense d a)
  let step : TransfiniteSystems.NextStep (ScheduledIteration.system.obj j) :=
    { Labels := Labels, forcing := R, ccc := hRccc, card_le := labels_card.le, cover := hRcover }
  have hstep : ScheduledIteration.next j (stagePrefix j) = step := hselected
  let f := SuccessorBridge.completionToFinal j step hstep
  have hf : f.comp (CompletionEmbedding.baseHom R) = ScheduledCoverage.finalEmbedding j :=
    SuccessorBridge.completionToFinal_base j step hstep
  have hRimage : mapPoset (ScheduledCoverage.finalEmbedding j) R = P :=
    (ScheduledCoverage.poset_final_image hij Q).trans hQ
  have hDenseImage (d a : Labels) :
      ScheduledCoverage.finalEmbedding j (stageDense d a) = dense d a :=
    (DFunLike.congr_fun (ScheduledCoverage.finalEmbedding_comp hij) (earlierDense d a)).trans
      (hEarlier d a)
  have hStageDense : ∀ d, ⊤ ≤ denseValue (V (ScheduledIteration.system.obj j))
      (domainName R checkLabel) (orderName R checkLabel) (weightedSet checkLabel (stageDense d)) := by
    intro d
    apply BooleanCodeTransport.reflect_dense_code (ScheduledCoverage.finalEmbedding j)
      (ScheduledCoverage.finalEmbedding_injective j) R (stageDense d)
    have hweights : (fun a => ScheduledCoverage.finalEmbedding j (stageDense d a)) = dense d :=
      funext (hDenseImage d)
    rw [hRimage, hweights]
    exact hdense d
  have hwitness := GenericFilterModel.generic_filter_meets_family R stageDense hStageDense
  have hmapped := OrderHomClass.monotone f hwitness
  rw [map_top, map_inf, BooleanForcingTransport.map_orderFilterValue,
    BooleanForcingTransport.map_meetsFamilyValue] at hmapped
  have hpos : mapPoset f (mapPoset (CompletionEmbedding.baseHom R) R) = P := by
    rw [mapPoset_comp, hf, hRimage]
  have hdomain : BooleanNameTransport.nameMap f
      (domainName (mapPoset (CompletionEmbedding.baseHom R) R) checkLabel) =
      domainName P checkLabel := by
    rw [BooleanCodeTransport.map_domain_check, hpos]
  have horder : BooleanNameTransport.nameMap f
      (orderName (mapPoset (CompletionEmbedding.baseHom R) R) checkLabel) =
      orderName P checkLabel := by
    rw [BooleanCodeTransport.map_order_check, hpos]
  have hfamily : BooleanNameTransport.nameMap f (GenericFilterModel.familyName R stageDense) =
      weightedSet (fun d => weightedSet checkLabel (dense d)) (fun _ => ⊤) := by
    unfold GenericFilterModel.familyName GenericFilterModel.denseName
    rw [BooleanCodeTransport.map_family_check]
    apply congrArg (fun family => weightedSet family (fun _ : Labels => ⊤))
    funext d
    apply congrArg (weightedSet checkLabel)
    funext a
    exact (DFunLike.congr_fun hf (stageDense d a)).trans (hDenseImage d a)
  rw [hdomain, horder, hfamily] at hmapped
  exact le_iSup_of_le (BooleanNameTransport.nameMap f (GenericFilterModel.filterName R)) hmapped

theorem final_coded_martin_of_value
    (P : BooleanIteration.BooleanPoset ScheduledIteration.finalAlgebra Labels)
    (dense : Labels → Labels → ScheduledIteration.finalAlgebra)
    (hccc : ⊤ ≤ countableChainConditionValue (V ScheduledIteration.finalAlgebra)
      (domainName P checkLabel) (orderName P checkLabel))
    (hcover : (⨆ a, P.member a) = ⊤)
    (hdense : ∀ d, ⊤ ≤ denseValue (V ScheduledIteration.finalAlgebra)
      (domainName P checkLabel) (orderName P checkLabel) (weightedSet checkLabel (dense d))) :
    ⊤ ≤ ⨆ filter : bSet ScheduledIteration.finalAlgebra,
      orderFilterValue (V ScheduledIteration.finalAlgebra)
        (domainName P checkLabel) (orderName P checkLabel) filter ⊓
      meetsFamilyValue (V ScheduledIteration.finalAlgebra) filter
        (weightedSet (fun d => weightedSet checkLabel (dense d)) (fun _ => ⊤)) :=
  final_coded_martin P dense
    (BooleanPosetCoding.two_step_ccc_checkLabels ScheduledIteration.finalAlgebra.ccc P hccc)
    hcover hdense

end Erdos597Object.CodedMartinModel
