import Erdos597Object.ContextualMartinModel

set_option backward.isDefEq.respectTransparency false

/-! The final model meets small families on small poset names under arbitrary Boolean contexts. -/

namespace Erdos597Object.SmallNameMartin

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections ScheduledIteration

theorem small_names_filter_exists (context : ScheduledIteration.finalAlgebra)
    (domain relation family : bSet ScheduledIteration.finalAlgebra)
    (label : Labels → bSet ScheduledIteration.finalAlgebra)
    (hlabel : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (hdomain : context ≤ injectsIntoValue (V ScheduledIteration.finalAlgebra) domain
      (weightedSet label (fun _ => ⊤)))
    (hfamily : context ≤ injectsIntoValue (V ScheduledIteration.finalAlgebra) family
      (weightedSet label (fun _ => ⊤)))
    (hnonempty : context ≤ nonemptyValue (V ScheduledIteration.finalAlgebra) domain)
    (horder : context ≤ partialOrderValue (V ScheduledIteration.finalAlgebra) domain relation)
    (hccc : context ≤ countableChainConditionValue (V ScheduledIteration.finalAlgebra) domain relation)
    (hdense : context ≤ ⨅ subset : bSet ScheduledIteration.finalAlgebra,
      lattice.imp (subset ∈ᴮ family) (denseValue (V ScheduledIteration.finalAlgebra) domain relation subset)) :
    context ≤ ⨆ filter : bSet ScheduledIteration.finalAlgebra,
      orderFilterValue (V ScheduledIteration.finalAlgebra) domain relation filter ⊓
        meetsFamilyValue (V ScheduledIteration.finalAlgebra) filter family := by
  obtain ⟨element, P, hcover, hvalid, hseparate, heq, _⟩ :=
    PresentedPosets.poset_presentation domain relation label hlabel hdomain horder hnonempty
  obtain ⟨denseSet, familyWeight, hfamilyValid, _, hfamilyEq⟩ :=
    presentation_of_injection family label hlabel hfamily
  apply ContextualMartinModel.presented_filter_exists context domain relation family element P.member
    denseSet familyWeight hvalid hseparate horder heq hcover hccc hfamilyEq
    (fun d => (hfamilyValid d).1)
  intro d
  have h := ((hfamilyValid d).1.trans hdense).trans (iInf_le _ (denseSet d))
  exact lattice.bv_context_apply h (hfamilyValid d).2

end Erdos597Object.SmallNameMartin
