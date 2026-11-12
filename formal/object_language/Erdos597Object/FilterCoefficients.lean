import Erdos597Object.BooleanFilterSemantics
import Erdos597Object.CodedMartinModel

set_option backward.isDefEq.respectTransparency false

/-! Extract coefficient witnesses from a filter in the coded Boolean-valued poset. -/

namespace Erdos597Object.FilterCoefficients

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanIteration BooleanSets BooleanPosetCoding BooleanFilterSemantics

variable {B I D : Type} [CompleteBooleanAlgebra B]

noncomputable def values (P : BooleanPoset B I) (filter : bSet B) (i : I) : B :=
  P.member i ⊓ (checkLabel i ∈ᴮ filter)

theorem filter_presentation_at (context : B) (P : BooleanPoset B I) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B) (domainName P checkLabel) (orderName P checkLabel) filter) :
    context ≤ filter =ᴮ weightedSet checkLabel (values P filter) :=
  PresentedSubsets.subset_presentation context (domainName P checkLabel) filter checkLabel P.member
    bSet.bv_refl (hfilter.trans inf_le_left)

theorem filter_presentation (P : BooleanPoset B I) (filter : bSet B)
    (hfilter : ⊤ ≤ orderFilterValue (V B) (domainName P checkLabel) (orderName P checkLabel) filter) :
    ⊤ ≤ filter =ᴮ weightedSet checkLabel (values P filter) :=
  filter_presentation_at ⊤ P filter hfilter

theorem values_cover_at (context : B) (P : BooleanPoset B I) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B) (domainName P checkLabel) (orderName P checkLabel) filter) :
    context ≤ ⨆ i, values P filter i := by
  have hnonempty := hfilter.trans (inf_le_right.trans inf_le_left)
  have h := (le_inf (filter_presentation_at context P filter hfilter) hnonempty).trans
    (PresentedPosets.nonempty_ext filter (weightedSet checkLabel (values P filter)))
  change context ≤ nonemptyValue (V B) (weightedSet checkLabel (values P filter)) at h
  rwa [PresentedPosets.weighted_nonempty] at h

theorem values_cover (P : BooleanPoset B I) (filter : bSet B)
    (hfilter : ⊤ ≤ orderFilterValue (V B) (domainName P checkLabel) (orderName P checkLabel) filter) :
    (⨆ i, values P filter i) = ⊤ := by
  exact top_unique (values_cover_at ⊤ P filter hfilter)

theorem values_upward (P : BooleanPoset B I) (filter : bSet B)
    (hfilter : ⊤ ≤ orderFilterValue (V B) (domainName P checkLabel) (orderName P checkLabel) filter)
    (i j : I) : values P filter i ⊓ P.leValue i j ≤ values P filter j := by
  let part := values P filter i ⊓ P.leValue i j
  have hj : part ≤ checkLabel j ∈ᴮ domainName P checkLabel := by
    rw [domainName_member P checkLabel (fun _ _ h => checkLabel_discrete h)]
    exact inf_le_right.trans ((P.le_members i j).trans inf_le_right)
  have hedge : part ≤ edgeValue (V B) (orderName P checkLabel) (checkLabel i) (checkLabel j) := by
    rw [orderName_edge P checkLabel (fun _ _ h => checkLabel_discrete h)]
    exact inf_le_right
  exact le_inf (inf_le_right.trans ((P.le_members i j).trans inf_le_right))
    (filter_upward _ _ _ _ _ (le_top.trans hfilter) (inf_le_left.trans inf_le_right) hj hedge)

theorem values_directed_at (context : B) (P : BooleanPoset B I) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B) (domainName P checkLabel) (orderName P checkLabel) filter)
    (i j : I) : context ⊓ (values P filter i ⊓ values P filter j) ≤
      ⨆ k, values P filter k ⊓ (P.leValue k i ⊓ P.leValue k j) := by
  have hcomp := filter_directed (context := context ⊓ (values P filter i ⊓ values P filter j))
    (domainName P checkLabel) (orderName P checkLabel) filter
    (checkLabel i) (checkLabel j) (inf_le_left.trans hfilter)
    (inf_le_right.trans (inf_le_left.trans inf_le_right))
    (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have h := (le_inf (inf_le_left.trans (filter_presentation_at context P filter hfilter)) hcomp).trans
    (PresentedCompatibility.compatibility_domain_ext (orderName P checkLabel)
      (checkLabel i) (checkLabel j) filter (weightedSet checkLabel (values P filter)))
  change context ⊓ (values P filter i ⊓ values P filter j) ≤ Erdos597Object.compatibleValue (V B)
    (weightedSet checkLabel (values P filter)) (orderName P checkLabel) (checkLabel i) (checkLabel j) at h
  rw [PresentedCompatibility.weighted_compatibility] at h
  simpa only [orderName_edge P checkLabel (fun _ _ h => checkLabel_discrete h)] using! h

theorem values_directed (P : BooleanPoset B I) (filter : bSet B)
    (hfilter : ⊤ ≤ orderFilterValue (V B) (domainName P checkLabel) (orderName P checkLabel) filter)
    (i j : I) : values P filter i ⊓ values P filter j ≤
      ⨆ k, values P filter k ⊓ (P.leValue k i ⊓ P.leValue k j) := by
  simpa only [top_inf_eq] using values_directed_at ⊤ P filter hfilter i j

theorem values_meet_family (P : BooleanPoset B I) (filter : bSet B) (dense : D → I → B)
    (hfilter : ⊤ ≤ orderFilterValue (V B) (domainName P checkLabel) (orderName P checkLabel) filter)
    (hmeets : ⊤ ≤ meetsFamilyValue (V B) filter
      (weightedSet (fun d => weightedSet checkLabel (dense d)) (fun _ => ⊤))) :
    ∀ d, (⨆ i, values P filter i ⊓ dense d i) = ⊤ := by
  unfold meetsFamilyValue at hmeets
  change ⊤ ≤ ⨅ d : bSet B, lattice.imp
    (d ∈ᴮ weightedSet (fun d => weightedSet checkLabel (dense d)) (fun _ => ⊤))
    (⨆ x : bSet B, (x ∈ᴮ filter) ⊓ (x ∈ᴮ d)) at hmeets
  rw [weighted_bounded_forall _ _ _
    (bSet.B_ext_iSup fun x => bSet.B_ext_inf (bSet.B_ext_const _) (bSet.B_ext_mem_right x))] at hmeets
  intro d
  have h := lattice.bv_context_apply (hmeets.trans (iInf_le _ d)) le_rfl
  have hext : bSet.B_ext (fun f : bSet B => ⨆ x : bSet B,
      (x ∈ᴮ f) ⊓ (x ∈ᴮ weightedSet checkLabel (dense d))) :=
    bSet.B_ext_iSup fun x => bSet.B_ext_inf (bSet.B_ext_mem_right x) (bSet.B_ext_const _)
  have hweight := (le_inf (filter_presentation P filter hfilter) h).trans
    (hext filter (weightedSet checkLabel (values P filter)))
  change ⊤ ≤ ⨆ x : bSet B, (x ∈ᴮ weightedSet checkLabel (values P filter)) ⊓
    (x ∈ᴮ weightedSet checkLabel (dense d)) at hweight
  rw [WeightedFilterModel.intersection_value] at hweight
  exact top_unique hweight

theorem final_coefficients
    (P : BooleanPoset ScheduledIteration.finalAlgebra ScheduledIteration.Labels)
    (dense : ScheduledIteration.Labels → ScheduledIteration.Labels → ScheduledIteration.finalAlgebra)
    (hccc : MartinTransport.CountableChainCondition (Condition P))
    (hcover : (⨆ i, P.member i) = ⊤)
    (hdense : ∀ d, ⊤ ≤ denseValue (V ScheduledIteration.finalAlgebra)
      (domainName P checkLabel) (orderName P checkLabel) (weightedSet checkLabel (dense d))) :
    ∃ weight : ScheduledIteration.Labels → ScheduledIteration.finalAlgebra,
      (∀ i, weight i ≤ P.member i) ∧
      (⨆ i, weight i) = ⊤ ∧
      (∀ i j, weight i ⊓ P.leValue i j ≤ weight j) ∧
      (∀ i j, weight i ⊓ weight j ≤ ⨆ k, weight k ⊓ (P.leValue k i ⊓ P.leValue k j)) ∧
      (∀ d, (⨆ i, weight i ⊓ dense d i) = ⊤) := by
  have hex := CodedMartinModel.final_coded_martin P dense hccc hcover hdense
  obtain ⟨filter, hfilter⟩ := bSet.exists_convert hex
    (bSet.B_ext_inf (orderFilter_ext _ _) (meetsFamily_ext _))
  have horder := hfilter.trans inf_le_left
  refine ⟨values P filter, fun _ => inf_le_left, values_cover P filter horder,
    values_upward P filter horder, values_directed P filter horder, ?_⟩
  exact values_meet_family P filter dense horder (hfilter.trans inf_le_right)

end Erdos597Object.FilterCoefficients
