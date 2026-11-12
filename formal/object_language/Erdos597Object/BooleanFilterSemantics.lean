import Erdos597Object.PresentedSubsets

set_option backward.isDefEq.respectTransparency false

/-! Extensionality and pointwise consequences of the first-order filter predicates. -/

namespace Erdos597Object.BooleanFilterSemantics

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets PresentedPosets

variable {B : Type} [CompleteBooleanAlgebra B]

theorem orderFilter_ext (domain relation : bSet B) :
    bSet.B_ext (fun filter => orderFilterValue (V B) domain relation filter) := by
  simp only [orderFilterValue, subsetValue, nonemptyValue, memberValue_bSet, sup_assoc]
  apply bSet.B_ext_inf
  · exact bSet.B_ext_iInf fun x =>
      bSet.B_ext_sup (bSet.B_ext_compl (bSet.B_ext_mem_right x)) (bSet.B_ext_const _)
  · apply bSet.B_ext_inf
    · exact bSet.B_ext_iSup fun x => bSet.B_ext_mem_right x
    · apply bSet.B_ext_inf
      · exact bSet.B_ext_iInf fun x =>
          bSet.B_ext_sup (bSet.B_ext_compl (bSet.B_ext_mem_right x))
            (bSet.B_ext_iInf fun y => bSet.B_ext_sup (bSet.B_ext_const _)
              (bSet.B_ext_sup (bSet.B_ext_const _) (bSet.B_ext_mem_right y)))
      · exact bSet.B_ext_iInf fun x =>
          bSet.B_ext_sup (bSet.B_ext_compl (bSet.B_ext_mem_right x))
            (bSet.B_ext_iInf fun y =>
              bSet.B_ext_sup (bSet.B_ext_compl (bSet.B_ext_mem_right y))
                (bSet.B_ext_iSup fun z =>
                  bSet.B_ext_inf (bSet.B_ext_mem_right z) (bSet.B_ext_const _)))

theorem meetsFamily_ext (family : bSet B) :
    bSet.B_ext (fun filter => meetsFamilyValue (V B) filter family) := by
  unfold meetsFamilyValue
  exact bSet.B_ext_iInf fun d => bSet.B_ext_sup (bSet.B_ext_const _)
    (bSet.B_ext_iSup fun x => bSet.B_ext_inf (bSet.B_ext_mem_right x) (bSet.B_ext_const _))

theorem filter_upward {context : B} (domain relation filter x y : bSet B)
    (hfilter : context ≤ orderFilterValue (V B) domain relation filter)
    (hx : context ≤ x ∈ᴮ filter) (hy : context ≤ y ∈ᴮ domain)
    (hxy : context ≤ edgeValue (V B) relation x y) : context ≤ y ∈ᴮ filter := by
  simp only [orderFilterValue, memberValue_bSet, sup_assoc] at hfilter
  have hup := hfilter.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have hxImp := lattice.bv_context_apply (hup.trans (iInf_le _ x)) hx
  have hyImp := lattice.bv_context_apply (hxImp.trans (iInf_le _ y)) hy
  exact lattice.bv_context_apply hyImp hxy

theorem filter_directed {context : B} (domain relation filter x y : bSet B)
    (hfilter : context ≤ orderFilterValue (V B) domain relation filter)
    (hx : context ≤ x ∈ᴮ filter) (hy : context ≤ y ∈ᴮ filter) :
    context ≤ Erdos597Object.compatibleValue (V B) filter relation x y := by
  simp only [orderFilterValue, memberValue_bSet, sup_assoc] at hfilter
  have hdir := hfilter.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have hxImp := lattice.bv_context_apply (hdir.trans (iInf_le _ x)) hx
  exact lattice.bv_context_apply (hxImp.trans (iInf_le _ y)) hy

end Erdos597Object.BooleanFilterSemantics
