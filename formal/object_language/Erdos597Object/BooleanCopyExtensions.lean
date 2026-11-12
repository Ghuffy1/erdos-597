import Erdos597Object.BooleanInducedGraphs

set_option backward.isDefEq.respectTransparency false

/-! Transfer graph copies from an induced subdomain to a larger ordered host. -/

namespace Erdos597Object.BooleanCopyExtensions

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanFunctionBridge BooleanInducedGraphs BooleanOrientedSupport

variable {B : Type} [CompleteBooleanAlgebra B]

theorem function_enlarge (context : B) (source small large mapping : bSet B)
    (hsub : context ≤ small ⊆ᴮ large)
    (hfunction : context ≤ functionFromValue (V B) source small mapping) :
    context ≤ functionFromValue (V B) source large mapping := by
  rw [functionFrom_eq_is_function] at hfunction ⊢
  refine le_inf (le_inf (hfunction.trans (inf_le_left.trans inf_le_left)) ?_) ?_
  · apply le_iInf
    intro x
    apply lattice.bv_imp_intro
    have htotal := lattice.bv_context_apply
      ((inf_le_left.trans (hfunction.trans (inf_le_left.trans inf_le_right))).trans (iInf_le _ x))
      inf_le_right
    apply (le_inf le_rfl htotal).trans
    apply lattice.bv_cases_right
    intro y
    exact le_iSup_of_le y (le_inf
      (bSet.mem_of_mem_subset' (inf_le_left.trans (inf_le_left.trans hsub)) (inf_le_right.trans inf_le_left))
      (inf_le_right.trans inf_le_right))
  · exact BooleanUncountableRamsey.subset_trans (hfunction.trans inf_le_right) (bSet.prod_subset_right hsub)

theorem blueCopy_enlarge (context : B) (vertices small large edges blue : bSet B)
    (hsub : context ≤ small ⊆ᴮ large) :
    context ⊓ blueCopyValue (V B) vertices small edges (restrictGraph small blue) ≤
      blueCopyValue (V B) vertices large edges blue := by
  unfold blueCopyValue
  apply lattice.bv_cases_right
  intro mapping
  let part := context ⊓ (functionFromValue (V B) vertices small mapping ⊓
    (injectiveValue (V B) mapping ⊓ preservesRelationValue (V B) edges (restrictGraph small blue) mapping))
  apply le_iSup_of_le mapping
  refine le_inf (function_enlarge part vertices small large mapping
    (inf_le_left.trans hsub) (inf_le_right.trans inf_le_left)) ?_
  apply le_inf (inf_le_right.trans (inf_le_right.trans inf_le_left))
  exact (le_inf le_rfl (inf_le_right.trans (inf_le_right.trans inf_le_right))).trans
    (preservesRelation_mono_target part edges (restrictGraph small blue) blue mapping
      (le_top.trans (restricted_subset small blue)))

theorem redCopy_enlarge (context : B) (redDomain small large redOrder smallOrder largeOrder blue : bSet B)
    (hsub : context ≤ small ⊆ᴮ large)
    (horder : ∀ x y, context ⊓ ((x ∈ᴮ small) ⊓ (y ∈ᴮ small)) ≤
      lattice.biimp (edgeValue (V B) smallOrder x y) (edgeValue (V B) largeOrder x y)) :
    context ⊓ redCopyValue (V B) redDomain small redOrder smallOrder (restrictGraph small blue) ≤
      redCopyValue (V B) redDomain large redOrder largeOrder blue := by
  unfold redCopyValue
  apply lattice.bv_cases_right
  intro mapping
  let part := context ⊓ (functionFromValue (V B) redDomain small mapping ⊓
    (injectiveValue (V B) mapping ⊓
      (respectsOrderValue (V B) redOrder smallOrder mapping ⊓
        avoidsEdgesValue (V B) (restrictGraph small blue) mapping)))
  have hpart : part ≤ context := inf_le_left
  have hfunction : part ≤ functionFromValue (V B) redDomain small mapping :=
    inf_le_right.trans inf_le_left
  have hrespect : part ≤ respectsOrderValue (V B) redOrder smallOrder mapping :=
    inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have havoid : part ≤ avoidsEdgesValue (V B) (restrictGraph small blue) mapping :=
    inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have hmembers (x a : bSet B) {piece : B} (hp : piece ≤ part)
      (hm : piece ≤ edgeValue (V B) mapping x a) : piece ≤ a ∈ᴮ small := by
    have hf : piece ≤ bSet.is_function redDomain small mapping := by
      rw [← functionFrom_eq_is_function]
      exact hp.trans hfunction
    exact bSet.mem_codomain_of_is_function hm hf
  apply le_iSup_of_le mapping
  refine le_inf (function_enlarge part redDomain small large mapping (hpart.trans hsub) hfunction) ?_
  apply le_inf (inf_le_right.trans (inf_le_right.trans inf_le_left))
  apply le_inf
  · apply le_iInf
    intro x
    apply le_iInf
    intro y
    apply le_iInf
    intro a
    apply le_iInf
    intro b
    apply lattice.bv_imp_intro
    let piece := part ⊓ (edgeValue (V B) mapping x a ⊓ edgeValue (V B) mapping y b)
    have ha : piece ≤ a ∈ᴮ small := hmembers x a inf_le_left (inf_le_right.trans inf_le_left)
    have hb : piece ≤ b ∈ᴮ small := hmembers y b inf_le_left (inf_le_right.trans inf_le_right)
    have hsame : piece ≤ lattice.biimp (edgeValue (V B) smallOrder a b)
        (edgeValue (V B) largeOrder a b) :=
      (le_inf (inf_le_left.trans hpart) (le_inf ha hb)).trans (horder a b)
    have hprevious := lattice.bv_context_apply
      ((inf_le_left.trans hrespect).trans ((iInf_le _ x).trans ((iInf_le _ y).trans
        ((iInf_le _ a).trans (iInf_le _ b))))) inf_le_right
    apply le_inf
    · apply lattice.bv_imp_intro
      have hsmall := lattice.bv_context_apply (inf_le_left.trans (hprevious.trans inf_le_left)) inf_le_right
      exact lattice.bv_context_apply (inf_le_left.trans (hsame.trans inf_le_left)) hsmall
    · apply lattice.bv_imp_intro
      have hsmall := lattice.bv_context_apply (inf_le_left.trans (hsame.trans inf_le_right)) inf_le_right
      exact lattice.bv_context_apply (inf_le_left.trans (hprevious.trans inf_le_right)) hsmall
  · apply le_iInf
    intro x
    apply le_iInf
    intro y
    apply le_iInf
    intro a
    apply le_iInf
    intro b
    apply lattice.bv_imp_intro
    let piece := part ⊓ (edgeValue (V B) mapping x a ⊓ edgeValue (V B) mapping y b)
    have ha : piece ≤ a ∈ᴮ small := hmembers x a inf_le_left (inf_le_right.trans inf_le_left)
    have hb : piece ≤ b ∈ᴮ small := hmembers y b inf_le_left (inf_le_right.trans inf_le_right)
    have hprevious := lattice.bv_context_apply
      ((inf_le_left.trans havoid).trans ((iInf_le _ x).trans ((iInf_le _ y).trans
        ((iInf_le _ a).trans (iInf_le _ b))))) inf_le_right
    apply (le_inf le_rfl hprevious).trans
    apply lattice.bv_or_elim_right
    · exact inf_le_right.trans le_sup_left
    · apply le_sup_of_le_right
      apply (le_compl_iff_disjoint_right).mpr
      apply disjoint_iff.mpr
      let cut := (piece ⊓ (edgeValue (V B) (restrictGraph small blue) a b)ᶜ) ⊓
        edgeValue (V B) blue a b
      have hrestricted : cut ≤ edgeValue (V B) (restrictGraph small blue) a b := by
        rw [restricted_edge]
        exact le_inf inf_le_right (le_inf
          ((inf_le_left.trans inf_le_left).trans ha) ((inf_le_left.trans inf_le_left).trans hb))
      exact bot_unique ((le_inf hrestricted (inf_le_left.trans inf_le_right)).trans_eq inf_compl_eq_bot)

end Erdos597Object.BooleanCopyExtensions
