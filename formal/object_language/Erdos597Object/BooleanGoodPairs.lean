import Erdos597Object.BooleanRectangles

set_option backward.isDefEq.respectTransparency false

/-! Good and bad pairs of uncountable set names, with actual refinement witnesses. -/

namespace Erdos597Object.BooleanGoodPairs

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanRectangles

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def forLargeSubsets (property : bSet B → bSet B → B) (left right : bSet B) : B :=
  ⨅ smallLeft : bSet B, lattice.imp (largeSubset left smallLeft)
    (⨅ smallRight : bSet B, lattice.imp (largeSubset right smallRight) (property smallLeft smallRight))

noncomputable def emptySubrectangle (relation left right : bSet B) : B :=
  ⨆ smallLeft : bSet B, largeSubset left smallLeft ⊓
    ⨆ smallRight : bSet B, largeSubset right smallRight ⊓ emptyRectangle relation smallLeft smallRight

noncomputable def goodPair (relation left right : bSet B) : B :=
  forLargeSubsets (emptySubrectangle relation) left right

noncomputable def badPair (relation left right : bSet B) : B :=
  forLargeSubsets (rectangleEdge relation) left right

theorem forLargeSubsets_left_ext (property : bSet B → bSet B → B) (right : bSet B) :
    bSet.B_ext (fun left => forLargeSubsets property left right) :=
  bSet.B_ext_iInf fun smallLeft => bSet.B_ext_imp (largeSubset_domain_ext smallLeft) (bSet.B_ext_const _)

theorem forLargeSubsets_right_ext (property : bSet B → bSet B → B) (left : bSet B) :
    bSet.B_ext (fun right => forLargeSubsets property left right) :=
  bSet.B_ext_iInf fun _ => bSet.B_ext_imp (bSet.B_ext_const _)
    (bSet.B_ext_iInf fun smallRight => bSet.B_ext_imp (largeSubset_domain_ext smallRight) (bSet.B_ext_const _))

theorem forLargeSubsets_restrict (context : B) (property : bSet B → bSet B → B)
    (left right smallLeft smallRight : bSet B)
    (hleft : context ≤ smallLeft ⊆ᴮ left) (hright : context ≤ smallRight ⊆ᴮ right)
    (hproperty : context ≤ forLargeSubsets property left right) :
    context ≤ forLargeSubsets property smallLeft smallRight := by
  apply le_iInf
  intro testLeft
  apply lattice.bv_imp_intro
  have hlargeLeft : context ⊓ largeSubset smallLeft testLeft ≤ largeSubset left testLeft :=
    largeSubset_mono context smallLeft left testLeft hleft
  have hrightProperty := lattice.bv_context_apply
    ((inf_le_left.trans hproperty).trans (iInf_le _ testLeft)) hlargeLeft
  apply le_iInf
  intro testRight
  apply lattice.bv_imp_intro
  have hlargeRight : (context ⊓ largeSubset smallLeft testLeft) ⊓ largeSubset smallRight testRight ≤
      largeSubset right testRight :=
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans
      (largeSubset_mono context smallRight right testRight hright)
  exact lattice.bv_context_apply ((inf_le_left.trans hrightProperty).trans (iInf_le _ testRight)) hlargeRight

theorem goodPair_left_ext (relation right : bSet B) :
    bSet.B_ext (fun left => goodPair relation left right) :=
  forLargeSubsets_left_ext (emptySubrectangle relation) right

theorem goodPair_right_ext (relation left : bSet B) :
    bSet.B_ext (fun right => goodPair relation left right) :=
  forLargeSubsets_right_ext (emptySubrectangle relation) left

theorem badPair_left_ext (relation right : bSet B) :
    bSet.B_ext (fun left => badPair relation left right) :=
  forLargeSubsets_left_ext (rectangleEdge relation) right

theorem badPair_right_ext (relation left : bSet B) :
    bSet.B_ext (fun right => badPair relation left right) :=
  forLargeSubsets_right_ext (rectangleEdge relation) left

theorem goodPair_restrict (context : B) (relation left right smallLeft smallRight : bSet B)
    (hleft : context ≤ smallLeft ⊆ᴮ left) (hright : context ≤ smallRight ⊆ᴮ right)
    (hgood : context ≤ goodPair relation left right) :
    context ≤ goodPair relation smallLeft smallRight :=
  forLargeSubsets_restrict context (emptySubrectangle relation) left right smallLeft smallRight hleft hright hgood

theorem badPair_restrict (context : B) (relation left right smallLeft smallRight : bSet B)
    (hleft : context ≤ smallLeft ⊆ᴮ left) (hright : context ≤ smallRight ⊆ᴮ right)
    (hbad : context ≤ badPair relation left right) :
    context ≤ badPair relation smallLeft smallRight :=
  forLargeSubsets_restrict context (rectangleEdge relation) left right smallLeft smallRight hleft hright hbad

theorem emptySubrectangle_left_ext (relation right : bSet B) :
    bSet.B_ext (fun left => emptySubrectangle relation left right) :=
  bSet.B_ext_iSup fun smallLeft => bSet.B_ext_inf (largeSubset_domain_ext smallLeft) (bSet.B_ext_const _)

theorem emptySubrectangle_right_ext (relation left : bSet B) :
    bSet.B_ext (fun right => emptySubrectangle relation left right) :=
  bSet.B_ext_iSup fun _ => bSet.B_ext_inf (bSet.B_ext_const _)
    (bSet.B_ext_iSup fun smallRight => bSet.B_ext_inf (largeSubset_domain_ext smallRight) (bSet.B_ext_const _))

theorem emptySubrectangle_witness (context : B) (relation left right : bSet B)
    (h : context ≤ emptySubrectangle relation left right) :
    ∃ smallLeft smallRight : bSet B, context ≤ largeSubset left smallLeft ∧
      context ≤ largeSubset right smallRight ∧ context ≤ emptyRectangle relation smallLeft smallRight := by
  obtain ⟨smallLeft, hleft⟩ := bSet.exists_convert h
    (bSet.B_ext_inf (largeSubset_ext left)
      (bSet.B_ext_iSup fun smallRight => bSet.B_ext_inf (bSet.B_ext_const _)
        (emptyRectangle_left_ext relation smallRight)))
  obtain ⟨smallRight, hright⟩ := bSet.exists_convert (hleft.trans inf_le_right)
    (bSet.B_ext_inf (largeSubset_ext right) (emptyRectangle_right_ext relation smallLeft))
  exact ⟨smallLeft, smallRight, hleft.trans inf_le_left, hright.trans inf_le_left, hright.trans inf_le_right⟩

theorem badPair_eq_compl (relation left right : bSet B) :
    badPair relation left right = (emptySubrectangle relation left right)ᶜ := by
  simp only [badPair, forLargeSubsets, emptySubrectangle, emptyRectangle,
    lattice.imp, compl_iSup, compl_inf, compl_compl]

theorem goodPair_compl (relation left right : bSet B) :
    (goodPair relation left right)ᶜ =
      ⨆ smallLeft : bSet B, largeSubset left smallLeft ⊓
        ⨆ smallRight : bSet B, largeSubset right smallRight ⊓ badPair relation smallLeft smallRight := by
  simp only [goodPair, forLargeSubsets, lattice.imp, compl_iInf, compl_sup, compl_compl, badPair_eq_compl]

theorem not_goodPair_witness (context : B) (relation left right : bSet B)
    (h : context ≤ (goodPair relation left right)ᶜ) :
    ∃ smallLeft smallRight : bSet B, context ≤ largeSubset left smallLeft ∧
      context ≤ largeSubset right smallRight ∧ context ≤ badPair relation smallLeft smallRight := by
  rw [goodPair_compl] at h
  obtain ⟨smallLeft, hleft⟩ := bSet.exists_convert h
    (bSet.B_ext_inf (largeSubset_ext left)
      (bSet.B_ext_iSup fun smallRight => bSet.B_ext_inf (bSet.B_ext_const _)
        (badPair_left_ext relation smallRight)))
  obtain ⟨smallRight, hright⟩ := bSet.exists_convert (hleft.trans inf_le_right)
    (bSet.B_ext_inf (largeSubset_ext right) (badPair_right_ext relation smallLeft))
  exact ⟨smallLeft, smallRight, hleft.trans inf_le_left, hright.trans inf_le_left, hright.trans inf_le_right⟩

theorem goodPair_refine (context : B) (relation left right testLeft testRight : bSet B)
    (hgood : context ≤ goodPair relation left right)
    (hleft : context ≤ largeSubset left testLeft) (hright : context ≤ largeSubset right testRight) :
    ∃ smallLeft smallRight : bSet B, context ≤ largeSubset testLeft smallLeft ∧
      context ≤ largeSubset testRight smallRight ∧ context ≤ emptyRectangle relation smallLeft smallRight := by
  have htestLeft := lattice.bv_context_apply (hgood.trans (iInf_le _ testLeft)) hleft
  exact emptySubrectangle_witness context relation testLeft testRight
    (lattice.bv_context_apply (htestLeft.trans (iInf_le _ testRight)) hright)

theorem badPair_edge (context : B) (relation left right testLeft testRight : bSet B)
    (hbad : context ≤ badPair relation left right)
    (hleft : context ≤ largeSubset left testLeft) (hright : context ≤ largeSubset right testRight) :
    ∃ x y : bSet B, context ≤ x ∈ᴮ testLeft ∧ context ≤ y ∈ᴮ testRight ∧
      context ≤ edgeValue (V B) relation x y := by
  have htestLeft := lattice.bv_context_apply (hbad.trans (iInf_le _ testLeft)) hleft
  exact rectangleEdge_witness context relation testLeft testRight
    (lattice.bv_context_apply (htestLeft.trans (iInf_le _ testRight)) hright)

end Erdos597Object.BooleanGoodPairs
