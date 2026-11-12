import Erdos597Object.BooleanGoodPairs

set_option backward.isDefEq.respectTransparency false

/-! Simultaneous good-or-bad decisions for finitely many uncountable rows. -/

namespace Erdos597Object.BooleanPairDecisions

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanRectangles BooleanGoodPairs

variable {B I : Type} [CompleteBooleanAlgebra B]

noncomputable def pairDecision (relation left right : bSet B) : B :=
  ⨆ smallLeft : bSet B, largeSubset left smallLeft ⊓
    (goodPair relation left right ⊔ badPair relation smallLeft right)

noncomputable def decisions (relation left : I → bSet B) (right : bSet B) (indices : Finset I) : B :=
  indices.inf (fun i => pairDecision (relation i) (left i) right)

theorem pairDecision_right_ext (relation left : bSet B) :
    bSet.B_ext (fun right => pairDecision relation left right) :=
  bSet.B_ext_iSup fun smallLeft => bSet.B_ext_inf (bSet.B_ext_const _)
    (bSet.B_ext_sup (goodPair_right_ext relation left) (badPair_right_ext relation smallLeft))

theorem pairDecision_witness (context : B) (relation left right : bSet B)
    (h : context ≤ pairDecision relation left right) :
    ∃ smallLeft : bSet B, context ≤ largeSubset left smallLeft ∧
      context ≤ goodPair relation left right ⊔ badPair relation smallLeft right := by
  obtain ⟨smallLeft, hleft⟩ := bSet.exists_convert h
    (bSet.B_ext_inf (largeSubset_ext left)
      (bSet.B_ext_sup (bSet.B_ext_const _) (badPair_left_ext relation right)))
  exact ⟨smallLeft, hleft.trans inf_le_left, hleft.trans inf_le_right⟩

theorem pairDecision_restrict (context : B) (relation left right smallRight : bSet B)
    (hsubset : context ≤ smallRight ⊆ᴮ right)
    (hdecision : context ≤ pairDecision relation left right) :
    context ≤ pairDecision relation left smallRight := by
  apply (le_inf le_rfl hdecision).trans
  change context ⊓ (⨆ smallLeft : bSet B, largeSubset left smallLeft ⊓
    (goodPair relation left right ⊔ badPair relation smallLeft right)) ≤ _
  rw [inf_iSup_eq]
  apply iSup_le
  intro smallLeft
  apply le_iSup_of_le smallLeft
  apply le_inf (inf_le_right.trans inf_le_left)
  apply lattice.context_or_elim' (inf_le_right.trans inf_le_right)
  · intro part hpart hgood
    exact (goodPair_restrict part relation left right left smallRight bSet.subset_self
      ((hpart.trans inf_le_left).trans hsubset) hgood).trans le_sup_left
  · intro part hpart hbad
    exact (badPair_restrict part relation smallLeft right smallLeft smallRight bSet.subset_self
      ((hpart.trans inf_le_left).trans hsubset) hbad).trans le_sup_right

theorem decisions_ext (relation left : I → bSet B) (indices : Finset I) :
    bSet.B_ext (fun right => decisions relation left right indices) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    simpa only [decisions, Finset.inf_empty] using bSet.B_ext_const (⊤ : B)
  | insert i indices hi ih =>
    simpa only [decisions, Finset.inf_insert] using
      bSet.B_ext_inf (pairDecision_right_ext (relation i) (left i)) ih

theorem decisions_restrict (context : B) (relation left : I → bSet B) (indices : Finset I)
    (right smallRight : bSet B) (hsubset : context ≤ smallRight ⊆ᴮ right)
    (hdecisions : context ≤ decisions relation left right indices) :
    context ≤ decisions relation left smallRight indices := by
  apply Finset.le_inf
  intro i hi
  exact pairDecision_restrict context (relation i) (left i) right smallRight hsubset
    (hdecisions.trans (Finset.inf_le hi))

theorem finite_decisions (relation left : I → bSet B) (indices : Finset I) :
    ∀ (context : B) (right : bSet B),
      (∀ i ∈ indices, context ≤ (injectsIntoValue (V B) (left i) bSet.omega)ᶜ) →
      context ≤ (injectsIntoValue (V B) right bSet.omega)ᶜ →
      ∃ smallRight : bSet B, context ≤ largeSubset right smallRight ∧
        context ≤ decisions relation left smallRight indices := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    intro context right _ hright
    exact ⟨right, largeSubset_refl context right hright, le_top⟩
  | @insert i indices hi ih =>
    intro context right hleft hright
    have hcovered : context ≤ ⨆ smallRight : bSet B,
        largeSubset right smallRight ⊓ decisions relation left smallRight (insert i indices) := by
      apply lattice.context_or_elim' (a := goodPair (relation i) (left i) right)
        (b := (goodPair (relation i) (left i) right)ᶜ)
        (by rw [sup_compl_eq_top]; exact le_top)
      · intro part hpart hgood
        obtain ⟨smallRight, hsmall, hrest⟩ := ih part right
          (fun j hj => hpart.trans (hleft j (Finset.mem_insert_of_mem hj))) (hpart.trans hright)
        apply le_iSup_of_le smallRight
        apply le_inf hsmall
        change part ≤ (insert i indices).inf (fun j => pairDecision (relation j) (left j) smallRight)
        rw [Finset.inf_insert]
        apply le_inf ?_ hrest
        apply le_iSup_of_le (left i)
        apply le_inf (largeSubset_refl part (left i)
          (hpart.trans (hleft i (Finset.mem_insert_self i indices))))
        exact (goodPair_restrict part (relation i) (left i) right (left i) smallRight
          bSet.subset_self (hsmall.trans inf_le_left) hgood).trans le_sup_left
      · intro part hpart hnotGood
        obtain ⟨smallLeft, middleRight, hsmallLeft, hmiddle, hbad⟩ :=
          not_goodPair_witness part (relation i) (left i) right hnotGood
        obtain ⟨smallRight, hsmall, hrest⟩ := ih part middleRight
          (fun j hj => hpart.trans (hleft j (Finset.mem_insert_of_mem hj)))
          (hmiddle.trans inf_le_right)
        apply le_iSup_of_le smallRight
        apply le_inf (largeSubset_trans part right middleRight smallRight hmiddle hsmall)
        change part ≤ (insert i indices).inf (fun j => pairDecision (relation j) (left j) smallRight)
        rw [Finset.inf_insert]
        apply le_inf ?_ hrest
        apply le_iSup_of_le smallLeft
        apply le_inf hsmallLeft
        exact (badPair_restrict part (relation i) smallLeft middleRight smallLeft smallRight
          bSet.subset_self (hsmall.trans inf_le_left) hbad).trans le_sup_right
    obtain ⟨smallRight, hsmallRight⟩ := bSet.exists_convert hcovered
      (bSet.B_ext_inf (largeSubset_ext right) (decisions_ext relation left (insert i indices)))
    exact ⟨smallRight, hsmallRight.trans inf_le_left, hsmallRight.trans inf_le_right⟩

theorem finite_decision_witnesses (context : B) (relation left : I → bSet B) (indices : Finset I)
    (right : bSet B)
    (hleft : ∀ i ∈ indices, context ≤ (injectsIntoValue (V B) (left i) bSet.omega)ᶜ)
    (hright : context ≤ (injectsIntoValue (V B) right bSet.omega)ᶜ) :
    ∃ smallRight : bSet B, context ≤ largeSubset right smallRight ∧
      ∀ i ∈ indices, ∃ smallLeft : bSet B, context ≤ largeSubset (left i) smallLeft ∧
        context ≤ goodPair (relation i) (left i) smallRight ⊔ badPair (relation i) smallLeft smallRight := by
  obtain ⟨smallRight, hsmall, hdecisions⟩ := finite_decisions relation left indices context right hleft hright
  exact ⟨smallRight, hsmall, fun i hi => pairDecision_witness context (relation i) (left i) smallRight
    (hdecisions.trans (Finset.inf_le hi))⟩

theorem all_finite_decisions [Fintype I] (context : B) (relation left : I → bSet B) (right : bSet B)
    (hleft : ∀ i, context ≤ (injectsIntoValue (V B) (left i) bSet.omega)ᶜ)
    (hright : context ≤ (injectsIntoValue (V B) right bSet.omega)ᶜ) :
    ∃ smallRight : bSet B, context ≤ largeSubset right smallRight ∧
      ∀ i, ∃ smallLeft : bSet B, context ≤ largeSubset (left i) smallLeft ∧
        context ≤ goodPair (relation i) (left i) smallRight ⊔ badPair (relation i) smallLeft smallRight := by
  obtain ⟨smallRight, hsmall, hwitness⟩ := finite_decision_witnesses context relation left Finset.univ right
    (fun i _ => hleft i) hright
  exact ⟨smallRight, hsmall, fun i => hwitness i (Finset.mem_univ i)⟩

end Erdos597Object.BooleanPairDecisions
