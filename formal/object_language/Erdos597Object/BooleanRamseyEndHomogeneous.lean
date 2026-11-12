import Erdos597Object.BooleanRamseyRecorded

set_option backward.isDefEq.respectTransparency false

/-! On the selected infinite set, a colour depends only on the earlier points. -/

namespace Erdos597Object.BooleanRamseyEndHomogeneous

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanRamseyTree BooleanRamseyForcing BooleanRamseySelection
open BooleanRamseyHistories BooleanRamseyColorRules BooleanRamseyFiniteCover
open BooleanRamseyRecorded BooleanPosetCoding

variable {B : Type} [CompleteBooleanAlgebra B]

theorem cover_true (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (hpositive : 0 < arity) (subset : Finset ℕ) (n : ℕ)
    (hcard : subset.card = arity) (hbefore : ∀ x ∈ subset, x < n) :
    context ⊓ (coverValue arity color initial filter (insert n subset) ⊓
      recordedValue arity color initial filter subset) ≤ color (insert n subset) := by
  unfold coverValue
  simp only [iSup_inf_eq, inf_iSup_eq]
  apply iSup_le
  intro history
  by_cases hcover : insert n subset ⊆ points history
  · simp only [hcover, ↓reduceIte]
    have hsubset : subset ⊆ points history := (Finset.subset_insert n subset).trans hcover
    have hn : n ∈ points history := hcover (Finset.mem_insert_self n subset)
    have hdecision := history_decision arity color initial hpositive history subset n hcard hsubset hn hbefore
    cases hrecorded : recorded history subset with
    | false =>
      exact (false_disjoint_recorded context arity color initial filter hfilter
        history subset hsubset hrecorded).trans bot_le
    | true =>
      simp only [hrecorded, ↓reduceIte] at hdecision
      exact inf_le_right.trans (inf_le_left.trans (inf_le_left.trans hdecision))
  · simp only [hcover, ↓reduceIte, bot_inf_eq, inf_bot_eq, bot_le]

theorem cover_false (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hpositive : 0 < arity) (subset : Finset ℕ) (n : ℕ)
    (hcard : subset.card = arity) (hbefore : ∀ x ∈ subset, x < n) :
    context ⊓ (coverValue arity color initial filter (insert n subset) ⊓
      (recordedValue arity color initial filter subset)ᶜ) ≤ (color (insert n subset))ᶜ := by
  unfold coverValue
  simp only [iSup_inf_eq, inf_iSup_eq]
  apply iSup_le
  intro history
  by_cases hcover : insert n subset ⊆ points history
  · simp only [hcover, ↓reduceIte]
    have hsubset : subset ⊆ points history := (Finset.subset_insert n subset).trans hcover
    have hn : n ∈ points history := hcover (Finset.mem_insert_self n subset)
    have hdecision := history_decision arity color initial hpositive history subset n hcard hsubset hn hbefore
    cases hrecorded : recorded history subset with
    | false =>
      simp only [hrecorded] at hdecision
      exact inf_le_right.trans (inf_le_left.trans (inf_le_left.trans hdecision))
    | true =>
      have hvalue := true_le_recorded arity color initial filter history subset hsubset hrecorded
      have hbot := (inf_le_inf hvalue (le_refl
        ((recordedValue arity color initial filter subset)ᶜ))).trans_eq inf_compl_eq_bot
      exact (inf_le_right.trans hbot).trans bot_le
  · simp only [hcover, ↓reduceIte, bot_inf_eq, inf_bot_eq, bot_le]

theorem selected_true (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (hpositive : 0 < arity) (subset : Finset ℕ) (n : ℕ)
    (hcard : subset.card = arity) (hbefore : ∀ x ∈ subset, x < n) :
    context ⊓ ((insert n subset).inf (selectedWeight arity color initial filter) ⊓
      recordedValue arity color initial filter subset) ≤ color (insert n subset) := by
  apply (le_inf inf_le_left (le_inf ?_ (inf_le_right.trans inf_le_right))).trans
    (cover_true context arity color initial filter hfilter hpositive subset n hcard hbefore)
  exact (le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans
    (finite_selected_cover context arity color initial filter hfilter (insert n subset))

theorem selected_false (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (hpositive : 0 < arity) (subset : Finset ℕ) (n : ℕ)
    (hcard : subset.card = arity) (hbefore : ∀ x ∈ subset, x < n) :
    context ⊓ ((insert n subset).inf (selectedWeight arity color initial filter) ⊓
      (recordedValue arity color initial filter subset)ᶜ) ≤ (color (insert n subset))ᶜ := by
  apply (le_inf inf_le_left (le_inf ?_ (inf_le_right.trans inf_le_right))).trans
    (cover_false context arity color initial filter hpositive subset n hcard hbefore)
  exact (le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans
    (finite_selected_cover context arity color initial filter hfilter (insert n subset))

end Erdos597Object.BooleanRamseyEndHomogeneous
