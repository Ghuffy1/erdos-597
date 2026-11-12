import Erdos597Object.BooleanRamseyFiniteCover

set_option backward.isDefEq.respectTransparency false

/-! The coherent Boolean colour recorded on a finite subset of the selected set. -/

namespace Erdos597Object.BooleanRamseyRecorded

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanRamseyTree BooleanRamseyForcing BooleanRamseySelection
open BooleanRamseyHistories BooleanRamseyColorRules BooleanRamseyCoherence BooleanPosetCoding

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def recordedValue (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (filter : bSet B) (subset : Finset ℕ) : B :=
  ⨆ history : List Choice, if subset ⊆ points history ∧ recorded history subset = true then
    FilterCoefficients.values (forcing arity color initial) filter history else ⊥

theorem incompatible_recordings (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (left right : List Choice) (subset : Finset ℕ)
    (hleft : subset ⊆ points left) (hright : subset ⊆ points right)
    (hdifferent : recorded left subset ≠ recorded right subset) :
    context ⊓ (FilterCoefficients.values (forcing arity color initial) filter left ⊓
      FilterCoefficients.values (forcing arity color initial) filter right) ≤ ⊥ := by
  by_cases hzero : context ⊓
      (FilterCoefficients.values (forcing arity color initial) filter left ⊓
        FilterCoefficients.values (forcing arity color initial) filter right) = ⊥
  · exact hzero.le
  · have hleftBound : context ⊓
        (FilterCoefficients.values (forcing arity color initial) filter left ⊓
          FilterCoefficients.values (forcing arity color initial) filter right) ≤
        weight arity color initial left := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have hrightBound : context ⊓
        (FilterCoefficients.values (forcing arity color initial) filter left ⊓
          FilterCoefficients.values (forcing arity color initial) filter right) ≤
        weight arity color initial right := inf_le_right.trans (inf_le_right.trans inf_le_left)
    have hleftNonzero : weight arity color initial left ≠ ⊥ := by
      intro hz
      exact hzero (bot_unique (hleftBound.trans_eq hz))
    have hrightNonzero : weight arity color initial right ≠ ⊥ := by
      intro hz
      exact hzero (bot_unique (hrightBound.trans_eq hz))
    rcases comparable_of_nonzero context arity color initial filter hfilter left right hzero with h | h
    · exact False.elim (hdifferent (recorded_stable left right subset
        (weight_nonzero_increasing arity color initial right hrightNonzero) h hleft).symm)
    · exact False.elim (hdifferent (recorded_stable right left subset
        (weight_nonzero_increasing arity color initial left hleftNonzero) h hright))

theorem true_le_recorded (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (filter : bSet B) (history : List Choice) (subset : Finset ℕ)
    (hsubset : subset ⊆ points history) (htrue : recorded history subset = true) :
    FilterCoefficients.values (forcing arity color initial) filter history ≤
      recordedValue arity color initial filter subset := by
  apply le_iSup_of_le history
  simp only [hsubset, htrue, and_self, ↓reduceIte, le_refl]

theorem false_disjoint_recorded (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (history : List Choice) (subset : Finset ℕ)
    (hsubset : subset ⊆ points history) (hfalse : recorded history subset = false) :
    context ⊓ (FilterCoefficients.values (forcing arity color initial) filter history ⊓
      recordedValue arity color initial filter subset) ≤ ⊥ := by
  unfold recordedValue
  simp only [inf_iSup_eq]
  apply iSup_le
  intro other
  by_cases hother : subset ⊆ points other ∧ recorded other subset = true
  · simp only [hother]
    apply incompatible_recordings context arity color initial filter hfilter history other subset
      hsubset hother.1
    intro heq
    have hbad : false = true := hfalse.symm.trans (heq.trans hother.2)
    cases hbad
  · simp only [hother, ↓reduceIte, inf_bot_eq, le_refl]

end Erdos597Object.BooleanRamseyRecorded
