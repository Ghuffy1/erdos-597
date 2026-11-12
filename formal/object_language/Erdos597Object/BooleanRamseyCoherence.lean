import Erdos597Object.BooleanRamseySelection
import Erdos597Object.FilterCoefficients

set_option backward.isDefEq.respectTransparency false

/-! Coherence of the finite histories selected by the Ramsey forcing filter. -/

namespace Erdos597Object.BooleanRamseyCoherence

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanRamseyTree BooleanRamseyForcing BooleanPosetCoding

variable {B : Type} [CompleteBooleanAlgebra B]

theorem incompatible_weights (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (left right : List Choice) (hleft : ¬ left.IsPrefix right) (hright : ¬ right.IsPrefix left) :
    context ⊓ (FilterCoefficients.values (forcing arity color initial) filter left ⊓
      FilterCoefficients.values (forcing arity color initial) filter right) ≤ ⊥ := by
  apply (FilterCoefficients.values_directed_at context (forcing arity color initial) filter hfilter left right).trans
  apply iSup_le
  intro history
  change FilterCoefficients.values (forcing arity color initial) filter history ⊓
    ((if left.IsPrefix history then weight arity color initial history else ⊥) ⊓
      (if right.IsPrefix history then weight arity color initial history else ⊥)) ≤ ⊥
  by_cases hl : left.IsPrefix history
  · by_cases hr : right.IsPrefix history
    · rcases List.prefix_or_prefix_of_prefix hl hr with h | h
      · exact False.elim (hleft h)
      · exact False.elim (hright h)
    · simp only [hl, hr, ↓reduceIte, inf_bot_eq, le_refl]
  · simp only [hl, ↓reduceIte, bot_inf_eq, inf_bot_eq, le_refl]

theorem comparable_of_nonzero (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (left right : List Choice)
    (hne : context ⊓ (FilterCoefficients.values (forcing arity color initial) filter left ⊓
      FilterCoefficients.values (forcing arity color initial) filter right) ≠ ⊥) :
    left.IsPrefix right ∨ right.IsPrefix left := by
  by_contra h
  exact hne (bot_unique (incompatible_weights context arity color initial filter hfilter left right
    (fun hl => h (Or.inl hl)) (fun hr => h (Or.inr hr))))

theorem prefix_of_length_le (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (left right : List Choice) (hlength : left.length ≤ right.length)
    (hne : context ⊓ (FilterCoefficients.values (forcing arity color initial) filter left ⊓
      FilterCoefficients.values (forcing arity color initial) filter right) ≠ ⊥) :
    left.IsPrefix right := by
  rcases comparable_of_nonzero context arity color initial filter hfilter left right hne with h | h
  · exact h
  · have heq : right = left := List.IsPrefix.eq_of_length_le h hlength
    rw [heq]

end Erdos597Object.BooleanRamseyCoherence
