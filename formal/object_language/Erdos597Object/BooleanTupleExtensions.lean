import Erdos597Object.BooleanFiniteSelections

set_option backward.isDefEq.respectTransparency false

/-! Extend finite increasing tuples without changing their selected initial entries. -/

namespace Erdos597Object.BooleanTupleExtensions

open BooleanFiniteSelections

def extend {n : ℕ} (tuple : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : i < n then tuple ⟨i, h⟩ else Finset.univ.sup tuple + (i - n) + 1

theorem extend_at {n : ℕ} (tuple : Fin n → ℕ) (i : ℕ) (hi : i < n) :
    extend tuple i = tuple ⟨i, hi⟩ := by
  simp only [extend, dite_eq_left hi]

theorem extend_strict {n : ℕ} (tuple : Fin n → ℕ) (hmono : StrictMono tuple) :
    StrictMono (extend tuple) := by
  intro i j hij
  by_cases hi : i < n
  · by_cases hj : j < n
    · simpa only [extend, dite_eq_left hi, dite_eq_left hj] using
        hmono (show (⟨i, hi⟩ : Fin n) < ⟨j, hj⟩ from hij)
    · have hbound : tuple ⟨i, hi⟩ ≤ Finset.univ.sup tuple := Finset.le_sup (Finset.mem_univ _)
      simp only [extend, dite_eq_left hi, dite_eq_right hj]
      omega
  · have hj : ¬ j < n := by omega
    simp only [extend, dite_eq_right hi, dite_eq_right hj]
    omega

theorem weight_le_composition {B : Type} [CompleteBooleanAlgebra B] {m n : ℕ}
    (weight : ℕ → B) (tuple : Fin n → ℕ) (indices : Fin m → ℕ) (hbound : ∀ i, indices i < n) :
    tupleWeight weight tuple ≤ tupleWeight weight (extend tuple ∘ indices) := by
  apply Finset.le_inf
  intro i _
  change tupleWeight weight tuple ≤ weight (extend tuple (indices i))
  rw [extend_at tuple (indices i) (hbound i)]
  exact tupleWeight_le weight tuple ⟨indices i, hbound i⟩

end Erdos597Object.BooleanTupleExtensions
