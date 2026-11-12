import Erdos597Object.BooleanInfiniteSets

set_option backward.isDefEq.respectTransparency false

/-! Finite increasing selections retain the Boolean membership weights. -/

namespace Erdos597Object.BooleanFiniteSelections

open BooleanInfiniteSets

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def tupleWeight {n : ℕ} (weight : ℕ → B) (tuple : Fin n → ℕ) : B :=
  Finset.univ.inf (fun i => weight (tuple i))

noncomputable def boundedTuples (weight : ℕ → B) (n bound : ℕ) : B := by
  classical
  exact ⨆ tuple : Fin n → ℕ, if StrictMono tuple ∧ (∀ i, bound ≤ tuple i) then
    tupleWeight weight tuple else ⊥

theorem tupleWeight_le {n : ℕ} (weight : ℕ → B) (tuple : Fin n → ℕ) (i : Fin n) :
    tupleWeight weight tuple ≤ weight (tuple i) := Finset.inf_le (Finset.mem_univ i)

theorem tupleWeight_mono {n : ℕ} (left right : ℕ → B) (tuple : Fin n → ℕ)
    (h : ∀ i, left i ≤ right i) : tupleWeight left tuple ≤ tupleWeight right tuple := by
  apply Finset.le_inf
  intro i _
  exact (tupleWeight_le left tuple i).trans (h (tuple i))

theorem tupleWeight_subtuple {m n : ℕ} (weight : ℕ → B) (tuple : Fin n → ℕ) (indices : Fin m → Fin n) :
    tupleWeight weight tuple ≤ tupleWeight weight (tuple ∘ indices) := by
  apply Finset.le_inf
  intro i _
  exact tupleWeight_le weight tuple (indices i)

theorem tupleWeight_image {n : ℕ} (weight : ℕ → B) (tuple : Fin n → ℕ) :
    (Finset.univ.image tuple).inf weight = tupleWeight weight tuple := by
  simp only [Finset.inf_image, tupleWeight, Function.comp_def]

theorem bounded_tuples_cover (weight : ℕ → B) (n bound : ℕ) :
    infiniteValue weight ≤ boundedTuples weight n bound := by
  classical
  induction n generalizing bound with
  | zero =>
    apply le_iSup_of_le (Fin.elim0 : Fin 0 → ℕ)
    have h : StrictMono (Fin.elim0 : Fin 0 → ℕ) ∧ (∀ i : Fin 0, bound ≤ Fin.elim0 i) :=
      ⟨fun i => i.elim0, fun i => i.elim0⟩
    rw [ite_eq_left h]
    simp [tupleWeight]
  | succ n ih =>
    have hfirst : infiniteValue weight ≤ ⨆ first : ℕ, ⨆ (_ : bound ≤ first),
        infiniteValue weight ⊓ weight first := by
      simpa only [tailValue, inf_iSup_eq] using
        (le_inf (le_refl (infiniteValue weight)) (infinite_le_tail weight bound))
    apply hfirst.trans
    apply iSup_le
    intro first
    apply iSup_le
    intro hbound
    apply (inf_le_inf (ih (first + 1)) (le_refl (weight first))).trans
    unfold boundedTuples
    rw [iSup_inf_eq]
    apply iSup_le
    intro tuple
    by_cases htuple : StrictMono tuple ∧ (∀ i, first + 1 ≤ tuple i)
    · rw [ite_eq_left htuple]
      have hmono : StrictMono (Fin.cases first tuple) := by
        intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact False.elim ((lt_irrefl _) hij)
          | succ j => exact (Nat.lt_succ_self first).trans_le (htuple.2 j)
        | succ i =>
          cases j using Fin.cases with
          | zero => exact False.elim (Fin.not_lt_zero _ hij)
          | succ j => exact htuple.1 (Fin.succ_lt_succ_iff.mp hij)
      have hbounds : ∀ i, bound ≤ Fin.cases first tuple i := by
        intro i
        cases i using Fin.cases with
        | zero => exact hbound
        | succ i => exact (hbound.trans (Nat.le_succ first)).trans (htuple.2 i)
      apply le_iSup_of_le (Fin.cases first tuple)
      rw [ite_eq_left ⟨hmono, hbounds⟩]
      apply Finset.le_inf
      intro i _
      cases i using Fin.cases with
      | zero => exact inf_le_right
      | succ i => exact inf_le_left.trans (tupleWeight_le weight tuple i)
    · rw [ite_eq_right htuple, bot_inf_eq]
      exact bot_le

theorem increasing_tuples_cover (weight : ℕ → B) (n : ℕ) :
    infiniteValue weight ≤ ⨆ tuple : Fin n → ℕ,
      if StrictMono tuple then tupleWeight weight tuple else ⊥ := by
  simpa only [boundedTuples, Nat.zero_le, implies_true, and_true] using bounded_tuples_cover weight n 0

end Erdos597Object.BooleanFiniteSelections
