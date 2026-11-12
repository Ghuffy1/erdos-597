import Erdos597Object.BooleanRamseyForcing

set_option backward.isDefEq.respectTransparency false

/-! The infinite set selected by the finite-stem filter. -/

namespace Erdos597Object.BooleanRamseySelection

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInfiniteSets BooleanRamseyTree BooleanRamseyForcing BooleanPosetCoding

variable {B : Type} [CompleteBooleanAlgebra B]

theorem reservoir_le_initial (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (history : List Choice) : ∀ n, (state arity color initial history).2 n ≤ initial n := by
  refine List.reverseRecOn history ?_ ?_
  · intro n
    exact le_rfl
  · intro history choice ih n
    rw [state_snoc]
    exact (stepWeight_le arity color _ _ choice n).trans (ih n)

theorem step_infinite_le_point (arity : ℕ) (color : Finset ℕ → B) (points : Finset ℕ)
    (current : ℕ → B) (choice : Choice) :
    infiniteValue (stepWeight arity color points current choice) ≤ current choice.1 := by
  have h : infiniteValue (stepWeight arity color points current choice) ≤
      infiniteValue (fromWeight (fun n => current n ⊓ current choice.1) (choice.1 + 1)) :=
    infinite_mono (fun _ => inf_le_left)
  rw [infinite_from, infinite_inf_const] at h
  exact h.trans inf_le_right

theorem weight_le_point_member (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (history : List Choice) :
    ∀ n ∈ (state arity color initial history).1, weight arity color initial history ≤ initial n := by
  refine List.reverseRecOn history ?_ ?_
  · intro n hn
    simp only [state, List.foldl_nil, Finset.notMem_empty] at hn
  · intro history choice ih n hn
    rw [state_snoc] at hn
    change n ∈ insert choice.1 (state arity color initial history).1 at hn
    rcases Finset.mem_insert.mp hn with hn | hn
    · subst n
      unfold weight
      rw [state_snoc]
      exact (step_infinite_le_point arity color _ _ choice).trans
        (reservoir_le_initial arity color initial history choice.1)
    · exact (weight_snoc_le arity color initial history choice).trans (ih n hn)

noncomputable def selectedWeight (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (filter : bSet B) (n : ℕ) : B :=
  ⨆ history : List Choice, if n ∈ (state arity color initial history).1 then
    weight arity color initial history ⊓ (checkLabel history ∈ᴮ filter) else ⊥

theorem selected_le_initial (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (filter : bSet B) (n : ℕ) : selectedWeight arity color initial filter n ≤ initial n := by
  apply iSup_le
  intro history
  split_ifs with hn
  · exact inf_le_left.trans (weight_le_point_member arity color initial history n hn)
  · exact bot_le

theorem selected_infinite (context : B) (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (filter : bSet B)
    (hmeets : ∀ bound : ℕ, context ≤ ⨆ history : List Choice,
      denseWeight arity color initial bound history ⊓ (checkLabel history ∈ᴮ filter)) :
    context ≤ infiniteValue (selectedWeight arity color initial filter) := by
  apply le_iInf
  intro bound
  apply (hmeets bound).trans
  apply iSup_le
  intro history
  by_cases h : ∃ n ∈ (state arity color initial history).1, bound ≤ n
  · rw [denseWeight, ite_eq_left h]
    obtain ⟨n, hn, hbound⟩ := h
    apply le_iSup_of_le n
    apply le_iSup_of_le hbound
    apply le_iSup_of_le history
    simp only [hn, ↓reduceIte, le_refl]
  · simp only [denseWeight, h, ↓reduceIte, bot_inf_eq, bot_le]

theorem selection_exists (context : ScheduledIteration.finalAlgebra) (arity : ℕ)
    (color : Finset ℕ → ScheduledIteration.finalAlgebra) (initial : ℕ → ScheduledIteration.finalAlgebra)
    (hinfinite : context ≤ infiniteValue initial) :
    ∃ filter : bSet ScheduledIteration.finalAlgebra,
      context ≤ orderFilterValue (V ScheduledIteration.finalAlgebra)
        (domainName (forcing arity color initial) checkLabel)
        (orderName (forcing arity color initial) checkLabel) filter ∧
      (∀ n, selectedWeight arity color initial filter n ≤ initial n) ∧
      context ≤ infiniteValue (selectedWeight arity color initial filter) := by
  obtain ⟨filter, hfilter, hmeets⟩ := filter_exists context arity color initial hinfinite
  exact ⟨filter, hfilter, selected_le_initial arity color initial filter,
    selected_infinite context arity color initial filter hmeets⟩

end Erdos597Object.BooleanRamseySelection
