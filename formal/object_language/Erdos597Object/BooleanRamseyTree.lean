import Erdos597Object.BooleanInfiniteSets

set_option backward.isDefEq.respectTransparency false

/-! Finite stems with infinite reservoirs for the Boolean-valued Ramsey construction. -/

namespace Erdos597Object.BooleanRamseyTree

open BooleanInfiniteSets

variable {B : Type} [CompleteBooleanAlgebra B]

theorem infinite_inf_const (weight : ℕ → B) (value : B) :
    infiniteValue (fun n => weight n ⊓ value) = infiniteValue weight ⊓ value := by
  have htail (bound : ℕ) : tailValue (fun n => weight n ⊓ value) bound =
      tailValue weight bound ⊓ value := by
    unfold tailValue
    rw [iSup_inf_eq]
    simp_rw [iSup_inf_eq]
  simp only [infiniteValue, htail, iInf_inf_eq, iInf_const]

abbrev Choice := ℕ × Finset (Finset ℕ)

def constraints (arity : ℕ) (points : Finset ℕ) (next : ℕ) : Finset (Finset ℕ) :=
  (insert next points).powerset.filter (fun s => s.card = arity ∧ next ∈ s)

noncomputable def stepWeight (arity : ℕ) (color : Finset ℕ → B) (points : Finset ℕ)
    (current : ℕ → B) (choice : Choice) : ℕ → B :=
  restrictedWeight
    (fromWeight (fun n => current n ⊓ current choice.1) (choice.1 + 1))
    (fun s n => color (insert n s)) (constraints arity points choice.1)
    (fun s => decide (s ∈ choice.2))

theorem stepWeight_le (arity : ℕ) (color : Finset ℕ → B) (points : Finset ℕ)
    (current : ℕ → B) (choice : Choice) (n : ℕ) :
    stepWeight arity color points current choice n ≤ current n := by
  have h : stepWeight arity color points current choice n ≤
      fromWeight (fun n => current n ⊓ current choice.1) (choice.1 + 1) n := inf_le_left
  by_cases hn : choice.1 + 1 ≤ n
  · have h' : stepWeight arity color points current choice n ≤ current n ⊓ current choice.1 := by
      simpa only [fromWeight, hn, ↓reduceIte] using h
    exact h'.trans inf_le_left
  · have hz : stepWeight arity color points current choice n ≤ ⊥ := by
      simpa only [fromWeight, hn, ↓reduceIte] using h
    exact hz.trans bot_le

theorem step_point_extension (arity : ℕ) (color : Finset ℕ → B) (points : Finset ℕ)
    (current : ℕ → B) (next : ℕ) :
    infiniteValue current ⊓ current next ≤
      ⨆ marked : Finset (Finset ℕ), infiniteValue (stepWeight arity color points current (next, marked)) := by
  let base := fromWeight (fun n => current n ⊓ current next) (next + 1)
  have hbase : infiniteValue base = infiniteValue current ⊓ current next := by
    rw [infinite_from, infinite_inf_const]
  rw [← hbase]
  apply (finite_decisions base (fun s n => color (insert n s)) (constraints arity points next)).trans
  apply iSup_le
  intro choice
  let marked : Finset (Finset ℕ) := (constraints arity points next).filter (fun s => choice s)
  apply le_iSup_of_le marked
  apply infinite_mono
  intro n
  apply le_inf inf_le_left
  apply le_iInf
  intro s
  apply le_iInf
  intro hs
  have hchoice : decide (s ∈ marked) = choice s := by
    cases hc : choice s <;> simp [marked, hs, hc]
  change _ ≤ if decide (s ∈ marked) then color (insert n s) else (color (insert n s))ᶜ
  rw [hchoice]
  exact inf_le_right.trans ((iInf_le _ s).trans (iInf_le _ hs))

theorem step_extension (arity : ℕ) (color : Finset ℕ → B) (points : Finset ℕ)
    (current : ℕ → B) :
    infiniteValue current ≤ ⨆ next : ℕ, ⨆ marked : Finset (Finset ℕ),
      infiniteValue (stepWeight arity color points current (next, marked)) := by
  apply (le_inf le_rfl (infinite_le_total current)).trans
  rw [inf_iSup_eq]
  exact iSup_le fun next => (step_point_extension arity color points current next).trans
    (le_iSup (fun next : ℕ => ⨆ marked : Finset (Finset ℕ),
      infiniteValue (stepWeight arity color points current (next, marked))) next)

theorem step_extension_above (arity : ℕ) (color : Finset ℕ → B) (points : Finset ℕ)
    (current : ℕ → B) (bound : ℕ) :
    infiniteValue current ≤ ⨆ next : ℕ, ⨆ (_ : bound ≤ next),
      ⨆ marked : Finset (Finset ℕ), infiniteValue (stepWeight arity color points current (next, marked)) := by
  apply (le_inf le_rfl (infinite_le_tail current bound)).trans
  change infiniteValue current ⊓ (⨆ next : ℕ, ⨆ (_ : bound ≤ next), current next) ≤ _
  rw [inf_iSup_eq]
  apply iSup_le
  intro next
  rw [inf_iSup_eq]
  apply iSup_le
  intro hnext
  exact (step_point_extension arity color points current next).trans
    (le_iSup_of_le next (le_iSup_of_le hnext le_rfl))

noncomputable def step (arity : ℕ) (color : Finset ℕ → B)
    (state : Finset ℕ × (ℕ → B)) (choice : Choice) : Finset ℕ × (ℕ → B) :=
  (insert choice.1 state.1, stepWeight arity color state.1 state.2 choice)

noncomputable def state (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (history : List Choice) : Finset ℕ × (ℕ → B) :=
  history.foldl (step arity color) (∅, initial)

noncomputable def weight (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (history : List Choice) : B := infiniteValue (state arity color initial history).2

theorem state_snoc (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (history : List Choice) (choice : Choice) :
    state arity color initial (history ++ [choice]) = step arity color (state arity color initial history) choice := by
  simp only [state, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem weight_snoc_le (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (history : List Choice) (choice : Choice) :
    weight arity color initial (history ++ [choice]) ≤ weight arity color initial history := by
  unfold weight
  rw [state_snoc]
  exact infinite_mono (stepWeight_le arity color _ _ choice)

theorem weight_append_le (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (history extra : List Choice) :
    weight arity color initial (history ++ extra) ≤ weight arity color initial history := by
  induction extra generalizing history with
  | nil => simp only [List.append_nil, le_refl]
  | cons choice extra ih =>
    simpa only [List.append_assoc, List.singleton_append] using
      (ih (history ++ [choice])).trans (weight_snoc_le arity color initial history choice)

theorem weight_extensions_cover (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (history : List Choice) :
    weight arity color initial history ≤ ⨆ choice : Choice,
      weight arity color initial (history ++ [choice]) := by
  simp only [weight, state_snoc]
  exact (step_extension arity color (state arity color initial history).1
    (state arity color initial history).2).trans
    (iSup_le fun next => iSup_le fun marked => le_iSup_of_le (next, marked) le_rfl)

theorem weight_extensions_above (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (history : List Choice) (bound : ℕ) :
    weight arity color initial history ≤ ⨆ next : ℕ, ⨆ (_ : bound ≤ next),
      ⨆ marked : Finset (Finset ℕ), weight arity color initial (history ++ [(next, marked)]) := by
  simpa only [weight, state_snoc, step] using
    step_extension_above arity color (state arity color initial history).1
      (state arity color initial history).2 bound

end Erdos597Object.BooleanRamseyTree
