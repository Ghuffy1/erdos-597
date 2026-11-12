import Erdos597Object.BooleanRamseyCoherence

set_option backward.isDefEq.respectTransparency false

/-! Point growth and recorded colour constraints in finite Ramsey histories. -/

namespace Erdos597Object.BooleanRamseyHistories

open BooleanInfiniteSets BooleanRamseyTree BooleanRamseySelection

variable {B : Type} [CompleteBooleanAlgebra B]

def points (history : List Choice) : Finset ℕ := (history.map Prod.fst).toFinset

def Increasing (history : List Choice) : Prop := history.Pairwise (fun left right => left.1 < right.1)

def recorded (history : List Choice) (subset : Finset ℕ) : Bool :=
  history.foldl (fun previous choice => if choice.1 ∈ subset then decide (subset ∈ choice.2) else previous) false

theorem points_snoc (history : List Choice) (choice : Choice) :
    points (history ++ [choice]) = insert choice.1 (points history) := by
  simp [points]

theorem point_mem (history : List Choice) (n : ℕ) :
    n ∈ points history ↔ ∃ choice ∈ history, choice.1 = n := by
  simp [points]

theorem state_points (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (history : List Choice) : (state arity color initial history).1 = points history := by
  refine List.reverseRecOn history ?_ ?_
  · rfl
  · intro history choice ih
    rw [state_snoc, points_snoc]
    simpa only [step] using congrArg (insert choice.1) ih

theorem stepWeight_zero_of_le (arity : ℕ) (color : Finset ℕ → B) (oldPoints : Finset ℕ)
    (current : ℕ → B) (choice : Choice) (n : ℕ) (hn : n ≤ choice.1) :
    stepWeight arity color oldPoints current choice n = ⊥ := by
  have hcutoff : ¬ choice.1 + 1 ≤ n := by omega
  simp only [stepWeight, restrictedWeight, fromWeight, hcutoff, ↓reduceIte, bot_inf_eq]

theorem reservoir_above (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (history : List Choice) : ∀ point ∈ points history, ∀ n, n ≤ point →
      (state arity color initial history).2 n = ⊥ := by
  refine List.reverseRecOn history ?_ ?_
  · intro point hp
    simp only [points, List.map_nil, List.toFinset_nil, Finset.notMem_empty] at hp
  · intro history choice ih point hp n hn
    rw [points_snoc] at hp
    rw [state_snoc]
    change stepWeight arity color (state arity color initial history).1
      (state arity color initial history).2 choice n = ⊥
    rcases Finset.mem_insert.mp hp with hp | hp
    · subst point
      exact stepWeight_zero_of_le arity color _ _ choice n hn
    · exact bot_unique ((stepWeight_le arity color _ _ choice n).trans_eq (ih point hp n hn))

theorem weight_nonzero_increasing (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (history : List Choice) : weight arity color initial history ≠ ⊥ → Increasing history := by
  refine List.reverseRecOn history ?_ ?_
  · intro _
    exact List.Pairwise.nil
  · intro history choice ih hnonzero
    have hold : weight arity color initial history ≠ ⊥ := by
      intro hz
      exact hnonzero (bot_unique ((weight_snoc_le arity color initial history choice).trans_eq hz))
    have hgreater (earlier : Choice) (hearlier : earlier ∈ history) : earlier.1 < choice.1 := by
      by_contra hnot
      have hle : choice.1 ≤ earlier.1 := Nat.le_of_not_gt hnot
      have hz := reservoir_above arity color initial history earlier.1
        ((point_mem history earlier.1).mpr ⟨earlier, hearlier, rfl⟩) choice.1 hle
      have hbound : weight arity color initial (history ++ [choice]) ≤
          (state arity color initial history).2 choice.1 := by
        unfold weight
        rw [state_snoc]
        exact step_infinite_le_point arity color _ _ choice
      exact hnonzero (bot_unique (hbound.trans_eq hz))
    apply List.pairwise_append.mpr
    refine ⟨ih hold, by simp, ?_⟩
    intro earlier hearlier last hlast
    obtain rfl := List.mem_singleton.mp hlast
    exact hgreater earlier hearlier

theorem recorded_snoc (history : List Choice) (choice : Choice) (subset : Finset ℕ) :
    recorded (history ++ [choice]) subset =
      if choice.1 ∈ subset then decide (subset ∈ choice.2) else recorded history subset := by
  simp only [recorded, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem recorded_append_of_disjoint (history extra : List Choice) (subset : Finset ℕ)
    (hdisjoint : ∀ choice ∈ extra, choice.1 ∉ subset) :
    recorded (history ++ extra) subset = recorded history subset := by
  induction extra generalizing history with
  | nil => simp only [List.append_nil]
  | cons choice extra ih =>
    have hchoice := hdisjoint choice List.mem_cons_self
    have hrest : ∀ choice ∈ extra, choice.1 ∉ subset :=
      fun choice h => hdisjoint choice (List.mem_cons_of_mem _ h)
    rw [show history ++ choice :: extra = (history ++ [choice]) ++ extra by simp]
    rw [ih _ hrest, recorded_snoc, ite_eq_right hchoice]

theorem recorded_stable (history extended : List Choice) (subset : Finset ℕ)
    (hincreasing : Increasing extended) (hprefix : history.IsPrefix extended)
    (hsubset : subset ⊆ points history) : recorded extended subset = recorded history subset := by
  obtain ⟨extra, rfl⟩ := hprefix
  apply recorded_append_of_disjoint
  intro later hlater hmember
  obtain ⟨earlier, hearlier, heq⟩ := (point_mem history later.1).mp (hsubset hmember)
  have hcross := (List.pairwise_append.mp hincreasing).2.2 earlier hearlier later hlater
  rw [heq] at hcross
  exact Nat.lt_irrefl _ hcross

theorem reservoir_decision (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (hpositive : 0 < arity) (history : List Choice) :
    ∀ subset : Finset ℕ, subset.card = arity → subset ⊆ points history → ∀ n,
      (state arity color initial history).2 n ≤
        if recorded history subset then color (insert n subset) else (color (insert n subset))ᶜ := by
  refine List.reverseRecOn history ?_ ?_
  · intro subset hcard hsubset n
    have hempty : subset = ∅ := Finset.subset_empty.mp hsubset
    subst subset
    simp only [Finset.card_empty] at hcard
    omega
  · intro history choice ih subset hcard hsubset n
    have hsubsetNew : subset ⊆ insert choice.1 (points history) := by
      simpa only [points_snoc] using hsubset
    by_cases hpoint : choice.1 ∈ subset
    · have hconstraint : subset ∈ constraints arity (state arity color initial history).1 choice.1 := by
        rw [state_points]
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsubsetNew, hcard, hpoint⟩
      rw [state_snoc, recorded_snoc]
      simp only [hpoint, ↓reduceIte]
      exact inf_le_right.trans ((iInf_le _ subset).trans (iInf_le _ hconstraint))
    · have hsubsetOld : subset ⊆ points history := by
        intro x hx
        rcases Finset.mem_insert.mp (hsubsetNew hx) with h | h
        · exact (hpoint (h ▸ hx)).elim
        · exact h
      rw [state_snoc, recorded_snoc]
      simp only [hpoint, ↓reduceIte]
      exact (stepWeight_le arity color _ _ choice n).trans (ih subset hcard hsubsetOld n)

end Erdos597Object.BooleanRamseyHistories
