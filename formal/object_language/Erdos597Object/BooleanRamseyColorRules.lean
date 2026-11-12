import Erdos597Object.BooleanRamseyHistories

set_option backward.isDefEq.respectTransparency false

/-! Colour rules enforced on finite subsets of a Ramsey history. -/

namespace Erdos597Object.BooleanRamseyColorRules

open BooleanRamseyTree BooleanRamseySelection BooleanRamseyHistories

variable {B : Type} [CompleteBooleanAlgebra B]

theorem points_prefix {history extended : List Choice} (hprefix : history.IsPrefix extended) :
    points history ⊆ points extended := by
  intro n hn
  obtain ⟨choice, hchoice, heq⟩ := (point_mem history n).mp hn
  exact (point_mem extended n).mpr ⟨choice, List.IsPrefix.subset hprefix hchoice, heq⟩

theorem weight_prefix_le (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    {history extended : List Choice} (hprefix : history.IsPrefix extended) :
    weight arity color initial extended ≤ weight arity color initial history := by
  obtain ⟨extra, rfl⟩ := hprefix
  exact weight_append_le arity color initial history extra

theorem history_decision (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (hpositive : 0 < arity) (history : List Choice) (subset : Finset ℕ) (n : ℕ)
    (hcard : subset.card = arity) (hsubset : subset ⊆ points history)
    (hn : n ∈ points history) (hbefore : ∀ x ∈ subset, x < n) :
    weight arity color initial history ≤
      if recorded history subset then color (insert n subset) else (color (insert n subset))ᶜ := by
  by_cases hzero : weight arity color initial history = ⊥
  · rw [hzero]
    exact bot_le
  · have hincreasing := weight_nonzero_increasing arity color initial history hzero
    obtain ⟨entry, hentry, rfl⟩ := (point_mem history n).mp hn
    obtain ⟨stem, rest, rfl⟩ := List.mem_iff_append.mp hentry
    have hsubsetPrefix : subset ⊆ points stem := by
      intro x hx
      obtain ⟨old, hold, heq⟩ := (point_mem (stem ++ entry :: rest) x).mp (hsubset hx)
      rcases List.mem_append.mp hold with hold | hold
      · exact (point_mem stem x).mpr ⟨old, hold, heq⟩
      · rcases List.mem_cons.mp hold with hold | hold
        · subst old
          have hlt := hbefore x hx
          rw [← heq] at hlt
          exact False.elim (Nat.lt_irrefl _ hlt)
        · have hafter := (List.pairwise_cons.mp (List.pairwise_append.mp hincreasing).2.1).1 old hold
          rw [heq] at hafter
          exact False.elim (Nat.lt_asymm (hbefore x hx) hafter)
    have hrecord := recorded_stable stem (stem ++ entry :: rest) subset hincreasing
      (List.prefix_append stem (entry :: rest)) hsubsetPrefix
    rw [hrecord]
    have hweight : weight arity color initial (stem ++ entry :: rest) ≤
        weight arity color initial (stem ++ [entry]) := by
      simpa only [List.append_assoc, List.singleton_append] using
        weight_append_le arity color initial (stem ++ [entry]) rest
    have hpoint : weight arity color initial (stem ++ [entry]) ≤
        (state arity color initial stem).2 entry.1 := by
      unfold weight
      rw [state_snoc]
      exact step_infinite_le_point arity color _ _ entry
    exact hweight.trans (hpoint.trans
      (reservoir_decision arity color initial hpositive stem subset hcard hsubsetPrefix entry.1))

end Erdos597Object.BooleanRamseyColorRules
