import Erdos597Object.BooleanTupleRamsey

set_option backward.isDefEq.respectTransparency false

/-! Boolean coverage by infinite all-good tuple witnesses and finite bad thinning. -/

namespace Erdos597Object.BooleanRamseyAlternatives

open BooleanInfiniteSets BooleanFiniteSelections

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def goodSupport (n : ℕ) (color : (Fin n → ℕ) → B) : B :=
  sSup {part : B | ∃ selected : ℕ → B, part ≤ infiniteValue selected ∧
    ∀ tuple : Fin n → ℕ, StrictMono tuple →
      part ⊓ tupleWeight selected tuple ≤ color tuple}

theorem witness_le_goodSupport (part : B) (n : ℕ) (color : (Fin n → ℕ) → B)
    (selected : ℕ → B) (hinfinite : part ≤ infiniteValue selected)
    (hgood : ∀ tuple : Fin n → ℕ, StrictMono tuple →
      part ⊓ tupleWeight selected tuple ≤ color tuple) :
    part ≤ goodSupport n color :=
  le_sSup ⟨selected, hinfinite, hgood⟩

theorem positive_side_le (context : B) (n : ℕ) (color : (Fin n → ℕ) → B)
    (selected : ℕ → B) (side : B) (hinfinite : context ≤ infiniteValue selected)
    (hhomogeneous : BooleanTupleRamsey.Homogeneous context n color selected side) :
    context ⊓ side ≤ goodSupport n color := by
  apply witness_le_goodSupport (context ⊓ side) n color selected
    (inf_le_left.trans hinfinite)
  intro tuple htuple
  have hweight : (context ⊓ side) ⊓ tupleWeight selected tuple ≤
      context ⊓ (tupleWeight selected tuple ⊓ side) := by
    exact le_inf (inf_le_left.trans inf_le_left)
      (le_inf inf_le_right (inf_le_left.trans inf_le_right))
  exact hweight.trans (hhomogeneous tuple htuple).1

theorem negative_of_avoiding_support (context : B) (n : ℕ)
    (color : (Fin n → ℕ) → B) (selected : ℕ → B) (side : B)
    (hinfinite : context ≤ infiniteValue selected)
    (hhomogeneous : BooleanTupleRamsey.Homogeneous context n color selected side)
    (havoid : context ≤ (goodSupport n color)ᶜ) :
    ∀ tuple : Fin n → ℕ, StrictMono tuple →
      context ⊓ tupleWeight selected tuple ≤ (color tuple)ᶜ := by
  have hside : context ⊓ side ≤ (⊥ : B) := by
    have hgood := positive_side_le context n color selected side hinfinite hhomogeneous
    have hboth := le_inf hgood (inf_le_left.trans havoid)
    simpa only [inf_compl_eq_bot] using hboth
  have hnegative : context ≤ sideᶜ := by
    calc
      context = context ⊓ (side ⊔ sideᶜ) := by simp only [sup_compl_eq_top, inf_top_eq]
      _ = (context ⊓ side) ⊔ (context ⊓ sideᶜ) := by
        simp only [inf_sup_left]
      _ ≤ ⊥ ⊔ sideᶜ := sup_le_sup hside inf_le_right
      _ = sideᶜ := bot_sup_eq _
  intro tuple htuple
  apply le_trans _ (hhomogeneous tuple htuple).2
  exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hnegative))

theorem exists_bad (context : ScheduledIteration.finalAlgebra) (n : ℕ)
    (color : (Fin n → ℕ) → ScheduledIteration.finalAlgebra)
    (initial : ℕ → ScheduledIteration.finalAlgebra)
    (hinfinite : context ≤ infiniteValue initial)
    (havoid : context ≤ (goodSupport n color)ᶜ) :
    ∃ selected : ℕ → ScheduledIteration.finalAlgebra,
      (∀ i, selected i ≤ initial i) ∧ context ≤ infiniteValue selected ∧
      ∀ tuple : Fin n → ℕ, StrictMono tuple →
        context ⊓ tupleWeight selected tuple ≤ (color tuple)ᶜ := by
  obtain ⟨selected, side, hsub, hlarge, hhomogeneous⟩ :=
    BooleanTupleRamsey.exists_homogeneous context n color initial hinfinite
  exact ⟨selected, hsub, hlarge,
    negative_of_avoiding_support context n color selected side hlarge hhomogeneous havoid⟩

theorem exists_all_bad (context : ScheduledIteration.finalAlgebra)
    (arity : ℕ → ℕ)
    (color : (k : ℕ) → (Fin (arity k) → ℕ) → ScheduledIteration.finalAlgebra)
    (n : ℕ) (initial : ℕ → ScheduledIteration.finalAlgebra)
    (hinfinite : context ≤ infiniteValue initial)
    (havoid : ∀ k, k < n → context ≤ (goodSupport (arity k) (color k))ᶜ) :
    ∃ selected : ℕ → ScheduledIteration.finalAlgebra,
      (∀ i, selected i ≤ initial i) ∧ context ≤ infiniteValue selected ∧
      ∀ k, k < n → ∀ tuple : Fin (arity k) → ℕ, StrictMono tuple →
        context ⊓ tupleWeight selected tuple ≤ (color k tuple)ᶜ := by
  induction n generalizing initial with
  | zero =>
    exact ⟨initial, fun _ => le_rfl, hinfinite, fun k hk => (Nat.not_lt_zero k hk).elim⟩
  | succ n ih =>
    obtain ⟨previous, hprevious, hlarge, hbad⟩ :=
      ih initial hinfinite (fun k hk => havoid k (Nat.lt_succ_of_lt hk))
    obtain ⟨selected, hsub, hlargeSelected, hlast⟩ :=
      exists_bad context (arity n) (color n) previous hlarge (havoid n (Nat.lt_succ_self n))
    refine ⟨selected, fun i => (hsub i).trans (hprevious i), hlargeSelected, ?_⟩
    intro k hk tuple htuple
    by_cases hearlier : k < n
    · exact (inf_le_inf_left context (tupleWeight_mono selected previous tuple hsub)).trans
        (hbad k hearlier tuple htuple)
    · have heq : k = n := by omega
      subst k
      exact hlast tuple htuple

end Erdos597Object.BooleanRamseyAlternatives
