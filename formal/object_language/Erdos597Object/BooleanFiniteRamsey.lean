import Erdos597Object.BooleanRamseyEndHomogeneous

set_option backward.isDefEq.respectTransparency false

/-! Finite-arity Ramsey homogeneity for Boolean-valued subsets of omega. -/

namespace Erdos597Object.BooleanFiniteRamsey

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanInfiniteSets BooleanRamseyTree BooleanRamseyForcing BooleanRamseySelection
open BooleanRamseyRecorded BooleanRamseyEndHomogeneous BooleanPosetCoding

variable {B : Type} [CompleteBooleanAlgebra B]

def Homogeneous (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (selected : ℕ → B) (side : B) : Prop :=
  ∀ subset : Finset ℕ, subset.card = arity →
    (context ⊓ (subset.inf selected ⊓ side) ≤ color subset) ∧
    (context ⊓ (subset.inf selected ⊓ sideᶜ) ≤ (color subset)ᶜ)

theorem zero_homogeneous (context : B) (color : Finset ℕ → B) (initial : ℕ → B) :
    Homogeneous context 0 color initial (color ∅) := by
  intro subset hcard
  have hempty : subset = ∅ := Finset.card_eq_zero.mp hcard
  subst subset
  simp only [Finset.inf_empty, top_inf_eq]
  exact ⟨inf_le_right, inf_le_right⟩

theorem exists_one (context : B) (color : Finset ℕ → B) (initial : ℕ → B)
    (hinfinite : context ≤ infiniteValue initial) :
    ∃ selected : ℕ → B, ∃ side : B,
      (∀ n, selected n ≤ initial n) ∧ context ≤ infiniteValue selected ∧
      Homogeneous context 1 color selected side := by
  let side := infiniteValue (fun n => initial n ⊓ color {n})
  let selected : ℕ → B := fun n => (initial n ⊓ color {n} ⊓ side) ⊔
    (initial n ⊓ (color {n})ᶜ ⊓ sideᶜ)
  have hsub : ∀ n, selected n ≤ initial n := fun _ =>
    sup_le (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_left)
  have hinfiniteEq : infiniteValue selected = infiniteValue initial := by
    dsimp only [selected]
    rw [infinite_sup, BooleanRamseyTree.infinite_inf_const, BooleanRamseyTree.infinite_inf_const]
    change (side ⊓ side) ⊔ (infiniteValue (fun n => initial n ⊓ (color {n})ᶜ) ⊓ sideᶜ) = _
    rw [inf_idem, sup_inf_left, sup_compl_eq_top, inf_top_eq]
    exact (infinite_split initial (fun n => color {n})).symm
  refine ⟨selected, side, hsub, hinfinite.trans_eq hinfiniteEq.symm, ?_⟩
  intro subset hcard
  obtain ⟨n, rfl⟩ := Finset.card_eq_one.mp hcard
  rw [Finset.inf_singleton]
  have htrue : selected n ⊓ side ≤ color {n} := by
    dsimp only [selected]
    simp only [inf_sup_right, inf_assoc, inf_idem, compl_inf_self, inf_bot_eq, sup_bot_eq]
    exact inf_le_right.trans inf_le_left
  have hfalse : selected n ⊓ sideᶜ ≤ (color {n})ᶜ := by
    dsimp only [selected]
    simp only [inf_sup_right, inf_assoc, inf_idem, inf_compl_eq_bot, inf_bot_eq, bot_sup_eq]
    exact inf_le_right.trans inf_le_left
  exact ⟨inf_le_right.trans htrue, inf_le_right.trans hfalse⟩

theorem lift_homogeneous (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (hpositive : 0 < arity) (selected : ℕ → B) (side : B)
    (hsub : ∀ n, selected n ≤ selectedWeight arity color initial filter n)
    (hhomogeneous : Homogeneous context arity (recordedValue arity color initial filter) selected side) :
    Homogeneous context (arity + 1) color selected side := by
  classical
  intro subset hcard
  have hnonempty : subset.Nonempty := Finset.card_pos.mp (by omega)
  let n := subset.max' hnonempty
  let earlier := subset.erase n
  have hn : n ∈ subset := Finset.max'_mem subset hnonempty
  have hinsert : insert n earlier = subset := Finset.insert_erase hn
  have hearlier : earlier.card = arity := by
    dsimp only [earlier]
    rw [Finset.card_erase_of_mem hn, hcard]
    omega
  have hbefore : ∀ x ∈ earlier, x < n := by
    intro x hx
    have hx' := Finset.mem_erase.mp hx
    exact lt_of_le_of_ne (subset.le_max' x hx'.2) hx'.1
  have hselected : subset.inf selected ≤ subset.inf (selectedWeight arity color initial filter) := by
    apply Finset.le_inf
    intro x hx
    exact (Finset.inf_le hx).trans (hsub x)
  have hdrop : subset.inf selected ≤ earlier.inf selected := by
    apply Finset.le_inf
    intro x hx
    exact Finset.inf_le (Finset.mem_of_mem_erase hx)
  obtain ⟨htrue, hfalse⟩ := hhomogeneous earlier hearlier
  have htrueRule : context ⊓ (subset.inf (selectedWeight arity color initial filter) ⊓
      recordedValue arity color initial filter earlier) ≤ color subset := by
    simpa only [hinsert] using
      selected_true context arity color initial filter hfilter hpositive earlier n hearlier hbefore
  have hfalseRule : context ⊓ (subset.inf (selectedWeight arity color initial filter) ⊓
      (recordedValue arity color initial filter earlier)ᶜ) ≤ (color subset)ᶜ := by
    simpa only [hinsert] using
      selected_false context arity color initial filter hfilter hpositive earlier n hearlier hbefore
  constructor
  · apply (le_inf inf_le_left (le_inf (inf_le_right.trans (inf_le_left.trans hselected)) ?_)).trans htrueRule
    exact (le_inf inf_le_left (le_inf (inf_le_right.trans (inf_le_left.trans hdrop))
      (inf_le_right.trans inf_le_right))).trans htrue
  · apply (le_inf inf_le_left (le_inf (inf_le_right.trans (inf_le_left.trans hselected)) ?_)).trans hfalseRule
    exact (le_inf inf_le_left (le_inf (inf_le_right.trans (inf_le_left.trans hdrop))
      (inf_le_right.trans inf_le_right))).trans hfalse

theorem exists_homogeneous (context : ScheduledIteration.finalAlgebra) (arity : ℕ)
    (color : Finset ℕ → ScheduledIteration.finalAlgebra)
    (initial : ℕ → ScheduledIteration.finalAlgebra) (hinfinite : context ≤ infiniteValue initial) :
    ∃ selected : ℕ → ScheduledIteration.finalAlgebra, ∃ side : ScheduledIteration.finalAlgebra,
      (∀ n, selected n ≤ initial n) ∧ context ≤ infiniteValue selected ∧
      Homogeneous context arity color selected side := by
  induction arity generalizing context color initial with
  | zero => exact ⟨initial, color ∅, fun _ => le_rfl, hinfinite, zero_homogeneous context color initial⟩
  | succ arity ih =>
    by_cases hzero : arity = 0
    · subst arity
      exact exists_one context color initial hinfinite
    · have hpositive : 0 < arity := Nat.pos_of_ne_zero hzero
      obtain ⟨filter, hfilter, hselected, hinfiniteSelected⟩ :=
        selection_exists context arity color initial hinfinite
      obtain ⟨selected, side, hsub, hinfiniteFinal, hhomogeneous⟩ :=
        ih context (recordedValue arity color initial filter)
          (selectedWeight arity color initial filter) hinfiniteSelected
      exact ⟨selected, side, fun n => (hsub n).trans (hselected n), hinfiniteFinal,
        lift_homogeneous context arity color initial filter hfilter hpositive selected side hsub hhomogeneous⟩

end Erdos597Object.BooleanFiniteRamsey
