import Erdos597Object.BooleanCountableDecision
import Erdos597Object.BooleanOrdinalBridge

set_option backward.isDefEq.respectTransparency false

/-! Preservation of ground uncountability by a dense omega-closed Boolean basis. -/

namespace Erdos597Object.BooleanClosedUncountability

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet Cardinal Ordinal
open BooleanSets BooleanFunctionBridge

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem countable_of_injected_discrete (hB : has_dense_omega_closed_subset B)
    (element : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (element i =ᴮ element j) = ⊥)
    (domain : bSet B) {context : B} (hne : context ≠ ⊥)
    (hmembers : ∀ i, context ≤ element i ∈ᴮ domain)
    (hinjects : context ≤ injectsIntoValue (V B) domain bSet.omega) : Countable I := by
  have hseparate : ∀ i j, i ≠ j →
      context ⊓ context ⊓ (element i =ᴮ element j) = ⊥ := by
    intro i j hij
    rw [hdiscrete i j hij, inf_bot_eq]
  exact BooleanCountableDecision.countable_of_constant_cover hB context hne
    (ContextualCCC.cover_of_injected_members element (fun _ => context) domain
      (fun _ => le_rfl) hmembers hseparate hinjects)

theorem injection_value_eq_bot (hB : has_dense_omega_closed_subset B) [Uncountable I]
    (element : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (element i =ᴮ element j) = ⊥)
    (domain : bSet B) (hmembers : ∀ i, ⊤ ≤ element i ∈ᴮ domain) :
    injectsIntoValue (V B) domain bSet.omega = ⊥ := by
  by_contra hne
  exact not_countable (countable_of_injected_discrete hB element hdiscrete domain hne
    (fun i => le_top.trans (hmembers i)) le_rfl)

theorem ordinal_check_not_countable (hB : has_dense_omega_closed_subset B)
    (o : Ordinal.{0}) (ho : ℵ₀ < o.card) :
    injectsIntoValue (V B) (bSet.check o.toPSet) bSet.omega = ⊥ := by
  have : Uncountable o.ToType := Cardinal.aleph0_lt_mk_iff.mp (by simpa using ho)
  let element : o.ToType → bSet B :=
    fun i => bSet.check (Ordinal.toPSet (Ordinal.typein (α := o.ToType) (· < ·) i))
  apply injection_value_eq_bot hB element
  · intro i j hij
    apply bSet.check_bv_eq_bot_of_not_equiv
    intro heq
    exact hij (Ordinal.typein_injective (α := o.ToType) (· < ·) (Flypitch.ordinal.mk_inj heq))
  · intro i
    exact bSet.check_mem (Flypitch.ordinal.mk_mem_mk_of_lt (Ordinal.typein_lt_self i))

theorem omegaOne_check_not_countable (hB : has_dense_omega_closed_subset B) :
    injectsIntoValue (V B) (bSet.check (ω₁ : Ordinal.{0}).toPSet) bSet.omega = ⊥ := by
  apply ordinal_check_not_countable hB
  simp

theorem omegaOneValue_check (hB : has_dense_omega_closed_subset B) :
    ⊤ ≤ omegaOneValue (V B) (bSet.check (ω₁ : Ordinal.{0}).toPSet) := by
  unfold omegaOneValue
  refine le_inf ?_ (le_inf ?_ ?_)
  · rw [BooleanOrdinalBridge.ordinalValue_eq_Ord]
    exact bSet.check_Ord (Flypitch.pSet.Ord_mk _)
  · change ⊤ ≤ (injectsIntoValue (V B) (bSet.check (ω₁ : Ordinal.{0}).toPSet) bSet.omega)ᶜ
    rw [omegaOne_check_not_countable hB, compl_bot]
  · apply le_iInf
    intro x
    apply lattice.bv_imp_intro
    exact BooleanOrdinalBridge.countable_members_of_check_omegaOne x inf_le_right

end Erdos597Object.BooleanClosedUncountability
