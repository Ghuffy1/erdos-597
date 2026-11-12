import Erdos597Object.ContextualCCC

set_option backward.isDefEq.respectTransparency false

/-! CCC algebras preserve the uncountability of ground-model discrete families. -/

namespace Erdos597Object.BooleanUncountability

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open scoped Cardinal Ordinal
open BooleanSets BooleanPosetCoding BooleanIteration ContextualCCC

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem countable_of_injected_discrete (hB : Flypitch.BA_CCC B)
    (element : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (element i =ᴮ element j) = ⊥)
    (domain : bSet B) {context : B} (hne : context ≠ ⊥)
    (hmembers : ∀ i, context ≤ element i ∈ᴮ domain)
    (hinjects : context ≤ injectsIntoValue (V B) domain bSet.omega) :
    Countable I := by
  have hseparate : ∀ i j, i ≠ j →
      context ⊓ context ⊓ (element i =ᴮ element j) = ⊥ := by
    intro i j hij
    rw [hdiscrete i j hij, inf_bot_eq]
  have hcover := cover_of_injected_members element (fun _ => context) domain
    (fun _ => le_rfl) hmembers hseparate hinjects
  have hcount := countable_support_of_cover hB (fun _ : I => context) hcover
  have hall : {i : I | (fun _ : I => context) i ≠ ⊥} = Set.univ :=
    Set.eq_univ_of_forall (fun _ => hne)
  rw [hall] at hcount
  exact Set.countable_univ_iff.mp hcount

theorem injection_value_eq_bot (hB : Flypitch.BA_CCC B) [Uncountable I]
    (element : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (element i =ᴮ element j) = ⊥)
    (domain : bSet B) (hmembers : ∀ i, ⊤ ≤ element i ∈ᴮ domain) :
    injectsIntoValue (V B) domain bSet.omega = ⊥ := by
  by_contra hne
  have hcount := countable_of_injected_discrete hB element hdiscrete domain hne
    (fun i => le_top.trans (hmembers i)) le_rfl
  exact not_countable hcount

theorem weighted_top_not_countable (hB : Flypitch.BA_CCC B) [Uncountable I]
    (element : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (element i =ᴮ element j) = ⊥) :
    injectsIntoValue (V B) (weightedSet element (fun _ => ⊤)) bSet.omega = ⊥ :=
  injection_value_eq_bot hB element hdiscrete _ (weight_le_member element (fun _ => ⊤))

theorem checkLabels_not_countable (hB : Flypitch.BA_CCC B) [Uncountable I] :
    injectsIntoValue (V B)
      (weightedSet (checkLabel (B := B) (I := I)) (fun _ => ⊤)) bSet.omega = ⊥ :=
  weighted_top_not_countable hB checkLabel (fun _ _ h => checkLabel_discrete h)

theorem ordinal_check_not_countable (hB : Flypitch.BA_CCC B)
    (o : Ordinal.{0}) (ho : ℵ₀ < o.card) :
    injectsIntoValue (V B) (bSet.check o.toPSet) bSet.omega = ⊥ := by
  haveI : Uncountable o.ToType := Cardinal.aleph0_lt_mk_iff.mp (by simpa using ho)
  let element : o.ToType → bSet B :=
    fun i => bSet.check (Ordinal.toPSet (Ordinal.typein (α := o.ToType) (· < ·) i))
  apply injection_value_eq_bot hB element
  · intro i j hij
    apply bSet.check_bv_eq_bot_of_not_equiv
    intro heq
    exact hij (Ordinal.typein_injective (α := o.ToType) (· < ·) (Flypitch.ordinal.mk_inj heq))
  · intro i
    exact bSet.check_mem (Flypitch.ordinal.mk_mem_mk_of_lt (Ordinal.typein_lt_self i))

theorem omegaOne_check_not_countable (hB : Flypitch.BA_CCC B) :
    injectsIntoValue (V B) (bSet.check (ω₁ : Ordinal.{0}).toPSet) bSet.omega = ⊥ := by
  apply ordinal_check_not_countable hB
  simpa using Cardinal.aleph0_lt_aleph_one

end Erdos597Object.BooleanUncountability
