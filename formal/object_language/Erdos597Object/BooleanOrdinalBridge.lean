import Erdos597Object.BooleanFunctionBridge

set_option backward.isDefEq.respectTransparency false

/-! The ordinal and first-uncountable-ordinal formulas in a CCC Boolean-valued model. -/

namespace Erdos597Object.BooleanOrdinalBridge

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet Ordinal
open BooleanSets BooleanFunctionBridge BooleanUncountability

variable {B : Type} [CompleteBooleanAlgebra B]

theorem transitiveValue_eq_is_transitive (x : bSet B) :
    transitiveValue (V B) x = bSet.is_transitive x := by
  simp only [transitiveValue, bSet.is_transitive, subsetValue_bSet, memberValue_bSet, lattice.imp]
  rfl

theorem trichotomyValue_eq_epsilon_trichotomy (x : bSet B) :
    trichotomyValue (V B) x = bSet.epsilon_trichotomy x := by
  simp only [trichotomyValue, bSet.epsilon_trichotomy, memberValue_bSet, eqValue_bSet,
    lattice.imp, sup_assoc]
  rfl

theorem wellFoundedValue_eq_epsilon_well_founded (x : bSet B) :
    wellFoundedValue (V B) x = bSet.epsilon_well_founded x := by
  simp only [wellFoundedValue, bSet.epsilon_well_founded, subsetValue_bSet,
    memberValue_bSet, eqValue_bSet, lattice.imp, compl_compl, sup_assoc]
  rfl

theorem ordinalValue_eq_Ord (x : bSet B) : ordinalValue (V B) x = bSet.Ord x := by
  rw [ordinalValue, trichotomyValue_eq_epsilon_trichotomy,
    wellFoundedValue_eq_epsilon_well_founded, transitiveValue_eq_is_transitive]
  rfl

theorem omegaOneValue_ext : bSet.B_ext (fun x : bSet B => omegaOneValue (V B) x) := by
  simp only [omegaOneValue, ordinalValue_eq_Ord, injectsInto_eq_injects_into]
  exact bSet.B_ext_inf bSet.B_ext_Ord
    (bSet.B_ext_inf (bSet.B_ext_compl bSet.B_ext_injects_into_left)
      (bSet.B_ext_iInf fun y => bSet.B_ext_sup
        (bSet.B_ext_compl (bSet.B_ext_mem_right y)) (bSet.B_ext_const _)))

theorem countable_members_of_check_omegaOne {context : B} (x : bSet B)
    (hmem : context ≤ x ∈ᴮ bSet.check (ω₁ : Ordinal.{0}).toPSet) :
    context ≤ injectsIntoValue (V B) x bSet.omega := by
  rw [injectsInto_eq_injects_into]
  have hmem' : context ≤ x ∈ᴮ bSet.check Flypitch.pSet.aleph_one := by
    simpa only [Flypitch.pSet.aleph_one, Flypitch.pSet.card_ex, Flypitch.ordinal.mk,
      Cardinal.ord_aleph] using hmem
  exact bSet.injects_into_omega_of_mem_aleph_one_check hmem'

theorem omegaOneValue_check (hB : Flypitch.BA_CCC B) :
    ⊤ ≤ omegaOneValue (V B) (bSet.check (ω₁ : Ordinal.{0}).toPSet) := by
  unfold omegaOneValue
  refine le_inf ?_ (le_inf ?_ ?_)
  · rw [ordinalValue_eq_Ord]
    exact bSet.check_Ord (Flypitch.pSet.Ord_mk _)
  · change ⊤ ≤ (injectsIntoValue (V B) (bSet.check (ω₁ : Ordinal.{0}).toPSet) bSet.omega)ᶜ
    rw [omegaOne_check_not_countable hB, compl_bot]
  · apply le_iInf
    intro x
    apply lattice.bv_imp_intro
    exact countable_members_of_check_omegaOne x inf_le_right

theorem omegaOneValue_unique (hB : Flypitch.BA_CCC B) {context : B} (x : bSet B)
    (hx : context ≤ omegaOneValue (V B) x) :
    context ≤ x =ᴮ bSet.check (ω₁ : Ordinal.{0}).toPSet := by
  let canonical : bSet B := bSet.check (ω₁ : Ordinal.{0}).toPSet
  have hxOrd : context ≤ bSet.Ord x :=
    (hx.trans inf_le_left).trans_eq (ordinalValue_eq_Ord x)
  have hcanonicalOrd : context ≤ bSet.Ord canonical :=
    bSet.check_Ord (Flypitch.pSet.Ord_mk _)
  have htrichotomy := bSet.Ord.trichotomy hxOrd hcanonicalOrd
  have hnot : context ≤ (injectsIntoValue (V B) x bSet.omega)ᶜ :=
    hx.trans (inf_le_right.trans inf_le_left)
  have hsmall : context ⊓ (x ∈ᴮ canonical) ≤ ⊥ := by
    have hinjects := countable_members_of_check_omegaOne x
      (show context ⊓ (x ∈ᴮ canonical) ≤ x ∈ᴮ canonical from inf_le_right)
    exact (le_inf hinjects (inf_le_left.trans hnot)).trans (by simp)
  have hlarge : context ⊓ (canonical ∈ᴮ x) ≤ ⊥ := by
    have hall := hx.trans (inf_le_right.trans inf_le_right)
    have hentry := ((inf_le_left : context ⊓ (canonical ∈ᴮ x) ≤ context).trans hall).trans
      (iInf_le _ canonical)
    have hinjects := lattice.bv_context_apply hentry inf_le_right
    change context ⊓ (canonical ∈ᴮ x) ≤ injectsIntoValue (V B) canonical bSet.omega at hinjects
    exact hinjects.trans_eq (omegaOne_check_not_countable hB)
  apply (le_inf le_rfl htrichotomy).trans
  apply lattice.bv_or_elim_right
  · apply lattice.bv_or_elim_right
    · exact inf_le_right
    · exact hsmall.trans bot_le
  · exact hlarge.trans bot_le

theorem omegaOneValue_eq (hB : Flypitch.BA_CCC B) (x : bSet B) :
    omegaOneValue (V B) x = (x =ᴮ bSet.check (ω₁ : Ordinal.{0}).toPSet) := by
  apply le_antisymm (omegaOneValue_unique hB x le_rfl)
  have heq : (x =ᴮ bSet.check (ω₁ : Ordinal.{0}).toPSet) ≤
      bSet.check (ω₁ : Ordinal.{0}).toPSet =ᴮ x := bSet.bv_symm le_rfl
  exact (le_inf heq (le_top.trans (omegaOneValue_check hB))).trans
    (omegaOneValue_ext (bSet.check (ω₁ : Ordinal.{0}).toPSet) x)

end Erdos597Object.BooleanOrdinalBridge
