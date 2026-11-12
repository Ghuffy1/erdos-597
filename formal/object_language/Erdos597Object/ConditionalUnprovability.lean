import Erdos597Object.OrdinaryZFC

set_option backward.isDefEq.respectTransparency false

/-! Consequences of the ordinary ZFC model under the two stated set-theoretic hypotheses. -/

namespace Erdos597Object.ConditionalUnprovability

open Cardinal Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open scoped Cardinal
open Erdos597Object.SetInterpretation Erdos597Object.OrdinaryZFC
open Erdos597Object.AssertionInterpretation

local notation "[]" => dvector.nil

local instance : Nonempty setStructure := ⟨(∅ : ZFSet.{0})⟩

theorem forces_set_iff (f : sentence L_ZFC) :
    forces (⊤ : Prop) setStructure f ↔ boolean_realize_sentence setStructure f := by
  change (True → boolean_realize_sentence setStructure f) ↔ _
  exact ⟨fun h => h trivial, fun h _ => h⟩

theorem realize_sentence_not (f : sentence L_ZFC) :
    boolean_realize_sentence setStructure (∼f) ↔ ¬ boolean_realize_sentence setStructure f := by
  have hbot : boolean_realize_bounded_formula (S := setStructure) []
      (⊥ : sentence L_ZFC) [] = (⊥ : Prop) := by
    change boolean_realize_bounded_formula (S := setStructure) []
      (⟨preformula.falsum, trivial⟩ : sentence L_ZFC) [] = ⊥
    unfold boolean_realize_bounded_formula
    rfl
  simp [boolean_realize_sentence, sentence.not, sentence.imp, hbot, lattice.imp]

theorem finiteAssertion_unprovable_under_CH (hCH : (2 : Cardinal.{0}) ^ ℵ₀ = ℵ₁) :
    ¬ (Flypitch.ZFC.ZFC ⊢' finiteAssertion) := by
  have hneg : forces (⊤ : Prop) setStructure (∼finiteAssertion) :=
    (forces_set_iff _).mpr ((realize_sentence_not _).mpr (finiteAssertion_fails_under_CH hCH))
  exact unprovable_of_model_neg setStructure set_models_ZFC
    (hNonzero := (bot_lt_top : (⊥ : Prop) < ⊤)) hneg

theorem neg_finiteAssertion_unprovable_under_MA (hMA : Erdos597.MartinAxiomAlephOne) :
    ¬ (Flypitch.ZFC.ZFC ⊢' (∼finiteAssertion)) := by
  have hpos : forces (⊤ : Prop) setStructure finiteAssertion :=
    (forces_set_iff _).mpr (finiteAssertion_under_MA hMA)
  exact unprovable_of_model_neg setStructure set_models_ZFC
    (hNonzero := (bot_lt_top : (⊥ : Prop) < ⊤)) (forced_not_not_of_forced hpos)

end Erdos597Object.ConditionalUnprovability
