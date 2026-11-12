import Erdos597Object.FullMartinModel

set_option backward.isDefEq.respectTransparency false

/-! Consequences of the constructed model and the remaining syntactic implications. -/

namespace Erdos597Object.ModelConsequences

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC

variable {B : Type} [CompleteBooleanAlgebra B]

theorem provable_forced (S : bStructure L_ZFC B) [Nonempty S]
    {theory : Theory L_ZFC} {formula : sentence L_ZFC}
    (hmodel : forces_theory (⊤ : B) S theory) (hproof : theory ⊢' formula) :
    forces (⊤ : B) S formula := by
  obtain ⟨proof⟩ := hproof
  simpa only [inf_axioms_top_of_models hmodel] using
    (boolean_soundness (β := B) proof (S := S) (inferInstance : Nonempty S))

theorem forced_imp_elim (S : bStructure L_ZFC B) {context : B}
    (premise conclusion : sentence L_ZFC)
    (himp : forces context S (bd_imp premise conclusion))
    (hpremise : forces context S premise) : forces context S conclusion := by
  have hvalue : context ≤ lattice.imp (boolean_realize_sentence S premise)
      (boolean_realize_sentence S conclusion) := by
    simpa only [forces, boolean_realize_sentence, boolean_realize_bounded_formula_imp] using himp
  exact lattice.bv_context_apply hvalue hpremise

theorem consistent_of_model [Nontrivial B] (S : bStructure L_ZFC B) [Nonempty S]
    {theory : Theory L_ZFC} (hmodel : forces_theory (⊤ : B) S theory) :
    is_consistent theory := by
  intro hproof
  have hbot := provable_forced S hmodel hproof
  have hfalse : boolean_realize_bounded_formula (S := S) dvector.nil
      (⊥ : sentence L_ZFC) dvector.nil = (⊥ : B) := by
    change boolean_realize_bounded_formula (S := S) dvector.nil
      (⟨preformula.falsum, trivial⟩ : sentence L_ZFC) dvector.nil = ⊥
    unfold boolean_realize_bounded_formula
    rfl
  change (⊤ : B) ≤ boolean_realize_bounded_formula (S := S) dvector.nil
    (⊥ : sentence L_ZFC) dvector.nil at hbot
  rw [hfalse] at hbot
  exact not_le_of_gt (bot_lt_top : (⊥ : B) < ⊤) hbot

theorem final_models_martin :
    forces_theory (⊤ : ScheduledIteration.finalAlgebra) (V ScheduledIteration.finalAlgebra)
      (insert martinAxiomAlephOne Flypitch.ZFC.ZFC) := by
  apply le_iInf
  intro formula
  apply le_iInf
  intro hformula
  change formula = martinAxiomAlephOne ∨ formula ∈ Flypitch.ZFC.ZFC at hformula
  rcases hformula with rfl | hformula
  · exact FullMartinModel.final_martin_sentence
  · exact ((bSet_models_ZFC (β := ScheduledIteration.finalAlgebra)).trans
      (iInf_le _ formula)).trans (iInf_le _ hformula)

theorem martin_extension_consistent :
    is_consistent (insert martinAxiomAlephOne Flypitch.ZFC.ZFC) :=
  consistent_of_model (V ScheduledIteration.finalAlgebra) final_models_martin

theorem neg_martin_unprovable : ¬ (Flypitch.ZFC.ZFC ⊢' (∼martinAxiomAlephOne)) :=
  unprovable_of_model_neg (V ScheduledIteration.finalAlgebra) bSet_models_ZFC
    (hNonzero := bot_lt_top) (forced_not_not_of_forced FullMartinModel.final_martin_sentence)

theorem finiteAssertion_unprovable_of_negativeConditional
    (hproof : Flypitch.ZFC.ZFC ⊢' negativeConditional) :
    ¬ (Flypitch.ZFC.ZFC ⊢' finiteAssertion) := by
  let algebra := collapse_algebra.𝔹_collapse.{0}
  have hCH : forces (⊤ : algebra) (V algebra) CH_f :=
    (CH_f_sound (β := algebra) (Γ := ⊤)).2 collapse_algebra.CH₂_true
  have hnegative : forces (⊤ : algebra) (V algebra) (∼finiteAssertion) :=
    forced_imp_elim (V algebra) CH_f (bd_not finiteAssertion)
      (provable_forced (V algebra) bSet_models_ZFC hproof) hCH
  exact unprovable_of_model_neg (V algebra) bSet_models_ZFC
    (hNonzero := bot_lt_top) hnegative

theorem neg_finiteAssertion_unprovable_of_positiveConditional
    (hproof : Flypitch.ZFC.ZFC ⊢' positiveConditional) :
    ¬ (Flypitch.ZFC.ZFC ⊢' (∼finiteAssertion)) := by
  have hpositive : forces (⊤ : ScheduledIteration.finalAlgebra)
      (V ScheduledIteration.finalAlgebra) finiteAssertion :=
    forced_imp_elim (V ScheduledIteration.finalAlgebra) martinAxiomAlephOne finiteAssertion
      (provable_forced (V ScheduledIteration.finalAlgebra) bSet_models_ZFC hproof)
      FullMartinModel.final_martin_sentence
  exact unprovable_of_model_neg (V ScheduledIteration.finalAlgebra) bSet_models_ZFC
    (hNonzero := bot_lt_top) (forced_not_not_of_forced hpositive)

theorem finiteIndependence_of_conditionals
    (hnegative : Flypitch.ZFC.ZFC ⊢' negativeConditional)
    (hpositive : Flypitch.ZFC.ZFC ⊢' positiveConditional) : finiteIndependence :=
  ⟨finiteAssertion_unprovable_of_negativeConditional hnegative,
    neg_finiteAssertion_unprovable_of_positiveConditional hpositive⟩

theorem relativeFiniteIndependence_of_conditionals
    (hnegative : Flypitch.ZFC.ZFC ⊢' negativeConditional)
    (hpositive : Flypitch.ZFC.ZFC ⊢' positiveConditional) : relativeFiniteIndependence :=
  fun _ => finiteIndependence_of_conditionals hnegative hpositive

end Erdos597Object.ModelConsequences
