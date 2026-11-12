import Erdos597Object.CHInSets
import Erdos597Object.MartinEquivalence
import Mathlib.SetTheory.Cardinal.Continuum

set_option backward.isDefEq.respectTransparency false

/-! Match the library CH sentence with the hypothesis of the negative partition theorem. -/

namespace Erdos597Object.CHInterpretation

open Cardinal Ordinal Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open scoped Cardinal Ordinal
open Erdos597Object.SetInterpretation Erdos597Object.SetFunctions
open Erdos597Object.CHInSets Erdos597Object.FirstUncountable
open Erdos597Object.OrdinalPresentation Erdos597Object.OrdinalsInSets
open Erdos597Object.AssertionInterpretation

theorem injects_powersetOmega_ordinal_iff (a : Ordinal.{0}) :
    injectsIntoValue setStructure (ZFSet.powerset ZFSet.omega) a.toZFSet ↔
      (2 : Cardinal.{0}) ^ ℵ₀ ≤ a.card := by
  rw [injectsIntoValue_set]
  constructor
  · rintro ⟨f⟩
    let g := (powersetOmegaEquiv.symm.toEmbedding.trans f).trans (ordinalEquiv a).symm.toEmbedding
    simpa using Cardinal.mk_le_of_injective g.injective
  · intro h
    have hcard : #(Set ℕ) ≤ #(a.ToType) := by simpa using h
    obtain ⟨f⟩ := (Cardinal.le_def _ _).mp hcard
    exact ⟨(powersetOmegaEquiv.toEmbedding.trans f).trans (ordinalEquiv a).toEmbedding⟩

theorem continuumHypothesisValue_set_raw :
    continuumHypothesisValue setStructure ↔
      ∀ x : ZFSet.{0}, x.IsOrdinal →
        injectsIntoValue setStructure x ZFSet.omega ∨
          injectsIntoValue setStructure (ZFSet.powerset ZFSet.omega) x := by
  simp [continuumHypothesisValue, ordinalValue_set, surjectsSubsetValue_iff_injectsInto,
    powersetValue_set, Erdos597Object.PartitionInterpretation.omegaValue_set,
    or_iff_not_imp_left]
  rfl

theorem continuumHypothesisValue_set_iff :
    continuumHypothesisValue setStructure ↔ (2 : Cardinal.{0}) ^ ℵ₀ = ℵ₁ := by
  rw [continuumHypothesisValue_set_raw]
  constructor
  · intro h
    rcases h (ω₁ : Ordinal.{0}).toZFSet (ZFSet.isOrdinal_toZFSet _) with hsmall | hlarge
    · rw [← omega_toZFSet, injectsInto_ordinals_iff] at hsmall
      have hbad : (ℵ₁ : Cardinal.{0}) ≤ ℵ₀ := by simpa using hsmall
      exact (not_le_of_gt Cardinal.aleph0_lt_aleph_one hbad).elim
    · have hupper := (injects_powersetOmega_ordinal_iff _).mp hlarge
      apply le_antisymm
      · simpa using hupper
      · exact Cardinal.aleph_one_le_continuum
  · intro hCH x hx
    obtain ⟨a, rfl⟩ := ZFSet.isOrdinal_iff_mem_range_toZFSet.mp hx
    by_cases hcountable : a.card ≤ ℵ₀
    · left
      rw [← omega_toZFSet, injectsInto_ordinals_iff]
      simpa using hcountable
    · right
      rw [injects_powersetOmega_ordinal_iff, hCH]
      exact Cardinal.aleph_one_le_iff.mpr (lt_of_not_ge hcountable)

theorem originalCH_sentence_iff :
    boolean_realize_sentence setStructure CH_f ↔ (2 : Cardinal.{0}) ^ ℵ₀ = ℵ₁ := by
  rw [realize_originalCH, continuumHypothesisValue_set_iff]

theorem negativeConditional_set : boolean_realize_sentence setStructure negativeConditional := by
  unfold negativeConditional boolean_realize_sentence
  rw [boolean_realize_bounded_formula_imp]
  rw [boolean_realize_bounded_formula_not]
  simp only [Flypitch.lattice.imp, sup_Prop_eq]
  change (¬ boolean_realize_sentence setStructure CH_f) ∨
    ¬ boolean_realize_sentence setStructure finiteAssertion
  classical
  simp only [or_iff_not_imp_left, not_not]
  intro h
  exact finiteAssertion_fails_under_CH (originalCH_sentence_iff.mp h)

end Erdos597Object.CHInterpretation
