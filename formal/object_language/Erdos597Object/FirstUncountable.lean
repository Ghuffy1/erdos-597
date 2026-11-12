import Erdos597Object.OrdinalsInSets
import Erdos597Object.OriginalPartition

set_option backward.isDefEq.respectTransparency false

/-! The first uncountable ordinal in the ordinary set interpretation. -/

namespace Erdos597Object.FirstUncountable

open Cardinal Ordinal
open scoped Cardinal Ordinal
open Erdos597Object.SetInterpretation Erdos597Object.SetFunctions
open Erdos597Object.OrdinalsInSets Erdos597Object.OrdinalPresentation

noncomputable section

theorem injectsIntoValue_set (x y : ZFSet.{0}) :
    injectsIntoValue setStructure x y ↔ Nonempty (Members x ↪ Members y) := by
  rw [injectsIntoValue, iSup_Prop_eq]
  constructor
  · rintro ⟨relation, hfunc, hinj⟩
    refine ⟨⟨evaluate hfunc, (functionGraph_injective_iff _).mp ?_⟩⟩
    simpa only [functionGraph_evaluate] using hinj
  · rintro ⟨f⟩
    exact ⟨functionGraph f, functionGraph_functionFrom f,
      (functionGraph_injective_iff f).mpr f.injective⟩

theorem injectsInto_ordinals_iff (a b : Ordinal.{0}) :
    injectsIntoValue setStructure a.toZFSet b.toZFSet ↔ a.card ≤ b.card := by
  rw [injectsIntoValue_set]
  constructor
  · rintro ⟨f⟩
    let g : a.ToType ↪ b.ToType :=
      ((ordinalEquiv a).toEmbedding.trans f).trans (ordinalEquiv b).symm.toEmbedding
    simpa using Cardinal.mk_le_of_injective g.injective
  · intro h
    have hcard : Cardinal.mk a.ToType ≤ Cardinal.mk b.ToType := by simpa using h
    obtain ⟨f⟩ := (Cardinal.le_def _ _).mp hcard
    exact ⟨((ordinalEquiv a).symm.toEmbedding.trans f).trans (ordinalEquiv b).toEmbedding⟩

theorem omegaOneValue_set_raw (kappa : ZFSet.{0}) :
    omegaOneValue setStructure kappa ↔
      kappa.IsOrdinal ∧ ¬ injectsIntoValue setStructure kappa ZFSet.omega ∧
        ∀ alpha ∈ kappa, injectsIntoValue setStructure alpha ZFSet.omega := by
  simp [omegaOneValue, ordinalValue_set, or_iff_not_imp_left,
    Erdos597Object.PartitionInterpretation.omegaValue_set]
  intro _ _
  rfl

theorem omegaOneValue_set (kappa : ZFSet.{0}) :
    omegaOneValue setStructure kappa ↔ kappa = (ω₁ : Ordinal.{0}).toZFSet := by
  rw [omegaOneValue_set_raw]
  constructor
  · rintro ⟨hord, hbig, hsmall⟩
    obtain ⟨a, rfl⟩ := ZFSet.isOrdinal_iff_mem_range_toZFSet.mp hord
    have huncountable : ¬ a.card ≤ ℵ₀ := by
      rw [← omega_toZFSet, injectsInto_ordinals_iff] at hbig
      simpa using hbig
    have hlower : (ω₁ : Ordinal.{0}) ≤ a := by
      by_contra h
      have hlt : a < (ω₁ : Ordinal.{0}) := lt_of_not_ge h
      exact huncountable (Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_omega_iff_card_lt.mp hlt))
    have hupper : a ≤ (ω₁ : Ordinal.{0}) := by
      by_contra h
      have hlt : (ω₁ : Ordinal.{0}) < a := lt_of_not_ge h
      have hcountable := hsmall (ω₁ : Ordinal.{0}).toZFSet
        (Ordinal.toZFSet_mem_toZFSet_iff.mpr hlt)
      rw [← omega_toZFSet, injectsInto_ordinals_iff] at hcountable
      have hbad : (ℵ₁ : Cardinal.{0}) ≤ ℵ₀ := by simpa using hcountable
      exact (not_le_of_gt Cardinal.aleph0_lt_aleph_one) hbad
    exact congrArg Ordinal.toZFSet (le_antisymm hupper hlower)
  · rintro rfl
    refine ⟨ZFSet.isOrdinal_toZFSet _, ?_, ?_⟩
    · rw [← omega_toZFSet, injectsInto_ordinals_iff]
      simpa using (not_le_of_gt Cardinal.aleph0_lt_aleph_one)
    · intro alpha halpha
      obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp halpha
      rw [← omega_toZFSet, injectsInto_ordinals_iff]
      simpa using Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_omega_iff_card_lt.mp ha)

end

end Erdos597Object.FirstUncountable
