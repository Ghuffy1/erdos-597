import Erdos597Object.MartinSemantics
import Erdos597Object.FirstUncountable

set_option backward.isDefEq.respectTransparency false

/-! The ordinary set interpretation of Martin's axiom and its poset predicates. -/

namespace Erdos597Object.MartinInSets

open Erdos597Object.SetInterpretation Erdos597Object.OrdinalsInSets
open Erdos597Object.FirstUncountable Erdos597Object.OriginalPartition

theorem nonemptyValue_set (domain : ZFSet.{0}) :
    nonemptyValue setStructure domain ↔ ∃ x, x ∈ domain := by
  simp [nonemptyValue]
  rfl

theorem partialOrderValue_set (conditions order : ZFSet.{0}) :
    partialOrderValue setStructure conditions order ↔
      relationBetweenValue setStructure conditions conditions order ∧
      (∀ x ∈ conditions, ZFSet.pair x x ∈ order) ∧
      (∀ x ∈ conditions, ∀ y ∈ conditions,
        ZFSet.pair x y ∈ order → ZFSet.pair y x ∈ order → x = y) ∧
      (∀ x ∈ conditions, ∀ y ∈ conditions, ∀ z ∈ conditions,
        ZFSet.pair x y ∈ order → ZFSet.pair y z ∈ order → ZFSet.pair x z ∈ order) := by
  simp [partialOrderValue, or_iff_not_imp_left, and_imp]
  intro _
  rfl

theorem compatibleValue_set (conditions order x y : ZFSet.{0}) :
    compatibleValue setStructure conditions order x y ↔
      ∃ z ∈ conditions, ZFSet.pair z x ∈ order ∧ ZFSet.pair z y ∈ order := by
  simp [compatibleValue]
  rfl

theorem antichainValue_set (conditions order family : ZFSet.{0}) :
    antichainValue setStructure conditions order family ↔
      family ⊆ conditions ∧ ∀ x ∈ family, ∀ y ∈ family,
        x ≠ y → ¬ compatibleValue setStructure conditions order x y := by
  simp [antichainValue, subsetValue_set, or_iff_not_imp_left]
  intro _
  rfl

theorem countableChainConditionValue_set (conditions order : ZFSet.{0}) :
    countableChainConditionValue setStructure conditions order ↔
      ∀ family : ZFSet.{0}, antichainValue setStructure conditions order family →
        injectsIntoValue setStructure family ZFSet.omega := by
  simp [countableChainConditionValue, or_iff_not_imp_left,
    Erdos597Object.PartitionInterpretation.omegaValue_set]
  rfl

theorem denseValue_set (conditions order denseSet : ZFSet.{0}) :
    denseValue setStructure conditions order denseSet ↔
      denseSet ⊆ conditions ∧ ∀ x ∈ conditions,
        ∃ y ∈ denseSet, ZFSet.pair y x ∈ order := by
  simp [denseValue, subsetValue_set, or_iff_not_imp_left]
  intro _
  rfl

theorem orderFilterValue_set (conditions order filter : ZFSet.{0}) :
    orderFilterValue setStructure conditions order filter ↔
      filter ⊆ conditions ∧ (∃ x, x ∈ filter) ∧
      (∀ x ∈ filter, ∀ y ∈ conditions, ZFSet.pair x y ∈ order → y ∈ filter) ∧
      (∀ x ∈ filter, ∀ y ∈ filter,
        ∃ z ∈ filter, ZFSet.pair z x ∈ order ∧ ZFSet.pair z y ∈ order) := by
  simp [orderFilterValue, subsetValue_set, nonemptyValue_set, or_iff_not_imp_left]
  intro _ _ _
  rfl

theorem meetsFamilyValue_set (filter family : ZFSet.{0}) :
    meetsFamilyValue setStructure filter family ↔
      ∀ denseSet ∈ family, ∃ x ∈ filter, x ∈ denseSet := by
  simp [meetsFamilyValue, or_iff_not_imp_left]
  rfl

theorem martinAxiomAtValue_set (kappa : ZFSet.{0}) :
    martinAxiomAtValue setStructure kappa ↔
      ∀ conditions order family : ZFSet.{0},
        nonemptyValue setStructure conditions →
        partialOrderValue setStructure conditions order →
        countableChainConditionValue setStructure conditions order →
        injectsIntoValue setStructure family kappa →
        (∀ denseSet ∈ family, denseValue setStructure conditions order denseSet) →
        ∃ filter : ZFSet.{0}, orderFilterValue setStructure conditions order filter ∧
          meetsFamilyValue setStructure filter family := by
  simp [martinAxiomAtValue, or_iff_not_imp_left, and_imp]
  rfl

theorem martinAxiomAlephOneValue_set :
    martinAxiomAlephOneValue setStructure ↔ martinAxiomAtValue setStructure kappa := by
  simp only [martinAxiomAlephOneValue, iInf_Prop_eq, sup_Prop_eq]
  change (∀ cardinal : ZFSet.{0}, ¬ omegaOneValue setStructure cardinal ∨
    martinAxiomAtValue setStructure cardinal) ↔ _
  simp only [omegaOneValue_set, or_iff_not_imp_left, not_not]
  constructor
  · intro h
    exact h kappa rfl
  · intro h cardinal hcard
    simpa only [hcard] using h

end Erdos597Object.MartinInSets
