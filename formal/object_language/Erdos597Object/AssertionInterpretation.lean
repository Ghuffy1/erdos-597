import Erdos597Object.AssertionSemantics
import Erdos597Object.FirstUncountable

set_option backward.isDefEq.respectTransparency false

/-! The complete first-order sentence in the ordinary set interpretation. -/

namespace Erdos597Object.AssertionInterpretation

open Cardinal Ordinal Flypitch Flypitch.fol Flypitch.fol.bfol
open Erdos597Object.SetInterpretation Erdos597Object.SetProducts
open Erdos597Object.PartitionInterpretation Erdos597Object.FirstUncountable
open Erdos597Object.OriginalPartition
open scoped Cardinal Ordinal

theorem lexOrderValue_product_iff (left right order : ZFSet.{0}) :
    lexOrderValue setStructure (ZFSet.prod left right) order ↔
      order = lexOrderSet left right := by
  constructor
  · intro h
    obtain ⟨hbetween, horder⟩ := (lexOrderValue_set _ _).mp h
    apply ZFSet.ext
    intro entry
    constructor
    · intro hentry
      obtain ⟨x, hx, y, hy, rfl⟩ := (relationBetweenValue_set _ _ _).mp hbetween entry hentry
      exact (pair_mem_lexOrderSet left right x y).mpr
        ⟨hx, hy, (horder x hx y hy).mp hentry⟩
    · intro hentry
      obtain ⟨x, hx, y, hy, rfl, hless⟩ := ZFSet.mem_pairSep.mp hentry
      exact (horder x hx y hy).mpr hless
  · rintro rfl
    exact lexOrderSet_spec left right

theorem finiteAssertionValue_set_raw :
    finiteAssertionValue setStructure ↔
      ∀ kappa host redDomain hostOrder redOrder : ZFSet.{0},
        omegaOneValue setStructure kappa →
        cartesianProductValue setStructure kappa kappa host →
        cartesianProductValue setStructure ZFSet.omega kappa redDomain →
        lexOrderValue setStructure host hostOrder →
        lexOrderValue setStructure redDomain redOrder →
        finitePartitionValue setStructure host redDomain hostOrder redOrder := by
  simp [finiteAssertionValue, or_iff_not_imp_left]
  rfl

theorem finiteAssertionValue_set_iff :
    finiteAssertionValue setStructure ↔
      finitePartitionValue setStructure (ZFSet.prod kappa kappa) (ZFSet.prod ZFSet.omega kappa)
        (lexOrderSet kappa kappa) (lexOrderSet ZFSet.omega kappa) := by
  rw [finiteAssertionValue_set_raw]
  constructor
  · intro h
    exact h kappa _ _ _ _ ((omegaOneValue_set _).mpr rfl)
      ((cartesianProductValue_iff _ _ _).mpr rfl)
      ((cartesianProductValue_iff _ _ _).mpr rfl)
      (lexOrderSet_spec _ _) (lexOrderSet_spec _ _)
  · intro h cardinal host redDomain hostOrder redOrder hcard hhost hred hhostOrder hredOrder
    have hcardEq : cardinal = kappa := (omegaOneValue_set cardinal).mp hcard
    subst cardinal
    have hhostEq := (cartesianProductValue_iff _ _ _).mp hhost
    have hredEq := (cartesianProductValue_iff _ _ _).mp hred
    subst host
    subst redDomain
    have hhostOrderEq := (lexOrderValue_product_iff _ _ _).mp hhostOrder
    have hredOrderEq := (lexOrderValue_product_iff _ _ _).mp hredOrder
    subst hostOrder
    subst redOrder
    exact h

theorem finiteAssertion_set_iff_original :
    boolean_realize_sentence setStructure finiteAssertion ↔
      ∀ n (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
        Erdos597.OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ)) ((ω₁ : Ordinal.{0}) * ω) G := by
  rw [realize_finiteAssertion, finiteAssertionValue_set_iff, canonical_partition_iff_original]

theorem finiteAssertion_under_MA (hMA : Erdos597.MartinAxiomAlephOne) :
    boolean_realize_sentence setStructure finiteAssertion := by
  rw [realize_finiteAssertion, finiteAssertionValue_set_iff]
  exact canonical_partition_under_MA hMA

theorem finiteAssertion_fails_under_CH (hCH : (2 : Cardinal.{0}) ^ ℵ₀ = ℵ₁) :
    ¬ boolean_realize_sentence setStructure finiteAssertion := by
  rw [realize_finiteAssertion, finiteAssertionValue_set_iff]
  exact canonical_partition_fails_under_CH hCH

end Erdos597Object.AssertionInterpretation
