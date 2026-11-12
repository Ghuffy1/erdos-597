import Erdos597Object.SmallMartin
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

set_option backward.isDefEq.respectTransparency false

/-!
Cardinal bounds for enumerating the small forcing requirements.
The chosen cardinal has cofinality greater than aleph-one and is closed under
aleph-one powers. No continuum hypothesis is used in these bounds.
-/

namespace Erdos597Object.IterationCardinals

open Cardinal Set
open scoped Cardinal

noncomputable section

def iterationSize : Cardinal.{0} := 2 ^ ℵ₁

theorem aleph_one_lt_iterationSize : ℵ₁ < iterationSize :=
  Cardinal.cantor ℵ₁

theorem iterationSize_infinite : ℵ₀ ≤ iterationSize :=
  (Cardinal.aleph0_le_aleph 1).trans aleph_one_lt_iterationSize.le

theorem iterationSize_ne_zero : iterationSize ≠ 0 :=
  (Cardinal.aleph0_pos.trans_le iterationSize_infinite).ne'

theorem iterationSize_power_aleph_one : iterationSize ^ ℵ₁ = iterationSize := by
  rw [iterationSize, ← Cardinal.power_mul,
    Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)]

theorem aleph_one_lt_iterationSize_cofinality : ℵ₁ < iterationSize.ord.cof :=
  Cardinal.lt_cof_ord_power (Cardinal.aleph0_le_aleph 1) (by norm_num)

theorem small_range_bounded {I : Type} (hI : #I ≤ ℵ₁)
    (f : I → Ordinal.{0}) (hf : ∀ i, f i < iterationSize.ord) :
    ∃ b < iterationSize.ord, ∀ i, f i < b := by
  refine ⟨⨆ i, f i + 1,
    Ordinal.iSup_add_one_lt_of_lt_cof
      (hI.trans_lt aleph_one_lt_iterationSize_cofinality) hf, ?_⟩
  exact Ordinal.lt_iSup_add_one f

theorem function_card_le {P I : Type} (hP : #P ≤ iterationSize) (hI : #I ≤ ℵ₁) :
    #(I → P) ≤ iterationSize := by
  calc
    #(I → P) = #P ^ #I := by simp only [Cardinal.mk_arrow, Cardinal.lift_id]
    _ ≤ iterationSize ^ #I := Cardinal.power_le_power_right hP
    _ ≤ iterationSize ^ ℵ₁ := Cardinal.power_le_power_left iterationSize_ne_zero hI
    _ = iterationSize := iterationSize_power_aleph_one

theorem predicates_card_le {P : Type} (hP : #P ≤ ℵ₁) :
    #(Set P) ≤ iterationSize := by
  apply function_card_le
  · simpa only [Cardinal.mk_Prop] using
      (show (2 : Cardinal.{0}) ≤ ℵ₀ from Cardinal.natCast_le_aleph0).trans iterationSize_infinite
  · exact hP

theorem relations_card_le {P : Type} (hP : #P ≤ ℵ₁) :
    #(P → P → Prop) ≤ iterationSize :=
  function_card_le (predicates_card_le hP) hP

theorem dense_families_card_le {P I : Type} (hP : #P ≤ ℵ₁) (hI : #I ≤ ℵ₁) :
    #(I → Set P) ≤ iterationSize :=
  function_card_le (predicates_card_le hP) hI

theorem option_card_le {P : Type} (hP : #P ≤ iterationSize) :
    #(Option P) ≤ iterationSize := by
  calc
    #(Option P) = #P + 1 := Cardinal.mk_option
    _ ≤ iterationSize + iterationSize :=
      add_le_add hP (Cardinal.one_le_aleph0.trans iterationSize_infinite)
    _ = iterationSize := Cardinal.add_eq_self iterationSize_infinite

theorem countable_antichain_codes_card_le {P I : Type}
    (hP : #P ≤ iterationSize) (hI : #I ≤ ℵ₁) :
    #(I → ℕ → Option P) ≤ iterationSize := by
  apply function_card_le
  · apply function_card_le (option_card_le hP)
    simpa only [Cardinal.mk_nat] using (Cardinal.aleph0_le_aleph 1)
  · exact hI

end

end Erdos597Object.IterationCardinals
