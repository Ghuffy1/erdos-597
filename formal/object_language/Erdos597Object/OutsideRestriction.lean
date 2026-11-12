import Erdos597Object.CodedDensity

set_option backward.isDefEq.respectTransparency false

/-! Restrict filter coefficients from the completed poset to the original Boolean context. -/

namespace Erdos597Object.OutsideRestriction

open BooleanIteration ContextCompletion CodedDensity

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem restricted_cover (context : B) (P : BooleanPoset B I) (weight : Option I → B)
    (hvalid : ∀ i, weight i ≤ (withOutside context P).member i)
    (hcover : (⨆ i, weight i) = ⊤) : context ≤ ⨆ i, weight (some i) := by
  have htotal : weight none ⊔ (⨆ i, weight (some i)) = ⊤ :=
    (iSup_option weight).symm.trans hcover
  have hzero : context ⊓ weight none = ⊥ := by
    apply bot_unique
    exact (le_inf inf_le_left (inf_le_right.trans (hvalid none))).trans_eq (inf_compl_eq_bot)
  calc
    context = context ⊓ (weight none ⊔ (⨆ i, weight (some i))) := by rw [htotal, inf_top_eq]
    _ = (context ⊓ weight none) ⊔ (context ⊓ (⨆ i, weight (some i))) := inf_sup_left _ _ _
    _ ≤ _ := by rw [hzero, bot_sup_eq]; exact inf_le_right

theorem restricted_upward (context : B) (P : BooleanPoset B I) (weight : Option I → B)
    (hup : ∀ i j, weight i ⊓ (withOutside context P).leValue i j ≤ weight j) (i j : I) :
    weight (some i) ⊓ P.leValue i j ≤ weight (some j) := hup (some i) (some j)

theorem restricted_directed (context : B) (P : BooleanPoset B I) (weight : Option I → B)
    (hdir : ∀ i j, weight i ⊓ weight j ≤ ⨆ k, weight k ⊓
      ((withOutside context P).leValue k i ⊓ (withOutside context P).leValue k j)) (i j : I) :
    weight (some i) ⊓ weight (some j) ≤ ⨆ k, weight (some k) ⊓
      (P.leValue k i ⊓ P.leValue k j) := by
  simpa only [iSup_option, withOutside, inf_bot_eq, bot_inf_eq, bot_sup_eq] using! hdir (some i) (some j)

theorem restricted_meets (context active : B) (P : BooleanPoset B I)
    (weight : Option I → B) (dense : I → B) (hactive : active ≤ context)
    (hmeets : (⨆ i, weight i ⊓ outsideDense context active P dense i) = ⊤) :
    active ≤ ⨆ i, weight (some i) ⊓ dense i := by
  have h : active ≤ active ⊓ (⨆ i, weight i ⊓ outsideDense context active P dense i) := by
    rw [hmeets, inf_top_eq]
  rw [inf_iSup_eq] at h
  apply h.trans
  apply iSup_le
  intro i
  cases i with
  | none =>
    have hbot : active ⊓ (weight none ⊓ contextᶜ) ≤ context ⊓ contextᶜ :=
      le_inf (inf_le_left.trans hactive) (inf_le_right.trans inf_le_right)
    exact (hbot.trans_eq inf_compl_eq_bot).trans bot_le
  | some i =>
    apply le_iSup_of_le i
    change active ⊓ (weight (some i) ⊓ ((activeᶜ ⊓ P.member i) ⊔ dense i)) ≤ _
    rw [← inf_assoc, inf_sup_left]
    apply sup_le
    · have hbot : (active ⊓ weight (some i)) ⊓ (activeᶜ ⊓ P.member i) ≤ active ⊓ activeᶜ :=
        le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
      exact (hbot.trans_eq inf_compl_eq_bot).trans bot_le
    · exact le_inf (inf_le_left.trans inf_le_right) inf_le_right

end Erdos597Object.OutsideRestriction
