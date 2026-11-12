import Erdos597Object.ContextualCCC

set_option backward.isDefEq.respectTransparency false

/-! Complete a contextual Boolean poset with an isolated condition on the complementary context. -/

namespace Erdos597Object.ContextCompletion

open BooleanIteration

variable {B I : Type} [CompleteBooleanAlgebra B]

def withOutside (context : B) (P : BooleanPoset B I) : BooleanPoset B (Option I) where
  member label := match label with
    | none => contextᶜ
    | some i => P.member i
  leValue left right := match left, right with
    | none, none => contextᶜ
    | some i, some j => P.leValue i j
    | _, _ => ⊥
  le_members := by
    intro i j
    cases i <;> cases j
    · simp
    · exact bot_le
    · exact bot_le
    · exact P.le_members _ _
  reflexive := by
    intro i
    cases i <;> simp
    exact P.reflexive _
  transitive := by
    intro i j k
    cases i <;> cases j <;> cases k <;> simp
    exact P.transitive _ _ _
  antisymmetric := by
    intro i j hij
    cases i <;> cases j <;> simp_all
    exact P.antisymmetric _ _ hij

@[simp] theorem compatible_none_none (context : B) (P : BooleanPoset B I) :
    BooleanIteration.compatibleValue (withOutside context P) none none = contextᶜ := by
  simp [BooleanIteration.compatibleValue, withOutside, iSup_option]

@[simp] theorem compatible_some_some (context : B) (P : BooleanPoset B I) (i j : I) :
    BooleanIteration.compatibleValue (withOutside context P) (some i) (some j) = BooleanIteration.compatibleValue P i j := by
  simp [BooleanIteration.compatibleValue, withOutside, iSup_option]

@[simp] theorem compatible_none_some (context : B) (P : BooleanPoset B I) (i : I) :
    BooleanIteration.compatibleValue (withOutside context P) none (some i) = ⊥ := by
  simp [BooleanIteration.compatibleValue, withOutside, iSup_option]

@[simp] theorem compatible_some_none (context : B) (P : BooleanPoset B I) (i : I) :
    BooleanIteration.compatibleValue (withOutside context P) (some i) none = ⊥ := by
  simp [BooleanIteration.compatibleValue, withOutside, iSup_option]

theorem withOutside_cover (context : B) (P : BooleanPoset B I)
    (hcover : (⨆ i, P.member i) = context) :
    (⨆ i, (withOutside context P).member i) = ⊤ := by
  simp [withOutside, iSup_option, hcover]

theorem withOutside_booleanCCC [Nonempty I] (context : B) (P : BooleanPoset B I)
    (hP : BooleanCountableChainCondition P) :
    BooleanCountableChainCondition (withOutside context P) := by
  classical
  intro J label values hvalues hincompatible
  let insideLabel : J → I := fun j => (label j).getD Classical.ofNonempty
  let insideWeight : J → B := fun j => match label j with
    | none => ⊥
    | some _ => values j
  have hvalid : ∀ j, insideWeight j ≤ P.member (insideLabel j) := by
    intro j
    cases hj : label j with
    | none => simp [insideWeight, hj]
    | some i => simpa [insideWeight, insideLabel, hj, withOutside] using hvalues j
  have hinside : ∀ j k, j ≠ k → insideWeight j ⊓ insideWeight k ⊓
      BooleanIteration.compatibleValue P (insideLabel j) (insideLabel k) = ⊥ := by
    intro j k hjk
    cases hj : label j <;> cases hk : label k
    · simp [insideWeight, hj]
    · simp [insideWeight, hj]
    · simp [insideWeight, hk]
    · simpa [insideWeight, insideLabel, hj, hk] using hincompatible j k hjk
  obtain ⟨insideRows, hrows, hcover⟩ := hP J insideLabel insideWeight hvalid hinside
  let rows : ℕ → J → B := fun n j => match n with
    | 0 => match label j with
      | none => values j
      | some _ => ⊥
    | n + 1 => insideRows n j
  refine ⟨rows, ?_, ?_⟩
  · intro n j k hjk
    cases n with
    | zero =>
      cases hj : label j <;> cases hk : label k
      · have hbound : values j ⊓ values k ≤ contextᶜ :=
          inf_le_left.trans (by simpa [withOutside, hj] using hvalues j)
        have hzero := hincompatible j k hjk
        simpa [rows, hj, hk, inf_eq_left.mpr hbound] using hzero
      · simp [rows, hj, hk]
      · simp [rows, hj, hk]
      · simp [rows, hj, hk]
    | succ n => simpa [rows] using hrows n j k hjk
  · intro j
    cases hj : label j with
    | none => exact le_iSup_of_le 0 (by simp [rows, hj])
    | some i =>
      have h := hcover j
      simp only [insideWeight, hj] at h
      exact h.trans (iSup_le fun n => le_iSup_of_le (n + 1) (by simp [rows]))

theorem withOutside_ccc [Nonempty I] (hB : Flypitch.BA_CCC B)
    (context : B) (P : BooleanPoset B I) (hP : BooleanCountableChainCondition P) :
    MartinTransport.CountableChainCondition (Condition (withOutside context P)) :=
  two_step_ccc hB _ (withOutside_booleanCCC context P hP)

end Erdos597Object.ContextCompletion
