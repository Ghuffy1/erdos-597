import Erdos597Object.SystemExtension
import Erdos597Object.CofinalSequences

set_option backward.isDefEq.respectTransparency false

/-! Continuity is preserved by the successor and limit extension constructions. -/

namespace Erdos597Object.ExtensionContinuity

open Set Order
open SystemExtension BooleanDirectLimit

variable {I : Type} [Preorder I] {B : I → Type}
  [∀ i, CompleteBooleanAlgebra (B i)]

def Continuous (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j)) : Prop :=
  ∀ i, IsSuccLimit i → ∀ b : B i, b ≠ ⊥ →
    ∃ (j : I) (hji : j < i) (c : B j), c ≠ ⊥ ∧ e j i hji.le c ≤ b

theorem not_isSuccLimit_top_of_last (last : I) (hlast : ∀ i, i ≤ last) :
    ¬ IsSuccLimit (⊤ : WithTop I) := by
  intro hlimit
  apply hlimit.isSuccPrelimit (last : WithTop I)
  refine ⟨WithTop.coe_lt_top last, ?_⟩
  intro x hlastx hxtop
  cases x with
  | top => exact (lt_irrefl (⊤ : WithTop I)) hxtop
  | coe x => exact (WithTop.coe_lt_coe.mp hlastx).not_ge (hlast x)

theorem extended_continuous {C : Type} [CompleteBooleanAlgebra C]
    (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
    (legs : ∀ i, CompleteLatticeHom (B i) C) (hcontinuous : Continuous e)
    (htop : IsSuccLimit (⊤ : WithTop I) →
      ∀ c : C, c ≠ ⊥ → ∃ (i : I) (b : B i), b ≠ ⊥ ∧ legs i b ≤ c) :
    Continuous (extendedMap e legs) := by
  intro i hi b hb
  cases i with
  | top =>
      obtain ⟨j, c, hc, hcb⟩ := htop hi b hb
      exact ⟨j, WithTop.coe_lt_top j, c, hc, hcb⟩
  | coe i =>
      obtain ⟨j, hji, c, hc, hcb⟩ := hcontinuous i (WithTop.isSuccLimit_coe_iff.mp hi) b hb
      exact ⟨j, WithTop.coe_lt_coe.mpr hji, c, hc, hcb⟩

variable (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
  [DirectedSystem B (e · · ·)]

theorem successor_continuous (last : I) (hlast : ∀ i, i ≤ last)
    {L : Type} (Q : BooleanIteration.BooleanPoset (B last) L)
    (hcontinuous : Continuous e) :
    Continuous (extendedMap e (successorLeg e last hlast Q)) := by
  apply extended_continuous e _ hcontinuous
  intro hlimit
  exact False.elim (not_isSuccLimit_top_of_last last hlast hlimit)

theorem limit_continuous [IsDirectedOrder I]
    (hinj : ∀ i j h, Function.Injective (e i j h)) (hcontinuous : Continuous e) :
    Continuous (extendedMap e (LimitEmbeddings.stageHom e hinj)) := by
  apply extended_continuous e _ hcontinuous
  intro _ c hc
  exact LimitEmbeddings.stageHom_dense e hinj c hc

theorem limit_algebra_ccc {J : Type} [LinearOrder J] [WellFoundedLT J]
    {A : J → Type} [∀ j, CompleteBooleanAlgebra (A j)]
    (f : ∀ i j, i ≤ j → CompleteLatticeHom (A i) (A j))
    [DirectedSystem A (f · · ·)]
    (hinj : ∀ i j h, Function.Injective (f i j h))
    (hA : ∀ j, Flypitch.BA_CCC (A j)) (hcontinuous : Continuous f) :
    Flypitch.BA_CCC (PosetCompletion.Completion (Condition f)) :=
  CofinalSequences.completion_ccc_of_continuity f hinj hA hcontinuous

end Erdos597Object.ExtensionContinuity
