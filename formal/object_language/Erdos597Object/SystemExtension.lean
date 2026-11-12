import Erdos597Object.LimitEmbeddings
import Mathlib.Order.WithBot

set_option backward.isDefEq.respectTransparency false

/-! Adjoining a new last algebra to a coherent Boolean system. -/

namespace Erdos597Object.SystemExtension

open Set Cardinal
open scoped Cardinal
open BooleanDirectLimit IterationCardinals

variable {I : Type} [Preorder I] {B : I → Type}
  [∀ i, CompleteBooleanAlgebra (B i)]
  {C : Type} [CompleteBooleanAlgebra C]

def extendedFamily (B : I → Type) (C : Type) : WithTop I → Type
  | none => C
  | some i => B i

instance extendedAlgebra : (i : WithTop I) → CompleteBooleanAlgebra (extendedFamily B C i)
  | none => inferInstanceAs (CompleteBooleanAlgebra C)
  | some i => inferInstanceAs (CompleteBooleanAlgebra (B i))

theorem extendedFamily_ccc (hB : ∀ i, Flypitch.BA_CCC (B i)) (hC : Flypitch.BA_CCC C) :
    ∀ i, Flypitch.BA_CCC (extendedFamily B C i) := by
  intro i
  cases i with
  | top => exact hC
  | coe i => exact hB i

theorem extendedFamily_card_le (hB : ∀ i, #(B i) ≤ iterationSize)
    (hC : #C ≤ iterationSize) : ∀ i, #(extendedFamily B C i) ≤ iterationSize := by
  intro i
  cases i with
  | top => exact hC
  | coe i => exact hB i

theorem extendedIndex_card_le (hI : #I ≤ iterationSize) : #(WithTop I) ≤ iterationSize :=
  IterationCardinals.option_card_le hI

variable (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
  (legs : ∀ i, CompleteLatticeHom (B i) C)

def extendedMap (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
    (legs : ∀ i, CompleteLatticeHom (B i) C) : ∀ i j : WithTop I, i ≤ j →
    CompleteLatticeHom (extendedFamily B C i) (extendedFamily B C j)
  | none, none, _ => CompleteLatticeHom.id C
  | some i, none, _ => legs i
  | none, some j, h => False.elim (WithTop.not_top_le_coe j h)
  | some i, some j, h => e i j (WithTop.coe_le_coe.mp h)

theorem extendedMap_old (i j : I) (h : i ≤ j) :
    extendedMap e legs (i : WithTop I) (j : WithTop I) (WithTop.coe_le_coe.mpr h) = e i j h :=
  rfl

theorem extendedMap_to_top (i : I) :
    extendedMap e legs (i : WithTop I) ⊤ le_top = legs i := rfl

theorem extendedMap_top : extendedMap e legs ⊤ ⊤ le_rfl = CompleteLatticeHom.id C := rfl

variable [DirectedSystem B (e · · ·)]

theorem extendedDirectedSystem
    (hlegs : ∀ i j (h : i ≤ j) (b : B i), legs j (e i j h b) = legs i b) :
    DirectedSystem (extendedFamily B C) (extendedMap e legs · · ·) where
  map_self := by
    intro i b
    cases i with
    | top => rfl
    | coe i => exact DirectedSystem.map_self' e b
  map_map := by
    intro k j i hij hjk b
    cases i with
    | top =>
        cases j with
        | top =>
            cases k with
            | top => rfl
            | coe k => exact False.elim (WithTop.not_top_le_coe k hjk)
        | coe j => exact False.elim (WithTop.not_top_le_coe j hij)
    | coe i =>
        cases j with
        | top =>
            cases k with
            | top => rfl
            | coe k => exact False.elim (WithTop.not_top_le_coe k hjk)
        | coe j =>
            cases k with
            | top => exact hlegs i j (WithTop.coe_le_coe.mp hij) b
            | coe k => exact (DirectedSystem.map_map' e
                (WithTop.coe_le_coe.mp hij) (WithTop.coe_le_coe.mp hjk) b)

theorem extendedMap_injective
    (hinj : ∀ i j h, Function.Injective (e i j h))
    (hlegs : ∀ i, Function.Injective (legs i)) :
    ∀ i j h, Function.Injective (extendedMap e legs i j h) := by
  intro i j h
  cases i with
  | top =>
      cases j with
      | top => exact fun _ _ hxy => hxy
      | coe j => exact False.elim (WithTop.not_top_le_coe j h)
  | coe i =>
      cases j with
      | top => exact hlegs i
      | coe j => exact hinj i j (WithTop.coe_le_coe.mp h)

section Successor

variable (last : I) (hlast : ∀ i, i ≤ last)
  {L : Type} (Q : BooleanIteration.BooleanPoset (B last) L)

noncomputable def successorLeg (i : I) : CompleteLatticeHom (B i)
    (PosetCompletion.Completion (BooleanIteration.Condition Q)) :=
  (CompletionEmbedding.baseHom Q).comp (e i last (hlast i))

theorem successorLeg_coherent (i j : I) (hij : i ≤ j) (b : B i) :
    successorLeg e last hlast Q j (e i j hij b) = successorLeg e last hlast Q i b := by
  exact congrArg (CompletionEmbedding.baseHom Q) (DirectedSystem.map_map' e hij (hlast j) b)

theorem successorLeg_injective (hinj : ∀ i j h, Function.Injective (e i j h))
    (hQ : (⨆ i, Q.member i) = ⊤) (i : I) :
    Function.Injective (successorLeg e last hlast Q i) :=
  (CompletionEmbedding.baseHom_injective Q hQ).comp (hinj i last (hlast i))

theorem successor_extended_coherent :
    DirectedSystem
      (extendedFamily B (PosetCompletion.Completion (BooleanIteration.Condition Q)))
      (extendedMap e (successorLeg e last hlast Q) · · ·) :=
  extendedDirectedSystem e (successorLeg e last hlast Q)
    (successorLeg_coherent e last hlast Q)

end Successor

section Limit

variable [IsDirectedOrder I] (hinj : ∀ i j h, Function.Injective (e i j h))

theorem limit_extended_coherent :
    DirectedSystem (extendedFamily B (PosetCompletion.Completion (Condition e)))
      (extendedMap e (LimitEmbeddings.stageHom e hinj) · · ·) := by
  apply extendedDirectedSystem
  intro i j hij b
  exact (LimitEmbeddings.stageHom_coherent e hinj hij b).symm

theorem limit_extended_injective : ∀ i j h,
    Function.Injective (extendedMap e (LimitEmbeddings.stageHom e hinj) i j h) :=
  extendedMap_injective e _ hinj (LimitEmbeddings.stageHom_injective e hinj)

end Limit

end Erdos597Object.SystemExtension
