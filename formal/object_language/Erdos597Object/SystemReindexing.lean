import Erdos597Object.ExtensionContinuity

set_option backward.isDefEq.respectTransparency false

/-! Reindexing coherent systems and identifying a one-stage extension with an initial segment. -/

namespace Erdos597Object.SystemReindexing

open Set Order
open ExtensionContinuity

section Pullback

variable {I J : Type} [Preorder I] [Preorder J]
  {B : I → Type} [∀ i, CompleteBooleanAlgebra (B i)]
  (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
  (r : J → I) (hr : Monotone r)

def pullbackMap (i j : J) (hij : i ≤ j) : CompleteLatticeHom (B (r i)) (B (r j)) :=
  e (r i) (r j) (hr hij)

variable [DirectedSystem B (e · · ·)]

theorem pullback_directedSystem : DirectedSystem (fun j => B (r j)) (pullbackMap e r hr · · ·) where
  map_self := by
    intro i b
    exact DirectedSystem.map_self' e b
  map_map := by
    intro k j i hij hjk b
    exact DirectedSystem.map_map' e (hr hij) (hr hjk) b

theorem pullback_injective (hinj : ∀ i j h, Function.Injective (e i j h)) :
    ∀ i j h, Function.Injective (pullbackMap e r hr i j h) :=
  fun i j hij => hinj (r i) (r j) (hr hij)

theorem pullback_ccc (hB : ∀ i, Flypitch.BA_CCC (B i)) :
    ∀ j, Flypitch.BA_CCC (B (r j)) := fun j => hB (r j)

end Pullback

theorem pullback_continuous {I J : Type} [LinearOrder I] [LinearOrder J]
    {B : I → Type} [∀ i, CompleteBooleanAlgebra (B i)]
    (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
    (r : J ≃o I) (hcontinuous : Continuous e) :
    Continuous (pullbackMap e r r.monotone) := by
  intro j hj b hb
  obtain ⟨i, hij, c, hc, hcb⟩ := hcontinuous (r j) (r.isNormal.map_isSuccLimit hj) b hb
  obtain ⟨k, rfl⟩ := r.surjective i
  exact ⟨k, r.lt_iff_lt.mp hij, c, hc, hcb⟩

section InitialSegment

variable {J : Type} [LinearOrder J]

def upperPoint (j : J) : WithTop (Iio j) → Iic j
  | none => ⟨j, le_rfl⟩
  | some i => ⟨i.val, i.property.le⟩

def lowerPoint (j : J) (i : Iic j) : WithTop (Iio j) :=
  if h : i.val < j then (⟨i.val, h⟩ : Iio j) else ⊤

theorem lowerPoint_upperPoint (j : J) (i : WithTop (Iio j)) :
    lowerPoint j (upperPoint j i) = i := by
  cases i with
  | top => simp [lowerPoint, upperPoint]
  | coe i =>
      have hi : i.val < j := i.property
      simp only [upperPoint, lowerPoint, dif_pos hi]

theorem upperPoint_lowerPoint (j : J) (i : Iic j) :
    upperPoint j (lowerPoint j i) = i := by
  rcases i with ⟨i, hi⟩
  by_cases h : i < j
  · simp [lowerPoint, upperPoint, h]
  · have hij : i = j := le_antisymm hi (le_of_not_gt h)
    subst i
    simp [lowerPoint, upperPoint]

def prefixIso (j : J) : WithTop (Iio j) ≃o Iic j where
  toFun := upperPoint j
  invFun := lowerPoint j
  left_inv := lowerPoint_upperPoint j
  right_inv := upperPoint_lowerPoint j
  map_rel_iff' := by
    intro x y
    cases x with
    | top =>
        cases y with
        | top => simp [upperPoint]
        | coe y => simp [upperPoint, not_le.mpr y.property]
    | coe x =>
        cases y with
        | top => simp [upperPoint, x.property.le]
        | coe y => simp [upperPoint]

theorem prefixIso_top (j : J) : prefixIso j ⊤ = ⟨j, le_rfl⟩ := rfl

theorem prefixIso_coe (j : J) (i : Iio j) : prefixIso j i = ⟨i.val, i.property.le⟩ := rfl

end InitialSegment

end Erdos597Object.SystemReindexing
