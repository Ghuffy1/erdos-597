import Erdos597Object.BooleanNameTransport

set_option backward.isDefEq.respectTransparency false

/-! Transport of elementary set constructors and bounded Boolean quantifiers. -/

namespace Erdos597Object.BooleanBoundedTransport

open Flypitch BooleanNameTransport
open scoped Flypitch.bSet

universe u

variable {B C : Type u} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

theorem nameMap_insert (f : CompleteLatticeHom B C) (x y : bSet B) (b : B) :
    nameMap f (bSet.insert x b y) = bSet.insert (nameMap f x) (f b) (nameMap f y) := by
  cases y with
  | mk α children values =>
      dsimp [nameMap, bSet.insert]
      congr <;> funext i <;> cases i <;> rfl

theorem nameMap_insert1 (f : CompleteLatticeHom B C) (x y : bSet B) :
    nameMap f (insert x y) = insert (nameMap f x) (nameMap f y) := by
  change nameMap f (bSet.insert x ⊤ y) = bSet.insert (nameMap f x) ⊤ (nameMap f y)
  rw [nameMap_insert, map_top]

theorem nameMap_singleton (f : CompleteLatticeHom B C) (x : bSet B) :
    nameMap f ({x} : bSet B) = {nameMap f x} := by
  change nameMap f (insert x ∅) = insert (nameMap f x) ∅
  rw [nameMap_insert1, nameMap_empty]

theorem nameMap_pair (f : CompleteLatticeHom B C) (x y : bSet B) :
    nameMap f (bSet.pair x y) = bSet.pair (nameMap f x) (nameMap f y) := by
  simp only [bSet.pair, nameMap_insert1, nameMap_singleton]

theorem nameMap_omega (f : CompleteLatticeHom B C) :
    nameMap f (bSet.omega : bSet B) = bSet.omega :=
  nameMap_check f _

theorem nameMap_ofNat (f : CompleteLatticeHom B C) (n : ℕ) :
    nameMap f (bSet.ofNat n : bSet B) = bSet.ofNat n :=
  nameMap_check f _

theorem map_bounded_forall (f : CompleteLatticeHom B C) (x : bSet B)
    (φ : bSet B → B) (ψ : bSet C → C) (hφ : bSet.B_ext φ) (hψ : bSet.B_ext ψ)
    (hmap : ∀ y, f (φ y) = ψ (nameMap f y)) :
    f (⨅ y : bSet B, lattice.imp (y ∈ᴮ x) (φ y)) =
      ⨅ y : bSet C, lattice.imp (y ∈ᴮ nameMap f x) (ψ y) := by
  rw [← bSet.bounded_forall x φ hφ, ← bSet.bounded_forall (nameMap f x) ψ hψ]
  cases x with
  | mk α children values =>
      simp only [nameMap, bSet.type, bSet.func, bSet.bval, map_iInf, map_imp, hmap]

theorem map_bounded_exists (f : CompleteLatticeHom B C) (x : bSet B)
    (φ : bSet B → B) (ψ : bSet C → C) (hφ : bSet.B_ext φ) (hψ : bSet.B_ext ψ)
    (hmap : ∀ y, f (φ y) = ψ (nameMap f y)) :
    f (⨆ y : bSet B, (y ∈ᴮ x) ⊓ φ y) =
      ⨆ y : bSet C, (y ∈ᴮ nameMap f x) ⊓ ψ y := by
  rw [← bSet.bounded_exists x φ hφ, ← bSet.bounded_exists (nameMap f x) ψ hψ]
  cases x with
  | mk α children values =>
      simp only [nameMap, bSet.type, bSet.func, bSet.bval, map_iSup, map_inf, hmap]

theorem map_nonemptyValue (f : CompleteLatticeHom B C) (x : bSet B) :
    f (nonemptyValue (Flypitch.ZFC.V B) x) =
      nonemptyValue (Flypitch.ZFC.V C) (nameMap f x) := by
  change f (⨆ y : bSet B, y ∈ᴮ x) = ⨆ y : bSet C, y ∈ᴮ nameMap f x
  simpa only [inf_top_eq] using
    map_bounded_exists f x (fun _ => ⊤) (fun _ => ⊤) bSet.B_ext_top bSet.B_ext_top
      (fun _ => map_top f)

theorem map_edgeValue (f : CompleteLatticeHom B C) (relation x y : bSet B) :
    f (edgeValue (Flypitch.ZFC.V B) relation x y) =
      edgeValue (Flypitch.ZFC.V C) (nameMap f relation) (nameMap f x) (nameMap f y) := by
  change f (bSet.pair x y ∈ᴮ relation) =
    (bSet.pair (nameMap f x) (nameMap f y) ∈ᴮ nameMap f relation)
  rw [map_mem, nameMap_pair]

end Erdos597Object.BooleanBoundedTransport
