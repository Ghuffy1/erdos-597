import Erdos597Object.BooleanSets
import Mathlib.Order.Hom.CompleteLattice

set_option backward.isDefEq.respectTransparency false

/-! Transport of Boolean-valued names through complete Boolean homomorphisms. -/

namespace Erdos597Object.BooleanNameTransport

open Flypitch
open scoped Flypitch.bSet

universe u

variable {B C D : Type u} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]
  [CompleteBooleanAlgebra D]

def nameMap (f : CompleteLatticeHom B C) : bSet B → bSet C
  | .mk α children values =>
      .mk α (fun i => nameMap f (children i)) (fun i => f (values i))

theorem nameMap_mk (f : CompleteLatticeHom B C) (α : Type u)
    (children : α → bSet B) (values : α → B) :
    nameMap f (.mk α children values) =
      .mk α (fun i => nameMap f (children i)) (fun i => f (values i)) := rfl

theorem nameMap_type (f : CompleteLatticeHom B C) (x : bSet B) :
    (nameMap f x).type = x.type := by
  cases x
  rfl

theorem nameMap_func (f : CompleteLatticeHom B C) (x : bSet B) (i : x.type) :
    (nameMap f x).func (cast (nameMap_type f x).symm i) = nameMap f (x.func i) := by
  cases x
  rfl

theorem nameMap_bval (f : CompleteLatticeHom B C) (x : bSet B) (i : x.type) :
    (nameMap f x).bval (cast (nameMap_type f x).symm i) = f (x.bval i) := by
  cases x
  rfl

theorem nameMap_id (x : bSet B) : nameMap (CompleteLatticeHom.id B) x = x := by
  induction x with
  | mk α children values ih =>
      dsimp [nameMap]
      congr
      funext i
      exact ih i

theorem nameMap_comp (f : CompleteLatticeHom B C) (g : CompleteLatticeHom C D)
    (x : bSet B) : nameMap (g.comp f) x = nameMap g (nameMap f x) := by
  induction x with
  | mk α children values ih =>
      dsimp [nameMap]
      congr
      funext i
      exact ih i

theorem map_imp (f : CompleteLatticeHom B C) (a b : B) :
    f (lattice.imp a b) = lattice.imp (f a) (f b) := by
  simp only [lattice.imp, map_sup, map_compl']

theorem map_bv_eq (f : CompleteLatticeHom B C) (x y : bSet B) :
    f (x =ᴮ y) = (nameMap f x =ᴮ nameMap f y) := by
  induction x generalizing y with
  | mk α children values ih =>
      cases y with
      | mk β otherChildren otherValues =>
          simp only [bSet.bv_eq, nameMap, map_inf, map_iInf, map_iSup, map_imp, ih]

theorem map_mem (f : CompleteLatticeHom B C) (x y : bSet B) :
    f (x ∈ᴮ y) = (nameMap f x ∈ᴮ nameMap f y) := by
  cases y with
  | mk α children values =>
      simp only [bSet.mem, nameMap, map_iSup, map_inf, map_bv_eq]

theorem map_subset (f : CompleteLatticeHom B C) (x y : bSet B) :
    f (x ⊆ᴮ y) = (nameMap f x ⊆ᴮ nameMap f y) := by
  cases x with
  | mk α children values =>
      simp only [bSet.subset, nameMap, map_iInf, map_imp, map_mem]

theorem nameMap_empty (f : CompleteLatticeHom B C) :
    nameMap f (∅ : bSet B) = ∅ := by
  change bSet.mk PEmpty (fun i => nameMap f (PEmpty.elim i)) (fun i => f (PEmpty.elim i)) =
    bSet.mk PEmpty PEmpty.elim PEmpty.elim
  congr <;> funext i <;> cases i

theorem nameMap_check (f : CompleteLatticeHom B C) (x : pSet.{u}) :
    nameMap f (bSet.check x) = bSet.check x := by
  induction x with
  | mk α children ih =>
      simp only [bSet.check, nameMap, map_top]
      congr
      funext i
      exact ih i

theorem map_le_iff (f : CompleteLatticeHom B C) (hf : Function.Injective f) (a b : B) :
    f a ≤ f b ↔ a ≤ b := by
  rw [← inf_eq_left, ← map_inf, hf.eq_iff, inf_eq_left]

theorem context_bv_eq_iff (f : CompleteLatticeHom B C) (hf : Function.Injective f)
    (Γ : B) (x y : bSet B) :
    f Γ ≤ (nameMap f x =ᴮ nameMap f y) ↔ Γ ≤ (x =ᴮ y) := by
  rw [← map_bv_eq, map_le_iff f hf]

theorem context_mem_iff (f : CompleteLatticeHom B C) (hf : Function.Injective f)
    (Γ : B) (x y : bSet B) :
    f Γ ≤ (nameMap f x ∈ᴮ nameMap f y) ↔ Γ ≤ (x ∈ᴮ y) := by
  rw [← map_mem, map_le_iff f hf]

theorem context_subset_iff (f : CompleteLatticeHom B C) (hf : Function.Injective f)
    (Γ : B) (x y : bSet B) :
    f Γ ≤ (nameMap f x ⊆ᴮ nameMap f y) ↔ Γ ≤ (x ⊆ᴮ y) := by
  rw [← map_subset, map_le_iff f hf]

end Erdos597Object.BooleanNameTransport
