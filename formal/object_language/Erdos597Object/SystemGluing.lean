import Erdos597Object.SystemRestrictions

set_option backward.isDefEq.respectTransparency false

/-! Gluing exactly compatible initial-segment systems. -/

namespace Erdos597Object.SystemGluing

open Set IterationSystems SystemRestrictions

def castHom {A B : Algebra} (h : A = B) : CompleteLatticeHom A B := by
  cases h
  exact CompleteLatticeHom.id A

def transportMap {A A' B B' : Algebra} (hA : A = A') (hB : B = B')
    (f : CompleteLatticeHom A B) : CompleteLatticeHom A' B' :=
  (castHom hB).comp (f.comp (castHom hA.symm))

theorem transportMap_heq {A A' B B' : Algebra} (hA : A = A') (hB : B = B')
    (f : CompleteLatticeHom A B) : HEq (transportMap hA hB f) f := by
  cases hA
  cases hB
  rfl

theorem transportMap_injective {A A' B B' : Algebra} (hA : A = A') (hB : B = B')
    (f : CompleteLatticeHom A B) (hf : Function.Injective f) :
    Function.Injective (transportMap hA hB f) := by
  cases hA
  cases hB
  exact hf

theorem transportMap_comp {A A' B B' C C' : Algebra}
    (hA : A = A') (hB : B = B') (hC : C = C')
    (f : CompleteLatticeHom A B) (g : CompleteLatticeHom B C) :
    (transportMap hB hC g).comp (transportMap hA hB f) =
      transportMap hA hC (g.comp f) := by
  cases hA
  cases hB
  cases hC
  rfl

theorem system_map_heq {I : Type} [Preorder I] {S T : System I} (h : S = T)
    (i j : I) (hij : i ≤ j) : HEq (S.map i j hij) (T.map i j hij) := by
  cases h
  rfl

variable {J : Type} [LinearOrder J] {U : Set J}
  (S : ∀ i : U, System (Iic i.val))
  (hS : ∀ (i j : U) (hij : i ≤ j), restrict (S j) hij = S i)

def object (i : U) : Algebra := (S i).obj ⟨i.val, le_rfl⟩

include hS in
theorem object_eq_at (i j : U) (hij : i ≤ j) :
    (S j).obj ⟨i.val, hij⟩ = object S i :=
  congrArg (fun T : System (Iic i.val) => T.obj ⟨i.val, le_rfl⟩) (hS i j hij)

def glueMap (i j : U) (hij : i ≤ j) : CompleteLatticeHom (object S i) (object S j) :=
  transportMap (object_eq_at S hS i j hij) rfl
    ((S j).map ⟨i.val, hij⟩ ⟨j.val, le_rfl⟩ hij)

theorem glueMap_at (i j k : U) (hij : i ≤ j) (hjk : j ≤ k) :
    glueMap S hS i j hij =
      transportMap (object_eq_at S hS i k (hij.trans hjk)) (object_eq_at S hS j k hjk)
        ((S k).map ⟨i.val, hij.trans hjk⟩ ⟨j.val, hjk⟩ hij) := by
  have hm := system_map_heq (hS j k hjk) ⟨i.val, hij⟩ ⟨j.val, le_rfl⟩ hij
  apply eq_of_heq
  exact (transportMap_heq (object_eq_at S hS i j hij) rfl _).trans
    (hm.symm.trans (transportMap_heq (object_eq_at S hS i k (hij.trans hjk))
      (object_eq_at S hS j k hjk) _).symm)

theorem glueMap_self (i : U) (b : object S i) : glueMap S hS i i le_rfl b = b := by
  change (S i).map ⟨i.val, le_rfl⟩ ⟨i.val, le_rfl⟩ le_rfl b = b
  exact DirectedSystem.map_self' (S i).map b

theorem glueMap_comp (i j k : U) (hij : i ≤ j) (hjk : j ≤ k) :
    (glueMap S hS j k hjk).comp (glueMap S hS i j hij) =
      glueMap S hS i k (hij.trans hjk) := by
  rw [glueMap_at S hS i j k hij hjk]
  change (transportMap (object_eq_at S hS j k hjk) rfl
      ((S k).map ⟨j.val, hjk⟩ ⟨k.val, le_rfl⟩ hjk)).comp
      (transportMap (object_eq_at S hS i k (hij.trans hjk)) (object_eq_at S hS j k hjk)
      ((S k).map ⟨i.val, hij.trans hjk⟩ ⟨j.val, hjk⟩ hij)) =
      transportMap (object_eq_at S hS i k (hij.trans hjk)) rfl
      ((S k).map ⟨i.val, hij.trans hjk⟩ ⟨k.val, le_rfl⟩ (hij.trans hjk))
  rw [transportMap_comp]
  congr 1
  ext b
  exact DirectedSystem.map_map' (S k).map
    (show (⟨i.val, hij.trans hjk⟩ : Iic k.val) ≤ ⟨j.val, hjk⟩ from hij)
    (show (⟨j.val, hjk⟩ : Iic k.val) ≤ ⟨k.val, le_rfl⟩ from hjk) b

def glue : System U where
  obj := object S
  map := glueMap S hS
  coherent := {
    map_self := glueMap_self S hS
    map_map := by
      intro k j i hij hjk b
      exact DFunLike.congr_fun (glueMap_comp S hS i j k hij hjk) b }
  injective := fun i j hij => transportMap_injective _ _ _ ((S j).injective _ _ _)

def prefixLift (hU : IsLowerSet U) (i : U) (a : Iic i.val) : U :=
  ⟨a.val, hU a.property i.property⟩

theorem prefixLift_monotone (hU : IsLowerSet U) (i : U) : Monotone (prefixLift hU i) :=
  fun _ _ h => h

theorem glue_restrict (hU : IsLowerSet U) (i : U) :
    (glue S hS).reindex (prefixLift hU i) (prefixLift_monotone hU i) = S i := by
  apply System.ext
    (funext (fun a => (object_eq_at S hS (prefixLift hU i a) i a.property).symm))
  intro a b hab
  change HEq (glueMap S hS (prefixLift hU i a) (prefixLift hU i b) hab)
    ((S i).map a b hab)
  exact (heq_of_eq (glueMap_at S hS (prefixLift hU i a) (prefixLift hU i b) i
    hab b.property)).trans (transportMap_heq _ _ _)

def subtypeInitial (hU : IsLowerSet U) : U ≤i J where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl
  mem_range_of_rel' := fun a b hba => ⟨⟨b, hU hba.le a.property⟩, rfl⟩

theorem glue_continuous (hU : IsLowerSet U)
    (hcontinuous : ∀ i, ExtensionContinuity.Continuous (S i).map) :
    ExtensionContinuity.Continuous (glue S hS).map := by
  intro i hi b hb
  have hlocal : ExtensionContinuity.Continuous
      ((glue S hS).reindex (prefixLift hU i) (prefixLift_monotone hU i)).map := by
    rw [glue_restrict S hS hU i]
    exact hcontinuous i
  have htop : Order.IsSuccLimit (⟨i.val, le_rfl⟩ : Iic i.val) :=
    (subtypeInitial (isLowerSet_Iic i.val)).isSuccLimit_apply_iff.mp (hi.subtypeVal hU)
  obtain ⟨j, hji, c, hc, hcb⟩ := hlocal ⟨i.val, le_rfl⟩ htop b hb
  exact ⟨prefixLift hU i j, hji, c, hc, hcb⟩

end Erdos597Object.SystemGluing
