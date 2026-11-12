import Erdos597Object.IterationSystems
import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData

set_option backward.isDefEq.respectTransparency false

/-! Restriction of continuous Boolean systems to closed initial segments. -/

namespace Erdos597Object.SystemRestrictions

open Set Order CategoryTheory Opposite
open IterationSystems

variable {I J : Type} [LinearOrder I] [LinearOrder J]

theorem reindex_continuous (S : System I) (r : J ≤i I)
    (hS : ExtensionContinuity.Continuous S.map) :
    ExtensionContinuity.Continuous (S.reindex r r.monotone).map := by
  intro j hj b hb
  obtain ⟨i, hij, c, hc, hcb⟩ := hS (r j) (r.isNormal.map_isSuccLimit hj) b hb
  obtain ⟨k, rfl⟩ := r.mem_range_of_rel hij
  exact ⟨k, r.strictMono.lt_iff_lt.mp hij, c, hc, hcb⟩

def prefixInclusion {i j : J} (hij : i ≤ j) : Iic i ≤i Iic j where
  toFun a := ⟨a.val, a.property.trans hij⟩
  inj' := by
    intro a b h
    exact Subtype.ext (congrArg (fun x : Iic j => x.val) h)
  map_rel_iff' := Iff.rfl
  mem_range_of_rel' := by
    intro a b hba
    have hb : b.val ≤ i := (show b.val < a.val from hba).le.trans a.property
    exact ⟨⟨b.val, hb⟩, rfl⟩

def restrict {i j : J} (S : System (Iic j)) (hij : i ≤ j) : System (Iic i) :=
  S.reindex (prefixInclusion hij) (prefixInclusion hij).monotone

theorem restrict_refl {j : J} (S : System (Iic j)) : restrict S le_rfl = S := by
  apply System.ext rfl
  intro i k h
  rfl

theorem restrict_trans {i j k : J} (S : System (Iic k)) (hij : i ≤ j) (hjk : j ≤ k) :
    restrict (restrict S hjk) hij = restrict S (hij.trans hjk) := rfl

theorem restrict_obj {i j : J} (S : System (Iic j)) (hij : i ≤ j) (a : Iic i) :
    (restrict S hij).obj a = S.obj ⟨a.val, a.property.trans hij⟩ := rfl

theorem restrict_map {i j : J} (S : System (Iic j)) (hij : i ≤ j)
    (a b : Iic i) (hab : a ≤ b) :
    (restrict S hij).map a b hab =
      S.map ⟨a.val, a.property.trans hij⟩ ⟨b.val, b.property.trans hij⟩ hab := rfl

theorem restrict_continuous {i j : J} (S : System (Iic j)) (hij : i ≤ j)
    (hS : ExtensionContinuity.Continuous S.map) :
    ExtensionContinuity.Continuous (restrict S hij).map :=
  reindex_continuous S (prefixInclusion hij) hS

structure Prefix (j : J) where
  system : System (Iic j)
  continuous : ExtensionContinuity.Continuous system.map

def Prefix.restrict {i j : J} (S : Prefix j) (hij : i ≤ j) : Prefix i where
  system := SystemRestrictions.restrict S.system hij
  continuous := restrict_continuous S.system hij S.continuous

theorem Prefix.ext {j : J} {S T : Prefix j} (h : S.system = T.system) : S = T := by
  cases S
  cases T
  cases h
  rfl

theorem Prefix.restrict_refl {j : J} (S : Prefix j) : S.restrict le_rfl = S :=
  Prefix.ext (SystemRestrictions.restrict_refl S.system)

theorem Prefix.restrict_trans {i j k : J} (S : Prefix k) (hij : i ≤ j) (hjk : j ≤ k) :
    (S.restrict hjk).restrict hij = S.restrict (hij.trans hjk) := rfl

def prefixFunctor (J : Type) [LinearOrder J] : Jᵒᵖ ⥤ Type 1 where
  obj j := Prefix j.unop
  map f := TypeCat.ofHom (fun S => S.restrict (leOfHom f.unop))
  map_id := by
    intro j
    ext S
    exact S.restrict_refl
  map_comp := by
    intro i j k f g
    ext S
    rfl

end Erdos597Object.SystemRestrictions
