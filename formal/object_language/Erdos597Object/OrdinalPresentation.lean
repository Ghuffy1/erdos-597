import Erdos597Object.SetProducts
import Mathlib.SetTheory.Ordinal.Arithmetic

set_option backward.isDefEq.respectTransparency false

/-! Ordinal products and the constant omega in their set-coded presentations. -/

namespace Erdos597Object.OrdinalPresentation

open Ordinal
open scoped Ordinal Cardinal
open Erdos597Object.SetCodes Erdos597Object.SetFunctions
open Erdos597Object.GraphCopies Erdos597Object.SetProducts

noncomputable section

def initialSegmentEquiv (o : Ordinal.{0}) : Equiv (Set.Iio o) (Members o.toZFSet) :=
  Equiv.ofBijective
    (fun a => ⟨a.val.toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr a.property⟩)
    (by
      constructor
      · intro a b h
        exact Subtype.ext (Ordinal.toZFSet_injective (congrArg Subtype.val h))
      · intro x
        obtain ⟨a, ha, hax⟩ := Ordinal.mem_toZFSet_iff.mp x.property
        exact ⟨⟨a, ha⟩, Subtype.ext hax⟩)

def ordinalEquiv (o : Ordinal.{0}) : Equiv o.ToType (Members o.toZFSet) :=
  Ordinal.ToType.mk.symm.toEquiv.trans (initialSegmentEquiv o)

theorem ordinalEquiv_mem_iff (o : Ordinal.{0}) (a b : o.ToType) :
    (ordinalEquiv o a).val ∈ (ordinalEquiv o b).val ↔ a < b := by
  change (Ordinal.ToType.mk.symm a).val.toZFSet ∈
    (Ordinal.ToType.mk.symm b).val.toZFSet ↔ _
  rw [Ordinal.toZFSet_mem_toZFSet_iff]
  exact Ordinal.ToType.mk.symm.lt_iff_lt

def ordinalRelationIso (o : Ordinal.{0}) :
    ((· < ·) : o.ToType → o.ToType → Prop) ≃r
      (fun a b : Members o.toZFSet => a.val ∈ b.val) where
  toEquiv := ordinalEquiv o
  map_rel_iff' := ordinalEquiv_mem_iff o _ _

def ordinalProductIso (a b : Ordinal.{0}) :
    (Prod.Lex (· < ·) (· < ·) : (a.ToType × b.ToType) → (a.ToType × b.ToType) → Prop) ≃r
      relationOn (ZFSet.prod a.toZFSet b.toZFSet) (lexOrderSet a.toZFSet b.toZFSet) :=
  (RelIso.prodLexCongr (ordinalRelationIso a) (ordinalRelationIso b)).trans
    (productOrderIso a.toZFSet b.toZFSet)

def ordinalProductPresentation (a b : Ordinal.{0}) :
    ((· < ·) : (b * a).ToType → (b * a).ToType → Prop) ≃r
      relationOn (ZFSet.prod a.toZFSet b.toZFSet) (lexOrderSet a.toZFSet b.toZFSet) := by
  let first : ((· < ·) : (b * a).ToType → (b * a).ToType → Prop) ≃r
      (Prod.Lex (· < ·) (· < ·) : (a.ToType × b.ToType) → (a.ToType × b.ToType) → Prop) :=
    Classical.choice (type_eq.mp (by rw [type_toType, type_prod_lex, type_toType, type_toType]))
  exact first.trans (ordinalProductIso a b)

theorem mk_ofNat_eq_naturalSet (n : ℕ) :
    ZFSet.mk (PSet.ofNat n) = naturalSet n := by
  induction n with
  | zero =>
    rw [naturalSet_zero]
    rfl
  | succ n ih =>
    rw [naturalSet_succ]
    change insert (ZFSet.mk (PSet.ofNat n)) (ZFSet.mk (PSet.ofNat n)) = _
    rw [ih]

theorem mem_omega_iff (x : ZFSet.{0}) :
    x ∈ ZFSet.omega ↔ ∃ n : ℕ, naturalSet n = x := by
  induction x using Quotient.inductionOn with
  | h x =>
    change ZFSet.mk x ∈ ZFSet.mk PSet.omega ↔ _
    rw [ZFSet.mk_mem_iff]
    change (∃ n : ULift ℕ, PSet.Equiv x (PSet.ofNat n.down)) ↔ _
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n.down, (mk_ofNat_eq_naturalSet n.down).symm.trans (ZFSet.sound hn).symm⟩
    · rintro ⟨n, hn⟩
      exact ⟨⟨n⟩, ZFSet.exact ((mk_ofNat_eq_naturalSet n).trans hn).symm⟩

theorem omega_toZFSet : (ω : Ordinal.{0}).toZFSet = ZFSet.omega := by
  apply ZFSet.ext
  intro x
  rw [Ordinal.mem_toZFSet_iff, mem_omega_iff]
  constructor
  · rintro ⟨a, ha, hax⟩
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp ha
    exact ⟨n, hax⟩
  · rintro ⟨n, hnx⟩
    exact ⟨n, Ordinal.natCast_lt_omega0 n, hnx⟩

end

end Erdos597Object.OrdinalPresentation
