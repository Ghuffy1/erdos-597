import Erdos597Object.SetPosets

set_option backward.isDefEq.respectTransparency false

/-! Encode small partial orders and indexed families as sets. -/

namespace Erdos597Object.PosetEncoding

open Cardinal Ordinal
open scoped Cardinal Ordinal
open Erdos597Object.SetFunctions Erdos597Object.SetInterpretation
open Erdos597Object.SetSubsets Erdos597Object.SetPosets
open Erdos597Object.MartinInSets Erdos597Object.FirstUncountable
open Erdos597Object.OrdinalPresentation

noncomputable section

def orderCode (P : Type) [PartialOrder P] : ZFSet.{0} :=
  ZFSet.range fun p : {xy : P × P // xy.1 ≤ xy.2} =>
    ZFSet.pair (typeEquiv P p.val.1).val (typeEquiv P p.val.2).val

theorem pair_mem_orderCode (P : Type) [PartialOrder P] (x y : P) :
    ZFSet.pair (typeEquiv P x).val (typeEquiv P y).val ∈ orderCode P ↔ x ≤ y := by
  constructor
  · intro h
    obtain ⟨⟨⟨a, b⟩, hab⟩, hp⟩ := ZFSet.mem_range.mp h
    obtain ⟨ha, hb⟩ := ZFSet.pair_inj.mp hp
    have hax : a = x := (typeEquiv P).injective (Subtype.ext ha)
    have hby : b = y := (typeEquiv P).injective (Subtype.ext hb)
    simpa only [hax, hby] using hab
  · intro h
    exact ZFSet.mem_range.mpr ⟨⟨(x, y), h⟩, rfl⟩

theorem orderCode_partialOrder (P : Type) [PartialOrder P] :
    partialOrderValue setStructure (typeCode P) (orderCode P) := by
  rw [partialOrderValue_set]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [relationBetweenValue_set]
    intro entry hentry
    obtain ⟨p, rfl⟩ := ZFSet.mem_range.mp hentry
    exact ⟨_, (typeEquiv P p.val.1).property, _, (typeEquiv P p.val.2).property, rfl⟩
  · intro x hx
    obtain ⟨p, hp⟩ := (typeEquiv P).surjective ⟨x, hx⟩
    have hpv := congrArg Subtype.val hp
    simpa only [hpv] using (pair_mem_orderCode P p p).mpr le_rfl
  · intro x hx y hy hxy hyx
    obtain ⟨p, hp⟩ := (typeEquiv P).surjective ⟨x, hx⟩
    obtain ⟨q, hq⟩ := (typeEquiv P).surjective ⟨y, hy⟩
    have hpv := congrArg Subtype.val hp
    have hqv := congrArg Subtype.val hq
    have hpq : p ≤ q := (pair_mem_orderCode P p q).mp (by simpa only [hpv, hqv] using hxy)
    have hqp : q ≤ p := (pair_mem_orderCode P q p).mp (by simpa only [hpv, hqv] using hyx)
    exact hpv.symm.trans ((congrArg (fun p => (typeEquiv P p).val) (le_antisymm hpq hqp)).trans hqv)
  · intro x hx y hy z hz hxy hyz
    obtain ⟨p, hp⟩ := (typeEquiv P).surjective ⟨x, hx⟩
    obtain ⟨q, hq⟩ := (typeEquiv P).surjective ⟨y, hy⟩
    obtain ⟨r, hr⟩ := (typeEquiv P).surjective ⟨z, hz⟩
    have hpv := congrArg Subtype.val hp
    have hqv := congrArg Subtype.val hq
    have hrv := congrArg Subtype.val hr
    have hpq : p ≤ q := (pair_mem_orderCode P p q).mp (by simpa only [hpv, hqv] using hxy)
    have hqr : q ≤ r := (pair_mem_orderCode P q r).mp (by simpa only [hqv, hrv] using hyz)
    simpa only [hpv, hrv] using (pair_mem_orderCode P p r).mpr (hpq.trans hqr)

def typeOrderIso (P : Type) [PartialOrder P] :
    letI orderInstance : PartialOrder (Members (typeCode P)) := decodedPartialOrder (orderCode_partialOrder P)
    letI : Preorder (Members (typeCode P)) := orderInstance.toPreorder
    letI : LE (Members (typeCode P)) := orderInstance.toLE
    letI : LT (Members (typeCode P)) := orderInstance.toLT
    P ≃o Members (typeCode P) := by
  letI orderInstance : PartialOrder (Members (typeCode P)) := decodedPartialOrder (orderCode_partialOrder P)
  letI : Preorder (Members (typeCode P)) := orderInstance.toPreorder
  letI : LE (Members (typeCode P)) := orderInstance.toLE
  letI : LT (Members (typeCode P)) := orderInstance.toLT
  exact { toEquiv := typeEquiv P, map_rel_iff' := pair_mem_orderCode P _ _ }

def familyCode {conditions : ZFSet.{0}} {I : Type} (D : I → Set (Members conditions)) : ZFSet.{0} :=
  ZFSet.range fun i => subsetCode conditions (D i)

def familyIndex {conditions : ZFSet.{0}} {I : Type} (D : I → Set (Members conditions))
    (i : I) : Members (familyCode D) :=
  ⟨subsetCode conditions (D i), ZFSet.mem_range.mpr ⟨i, rfl⟩⟩

theorem familyIndex_surjective {conditions : ZFSet.{0}} {I : Type}
    (D : I → Set (Members conditions)) : Function.Surjective (familyIndex D) := by
  intro x
  obtain ⟨i, hi⟩ := ZFSet.mem_range.mp x.property
  exact ⟨i, Subtype.ext hi⟩

theorem familyCode_injectsInto_omegaOne {conditions : ZFSet.{0}} {I : Type}
    (D : I → Set (Members conditions)) (hI : #I ≤ ℵ₁) :
    injectsIntoValue setStructure (familyCode D) (ω₁ : Ordinal.{0}).toZFSet := by
  have hcard : #I ≤ #((ω₁ : Ordinal.{0}).ToType) := by simpa using hI
  obtain ⟨f⟩ := (Cardinal.le_def _ _).mp hcard
  let g := Function.Embedding.ofSurjective (familyIndex D) (familyIndex_surjective D)
  exact (injectsIntoValue_set _ _).mpr
    ⟨(g.trans f).trans (ordinalEquiv (ω₁ : Ordinal.{0})).toEmbedding⟩

end

end Erdos597Object.PosetEncoding
