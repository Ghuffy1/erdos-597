import Erdos597Object.CHSemantics
import Erdos597Object.SetSubsets

set_option backward.isDefEq.respectTransparency false

/-! Partial surjections and powersets in the ordinary set interpretation. -/

namespace Erdos597Object.CHInSets

open Erdos597Object.SetInterpretation Erdos597Object.SetFunctions
open Erdos597Object.SetSubsets Erdos597Object.FirstUncountable Erdos597Object.OrdinalsInSets

noncomputable section

@[simp] theorem powersetValue_set (x : ZFSet.{0}) :
    powersetValue setStructure x = ZFSet.powerset x := rfl

theorem functionalityValue_set (relation : ZFSet.{0}) :
    functionalityValue setStructure relation ↔ singleValuedValue setStructure relation := by
  rw [singleValuedValue_set]
  simp [functionalityValue, or_iff_not_imp_left, and_imp]
  constructor
  · intro h x y z hxy hxz
    exact h x x y z hxy hxz rfl
  · intro h x y a b hxa hyb hxy
    subst y
    exact h x a b hxa hyb

theorem surjectiveOnValue_set (domain codomain relation : ZFSet.{0}) :
    surjectiveOnValue setStructure domain codomain relation ↔
      ∀ y ∈ codomain, ∃ x ∈ domain, ZFSet.pair x y ∈ relation := by
  simp [surjectiveOnValue, or_iff_not_imp_left]
  rfl

theorem surjectsSubsetValue_set (domain codomain : ZFSet.{0}) :
    surjectsSubsetValue setStructure domain codomain ↔
      ∃ subset relation : ZFSet.{0}, subset ⊆ domain ∧
        singleValuedValue setStructure relation ∧
        totalOnValue setStructure subset codomain relation ∧
        surjectiveOnValue setStructure subset codomain relation := by
  simp [surjectsSubsetValue, subsetValue_set, functionalityValue_set, and_assoc]
  rfl

def inverseEmbeddingGraph {domain codomain : ZFSet.{0}}
    (f : Members codomain ↪ Members domain) : ZFSet.{0} :=
  ZFSet.range fun y : Members codomain => ZFSet.pair (f y).val y.val

theorem pair_mem_inverseEmbeddingGraph {domain codomain : ZFSet.{0}}
    (f : Members codomain ↪ Members domain) (x y : ZFSet.{0}) :
    ZFSet.pair x y ∈ inverseEmbeddingGraph f ↔
      ∃ hy : y ∈ codomain, (f ⟨y, hy⟩).val = x := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := ZFSet.mem_range.mp h
    obtain ⟨hx, hy⟩ := ZFSet.pair_inj.mp hz
    subst y
    exact ⟨z.property, hx⟩
  · rintro ⟨hy, hx⟩
    exact ZFSet.mem_range.mpr ⟨⟨y, hy⟩, congrArg (fun x => ZFSet.pair x y) hx⟩

theorem surjectsSubsetValue_iff_injection (domain codomain : ZFSet.{0}) :
    surjectsSubsetValue setStructure domain codomain ↔
      Nonempty (Members codomain ↪ Members domain) := by
  rw [surjectsSubsetValue_set]
  constructor
  · rintro ⟨subset, relation, hsubset, hsingle, _, hsurj⟩
    have hpreimage (y : Members codomain) :
        ∃ x : Members domain, x.val ∈ subset ∧ ZFSet.pair x.val y.val ∈ relation := by
      obtain ⟨x, hx, hxy⟩ := (surjectiveOnValue_set _ _ _).mp hsurj y.val y.property
      exact ⟨⟨x, hsubset hx⟩, hx, hxy⟩
    choose f hf using hpreimage
    refine ⟨⟨f, ?_⟩⟩
    intro x y hxy
    apply Subtype.ext
    exact (singleValuedValue_set _).mp hsingle (f x).val x.val y.val
      (hf x).2 (by simpa only [hxy] using (hf y).2)
  · rintro ⟨f⟩
    let subset : ZFSet.{0} := ZFSet.range fun y : Members codomain => (f y).val
    let relation := inverseEmbeddingGraph f
    refine ⟨subset, relation, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, rfl⟩ := ZFSet.mem_range.mp hx
      exact (f y).property
    · rw [singleValuedValue_set]
      intro x y z hxy hxz
      obtain ⟨hy, hfy⟩ := (pair_mem_inverseEmbeddingGraph f x y).mp hxy
      obtain ⟨hz, hfz⟩ := (pair_mem_inverseEmbeddingGraph f x z).mp hxz
      exact congrArg Subtype.val (f.injective (Subtype.ext (hfy.trans hfz.symm)))
    · rw [totalOnValue_set]
      intro x hx
      obtain ⟨y, hfy⟩ := ZFSet.mem_range.mp hx
      exact ⟨y.val, y.property, (pair_mem_inverseEmbeddingGraph f x y.val).mpr ⟨y.property, hfy⟩⟩
    · rw [surjectiveOnValue_set]
      intro y hy
      exact ⟨(f ⟨y, hy⟩).val, ZFSet.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩,
        (pair_mem_inverseEmbeddingGraph f _ _).mpr ⟨hy, rfl⟩⟩

theorem surjectsSubsetValue_iff_injectsInto (domain codomain : ZFSet.{0}) :
    surjectsSubsetValue setStructure domain codomain ↔
      injectsIntoValue setStructure codomain domain := by
  rw [surjectsSubsetValue_iff_injection, injectsIntoValue_set]

def powersetMembersEquiv (x : ZFSet.{0}) :
    Equiv (Members (ZFSet.powerset x)) (Set (Members x)) where
  toFun y := membersSubset x y.val
  invFun A := ⟨subsetCode x A, ZFSet.mem_powerset.mpr (subsetCode_subset x A)⟩
  left_inv y := Subtype.ext (subsetCode_membersSubset x y.val (ZFSet.mem_powerset.mp y.property))
  right_inv A := membersSubset_subsetCode x A

def powersetOmegaEquiv : Equiv (Members (ZFSet.powerset ZFSet.omega)) (Set ℕ) :=
  (powersetMembersEquiv ZFSet.omega).trans
    (Equiv.arrowCongr omegaEquiv.symm (Equiv.refl Prop))

end

end Erdos597Object.CHInSets
