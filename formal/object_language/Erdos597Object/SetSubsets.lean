import Erdos597Object.FirstUncountable

set_option backward.isDefEq.respectTransparency false

/-! Set codes for arbitrary subsets and countability. -/

namespace Erdos597Object.SetSubsets

open Cardinal Ordinal
open scoped Cardinal Ordinal
open Erdos597Object.SetInterpretation Erdos597Object.SetFunctions
open Erdos597Object.SetCodes Erdos597Object.FirstUncountable
open Erdos597Object.OrdinalPresentation

noncomputable section

def omegaEquiv : Equiv ℕ (Members ZFSet.omega) :=
  Equiv.ofBijective (fun n => ⟨naturalSet n, naturalSet_mem_omega n⟩) (by
    constructor
    · intro m n h
      exact naturalSet_injective (congrArg Subtype.val h)
    · intro x
      obtain ⟨n, hn⟩ := (mem_omega_iff x.val).mp x.property
      exact ⟨n, Subtype.ext hn⟩)

theorem injectsInto_omega_iff (x : ZFSet.{0}) :
    injectsIntoValue setStructure x ZFSet.omega ↔ Countable (Members x) := by
  rw [injectsIntoValue_set]
  constructor
  · rintro ⟨f⟩
    exact (omegaEquiv.symm.injective.comp f.injective).countable
  · intro h
    obtain ⟨f, hf⟩ := @Countable.exists_injective_nat (Members x) h
    exact ⟨⟨omegaEquiv ∘ f, omegaEquiv.injective.comp hf⟩⟩

def membersSubset (conditions subset : ZFSet.{0}) : Set (Members conditions) :=
  {x | x.val ∈ subset}

def subsetCode (conditions : ZFSet.{0}) (A : Set (Members conditions)) : ZFSet.{0} :=
  conditions.sep (fun x => ∃ hx : x ∈ conditions, (⟨x, hx⟩ : Members conditions) ∈ A)

theorem subsetCode_subset (conditions : ZFSet.{0}) (A : Set (Members conditions)) :
    subsetCode conditions A ⊆ conditions := ZFSet.sep_subset

theorem mem_subsetCode_iff (conditions : ZFSet.{0}) (A : Set (Members conditions))
    (x : ZFSet.{0}) : x ∈ subsetCode conditions A ↔
      ∃ hx : x ∈ conditions, (⟨x, hx⟩ : Members conditions) ∈ A := by
  rw [subsetCode, ZFSet.mem_sep]
  exact ⟨And.right, fun ⟨hx, hA⟩ => ⟨hx, hx, hA⟩⟩

@[simp] theorem member_mem_subsetCode (conditions : ZFSet.{0})
    (A : Set (Members conditions)) (x : Members conditions) :
    x.val ∈ subsetCode conditions A ↔ x ∈ A := by
  rw [mem_subsetCode_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.property, h⟩⟩

@[simp] theorem membersSubset_subsetCode (conditions : ZFSet.{0})
    (A : Set (Members conditions)) :
    membersSubset conditions (subsetCode conditions A) = A := by
  ext x
  exact member_mem_subsetCode conditions A x

theorem subsetCode_membersSubset (conditions subset : ZFSet.{0})
    (h : subset ⊆ conditions) : subsetCode conditions (membersSubset conditions subset) = subset := by
  apply ZFSet.ext
  intro x
  rw [mem_subsetCode_iff]
  exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨h hx, hx⟩⟩

def subsetCodeEquiv (conditions : ZFSet.{0}) (A : Set (Members conditions)) :
    Equiv A (Members (subsetCode conditions A)) :=
  Equiv.ofBijective
    (fun x => ⟨x.val.val, (member_mem_subsetCode conditions A x.val).mpr x.property⟩)
    (by
      constructor
      · intro x y h
        have hval : x.val.val = y.val.val :=
          congrArg (fun z : Members (subsetCode conditions A) => z.val) h
        exact Subtype.ext (Subtype.ext hval)
      · intro x
        let y : Members conditions := ⟨x.val, subsetCode_subset conditions A x.property⟩
        exact ⟨⟨y, (member_mem_subsetCode conditions A y).mp x.property⟩, rfl⟩)

theorem injectsInto_subsetCode_omega_iff (conditions : ZFSet.{0})
    (A : Set (Members conditions)) :
    injectsIntoValue setStructure (subsetCode conditions A) ZFSet.omega ↔ A.Countable := by
  rw [injectsInto_omega_iff]
  exact (subsetCodeEquiv conditions A).countable_iff.symm

theorem injectsInto_omegaOne_iff (family : ZFSet.{0}) :
    injectsIntoValue setStructure family (ω₁ : Ordinal.{0}).toZFSet ↔
      #(Shrink.{0} (Members family)) ≤ ℵ₁ := by
  rw [injectsIntoValue_set]
  let e : Equiv (Shrink.{0} (Members family)) (Members family) := (equivShrink _).symm
  let o : Equiv (ω₁ : Ordinal.{0}).ToType (Members (ω₁ : Ordinal.{0}).toZFSet) :=
    ordinalEquiv _
  constructor
  · rintro ⟨f⟩
    let g := (e.toEmbedding.trans f).trans o.symm.toEmbedding
    simpa using Cardinal.mk_le_of_injective g.injective
  · intro h
    have h' : #(Shrink.{0} (Members family)) ≤ #((ω₁ : Ordinal.{0}).ToType) := by
      simpa using h
    obtain ⟨f⟩ := (Cardinal.le_def _ _).mp h'
    exact ⟨(e.symm.toEmbedding.trans f).trans o.toEmbedding⟩

def typeCode (P : Type) : ZFSet.{0} := (#P).ord.toZFSet

def typeEquiv (P : Type) : Equiv P (Members (typeCode P)) :=
  (Classical.choice (Cardinal.eq.mp (by simp : #P = #((#P).ord.ToType)))).trans
    (ordinalEquiv (#P).ord)

end

end Erdos597Object.SetSubsets
