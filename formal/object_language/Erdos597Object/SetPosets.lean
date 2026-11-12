import Erdos597Object.MartinInSets
import Erdos597Object.MartinTransport
import Erdos597Object.SetSubsets

set_option backward.isDefEq.respectTransparency false

/-! Decode set-coded partial orders, dense sets, antichains and filters. -/

namespace Erdos597Object.SetPosets

open Erdos597Object.SetInterpretation Erdos597Object.SetFunctions
open Erdos597Object.MartinInSets Erdos597Object.SetSubsets

noncomputable section

abbrev decodedPartialOrder {conditions order : ZFSet.{0}}
    (h : partialOrderValue setStructure conditions order) : PartialOrder (Members conditions) where
  le x y := ZFSet.pair x.val y.val ∈ order
  lt x y := ZFSet.pair x.val y.val ∈ order ∧ ZFSet.pair y.val x.val ∉ order
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl x := (partialOrderValue_set _ _).mp h |>.2.1 x.val x.property
  le_trans x y z hxy hyz := (partialOrderValue_set _ _).mp h |>.2.2.2
    x.val x.property y.val y.property z.val z.property hxy hyz
  le_antisymm x y hxy hyx := Subtype.ext ((partialOrderValue_set _ _).mp h |>.2.2.1
    x.val x.property y.val y.property hxy hyx)

theorem compatibleValue_members {conditions order : ZFSet.{0}}
    (h : partialOrderValue setStructure conditions order) (x y : Members conditions) :
    letI orderInstance : PartialOrder (Members conditions) := decodedPartialOrder h
    letI : Preorder (Members conditions) := orderInstance.toPreorder
    letI : LE (Members conditions) := orderInstance.toLE
    letI : LT (Members conditions) := orderInstance.toLT
    compatibleValue setStructure conditions order x.val y.val ↔
      ∃ z : Members conditions, z ≤ x ∧ z ≤ y := by
  letI orderInstance : PartialOrder (Members conditions) := decodedPartialOrder h
  letI : Preorder (Members conditions) := orderInstance.toPreorder
  letI : LE (Members conditions) := orderInstance.toLE
  letI : LT (Members conditions) := orderInstance.toLT
  rw [compatibleValue_set]
  exact ⟨fun ⟨z, hz, hzx, hzy⟩ => ⟨⟨z, hz⟩, hzx, hzy⟩,
    fun ⟨z, hzx, hzy⟩ => ⟨z.val, z.property, hzx, hzy⟩⟩

theorem antichainValue_subsetCode_iff {conditions order : ZFSet.{0}}
    (h : partialOrderValue setStructure conditions order) (A : Set (Members conditions)) :
    letI orderInstance : PartialOrder (Members conditions) := decodedPartialOrder h
    letI : Preorder (Members conditions) := orderInstance.toPreorder
    letI : LE (Members conditions) := orderInstance.toLE
    letI : LT (Members conditions) := orderInstance.toLT
    antichainValue setStructure conditions order (subsetCode conditions A) ↔
      A.Pairwise (fun x y => ¬ ∃ z : Members conditions, z ≤ x ∧ z ≤ y) := by
  letI orderInstance : PartialOrder (Members conditions) := decodedPartialOrder h
  letI : Preorder (Members conditions) := orderInstance.toPreorder
  letI : LE (Members conditions) := orderInstance.toLE
  letI : LT (Members conditions) := orderInstance.toLT
  rw [antichainValue_set]
  constructor
  · rintro ⟨_, hA⟩ x hx y hy hxy hcommon
    exact hA x.val ((member_mem_subsetCode _ _ _).mpr hx)
      y.val ((member_mem_subsetCode _ _ _).mpr hy)
      (fun hval => hxy (Subtype.ext hval))
      ((compatibleValue_members h x y).mpr hcommon)
  · intro hA
    refine ⟨subsetCode_subset _ _, ?_⟩
    intro x hx y hy hxy hcommon
    obtain ⟨hxc, hxA⟩ := (mem_subsetCode_iff _ _ _).mp hx
    obtain ⟨hyc, hyA⟩ := (mem_subsetCode_iff _ _ _).mp hy
    exact hA hxA hyA (fun hval => hxy (congrArg Subtype.val hval))
      ((compatibleValue_members h ⟨x, hxc⟩ ⟨y, hyc⟩).mp hcommon)

theorem countableChainConditionValue_iff {conditions order : ZFSet.{0}}
    (h : partialOrderValue setStructure conditions order) :
    letI orderInstance : PartialOrder (Members conditions) := decodedPartialOrder h
    letI : Preorder (Members conditions) := orderInstance.toPreorder
    letI : LE (Members conditions) := orderInstance.toLE
    letI : LT (Members conditions) := orderInstance.toLT
    countableChainConditionValue setStructure conditions order ↔
      MartinTransport.CountableChainCondition (Members conditions) := by
  letI orderInstance : PartialOrder (Members conditions) := decodedPartialOrder h
  letI : Preorder (Members conditions) := orderInstance.toPreorder
  letI : LE (Members conditions) := orderInstance.toLE
  letI : LT (Members conditions) := orderInstance.toLT
  rw [countableChainConditionValue_set]
  constructor
  · intro hccc A hA
    exact (injectsInto_subsetCode_omega_iff conditions A).mp
      (hccc _ ((antichainValue_subsetCode_iff h A).mpr hA))
  · intro hccc family hA
    have hsub := ((antichainValue_set _ _ _).mp hA).1
    let A := membersSubset conditions family
    have hcode : subsetCode conditions A = family := subsetCode_membersSubset _ _ hsub
    have hpair := (antichainValue_subsetCode_iff h A).mp (by simpa only [hcode] using hA)
    have hinj := (injectsInto_subsetCode_omega_iff conditions A).mpr (hccc A hpair)
    simpa only [hcode] using hinj

theorem denseValue_subsetCode_iff {conditions order : ZFSet.{0}}
    (h : partialOrderValue setStructure conditions order) (D : Set (Members conditions)) :
    letI orderInstance : PartialOrder (Members conditions) := decodedPartialOrder h
    letI : Preorder (Members conditions) := orderInstance.toPreorder
    letI : LE (Members conditions) := orderInstance.toLE
    letI : LT (Members conditions) := orderInstance.toLT
    denseValue setStructure conditions order (subsetCode conditions D) ↔
      ∀ x : Members conditions, ∃ y ∈ D, y ≤ x := by
  letI orderInstance : PartialOrder (Members conditions) := decodedPartialOrder h
  letI : Preorder (Members conditions) := orderInstance.toPreorder
  letI : LE (Members conditions) := orderInstance.toLE
  letI : LT (Members conditions) := orderInstance.toLT
  rw [denseValue_set]
  constructor
  · rintro ⟨_, hD⟩ x
    obtain ⟨y, hy, hyx⟩ := hD x.val x.property
    obtain ⟨hyc, hyD⟩ := (mem_subsetCode_iff _ _ _).mp hy
    exact ⟨⟨y, hyc⟩, hyD, hyx⟩
  · intro hD
    refine ⟨subsetCode_subset _ _, ?_⟩
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hD ⟨x, hx⟩
    exact ⟨y.val, (member_mem_subsetCode _ _ _).mpr hy, hyx⟩

theorem denseValue_membersSubset {conditions order denseSet : ZFSet.{0}}
    (h : partialOrderValue setStructure conditions order)
    (hD : denseValue setStructure conditions order denseSet) :
    letI orderInstance : PartialOrder (Members conditions) := decodedPartialOrder h
    letI : Preorder (Members conditions) := orderInstance.toPreorder
    letI : LE (Members conditions) := orderInstance.toLE
    letI : LT (Members conditions) := orderInstance.toLT
    ∀ x : Members conditions, ∃ y ∈ membersSubset conditions denseSet, y ≤ x := by
  letI orderInstance : PartialOrder (Members conditions) := decodedPartialOrder h
  letI : Preorder (Members conditions) := orderInstance.toPreorder
  letI : LE (Members conditions) := orderInstance.toLE
  letI : LT (Members conditions) := orderInstance.toLT
  have hraw := (denseValue_set _ _ _).mp hD
  intro x
  obtain ⟨y, hy, hyx⟩ := hraw.2 x.val x.property
  exact ⟨⟨y, hraw.1 hy⟩, hy, hyx⟩

theorem orderFilterValue_of_filter {conditions order : ZFSet.{0}}
    (h : partialOrderValue setStructure conditions order)
    (F : @Order.PFilter (Members conditions) (decodedPartialOrder h).toPreorder) :
    orderFilterValue setStructure conditions order (subsetCode conditions (F : Set (Members conditions))) := by
  letI orderInstance : PartialOrder (Members conditions) := decodedPartialOrder h
  letI : Preorder (Members conditions) := orderInstance.toPreorder
  letI : LE (Members conditions) := orderInstance.toLE
  letI : LT (Members conditions) := orderInstance.toLT
  rw [orderFilterValue_set]
  refine ⟨subsetCode_subset _ _, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := F.nonempty
    exact ⟨x.val, (member_mem_subsetCode _ _ _).mpr hx⟩
  · intro x hx y hy hxy
    obtain ⟨hxc, hxF⟩ := (mem_subsetCode_iff _ _ _).mp hx
    exact (member_mem_subsetCode _ _ ⟨y, hy⟩).mpr (F.mem_of_le hxy hxF)
  · intro x hx y hy
    obtain ⟨hxc, hxF⟩ := (mem_subsetCode_iff _ _ _).mp hx
    obtain ⟨hyc, hyF⟩ := (mem_subsetCode_iff _ _ _).mp hy
    obtain ⟨z, hz, hzx, hzy⟩ := F.directed ⟨x, hxc⟩ hxF ⟨y, hyc⟩ hyF
    exact ⟨z.val, (member_mem_subsetCode _ _ _).mpr hz, hzx, hzy⟩

def filterOfValue {conditions order filter : ZFSet.{0}}
    (h : partialOrderValue setStructure conditions order)
    (hF : orderFilterValue setStructure conditions order filter) :
    @Order.PFilter (Members conditions) (decodedPartialOrder h).toPreorder := by
  letI orderInstance : PartialOrder (Members conditions) := decodedPartialOrder h
  letI : Preorder (Members conditions) := orderInstance.toPreorder
  letI : LE (Members conditions) := orderInstance.toLE
  letI : LT (Members conditions) := orderInstance.toLT
  have hraw := (orderFilterValue_set _ _ _).mp hF
  have hfilter : Order.IsPFilter (membersSubset conditions filter) := Order.IsPFilter.of_def
    (by
      obtain ⟨x, hx⟩ := hraw.2.1
      exact ⟨⟨x, hraw.1 hx⟩, hx⟩)
    (by
      intro x hx y hy
      obtain ⟨z, hz, hzx, hzy⟩ := hraw.2.2.2 x.val hx y.val hy
      exact ⟨⟨z, hraw.1 hz⟩, hz, hzx, hzy⟩)
    (by
      intro x y hxy hx
      exact hraw.2.2.1 x.val hx y.val y.property hxy)
  exact hfilter.toPFilter

@[simp] theorem mem_filterOfValue {conditions order filter : ZFSet.{0}}
    (h : partialOrderValue setStructure conditions order)
    (hF : orderFilterValue setStructure conditions order filter) (x : Members conditions) :
    x ∈ filterOfValue h hF ↔ x.val ∈ filter := Iff.rfl

end

end Erdos597Object.SetPosets
