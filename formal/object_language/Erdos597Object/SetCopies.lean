import Erdos597Object.SetFunctions

set_option backward.isDefEq.respectTransparency false

/-! Ordered red copies and ordinary weak graph copies in the set interpretation. -/

namespace Erdos597Object.SetCopies

open Erdos597Object.SetInterpretation Erdos597Object.SetFunctions

noncomputable section

theorem respectsOrderValue_set (source target mapping : ZFSet.{0}) :
    respectsOrderValue setStructure source target mapping ↔
      ∀ x y a b, ZFSet.pair x a ∈ mapping → ZFSet.pair y b ∈ mapping →
        (ZFSet.pair x y ∈ source ↔ ZFSet.pair a b ∈ target) := by
  simp [respectsOrderValue, or_iff_not_imp_left, iff_def]
  constructor
  · intro h x y a b hxa hyb
    exact h x y a b hxa hyb
  · intro h x y a b hxa hyb
    exact h x y a b hxa hyb

theorem avoidsEdgesValue_set (blue mapping : ZFSet.{0}) :
    avoidsEdgesValue setStructure blue mapping ↔
      ∀ x y a b, ZFSet.pair x a ∈ mapping → ZFSet.pair y b ∈ mapping →
        x ≠ y → ZFSet.pair a b ∉ blue := by
  simp [avoidsEdgesValue, or_iff_not_imp_left]
  rfl

theorem respectsOrder_functionGraph_iff {domain codomain : ZFSet.{0}}
    (f : Members domain → Members codomain) (source target : ZFSet.{0}) :
    respectsOrderValue setStructure source target (functionGraph f) ↔
      ∀ x y : Members domain,
        (ZFSet.pair x.val y.val ∈ source ↔ ZFSet.pair (f x).val (f y).val ∈ target) := by
  rw [respectsOrderValue_set]
  constructor
  · intro h x y
    exact h _ _ _ _ ((members_pair_mem_functionGraph f x (f x)).mpr rfl)
      ((members_pair_mem_functionGraph f y (f y)).mpr rfl)
  · intro h x y a b hxa hyb
    obtain ⟨hx, hfa⟩ := (pair_mem_functionGraph f x a).mp hxa
    obtain ⟨hy, hfb⟩ := (pair_mem_functionGraph f y b).mp hyb
    simpa only [hfa, hfb] using h ⟨x, hx⟩ ⟨y, hy⟩

theorem avoidsEdges_functionGraph_iff {domain codomain : ZFSet.{0}}
    (f : Members domain → Members codomain) (blue : ZFSet.{0}) :
    avoidsEdgesValue setStructure blue (functionGraph f) ↔
      ∀ x y : Members domain, x ≠ y → ZFSet.pair (f x).val (f y).val ∉ blue := by
  rw [avoidsEdgesValue_set]
  constructor
  · intro h x y hxy
    exact h _ _ _ _ ((members_pair_mem_functionGraph f x (f x)).mpr rfl)
      ((members_pair_mem_functionGraph f y (f y)).mpr rfl)
      (fun heq => hxy (Subtype.ext heq))
  · intro h x y a b hxa hyb hxy
    obtain ⟨hx, hfa⟩ := (pair_mem_functionGraph f x a).mp hxa
    obtain ⟨hy, hfb⟩ := (pair_mem_functionGraph f y b).mp hyb
    have hne : (⟨x, hx⟩ : Members domain) ≠ ⟨y, hy⟩ :=
      fun heq => hxy (congrArg Subtype.val heq)
    simpa only [hfa, hfb] using h ⟨x, hx⟩ ⟨y, hy⟩ hne

theorem redCopyValue_iff (domain codomain sourceOrder targetOrder blue : ZFSet.{0}) :
    redCopyValue setStructure domain codomain sourceOrder targetOrder blue ↔
      ∃ f : Members domain → Members codomain, Function.Injective f ∧
        (∀ x y : Members domain,
          ZFSet.pair x.val y.val ∈ sourceOrder ↔
            ZFSet.pair (f x).val (f y).val ∈ targetOrder) ∧
        (∀ x y : Members domain, x ≠ y → ZFSet.pair (f x).val (f y).val ∉ blue) := by
  rw [redCopyValue, iSup_Prop_eq]
  constructor
  · rintro ⟨mapping, hfunc, hinj, horder, hblue⟩
    refine ⟨evaluate hfunc, ?_, ?_, ?_⟩
    · apply (functionGraph_injective_iff _).mp
      simpa only [functionGraph_evaluate] using hinj
    · apply (respectsOrder_functionGraph_iff _ _ _).mp
      simpa only [functionGraph_evaluate] using horder
    · apply (avoidsEdges_functionGraph_iff _ _).mp
      simpa only [functionGraph_evaluate] using hblue
  · rintro ⟨f, hinj, horder, hblue⟩
    exact ⟨functionGraph f, functionGraph_functionFrom f,
      (functionGraph_injective_iff f).mpr hinj,
      (respectsOrder_functionGraph_iff f sourceOrder targetOrder).mpr horder,
      (avoidsEdges_functionGraph_iff f blue).mpr hblue⟩

end

end Erdos597Object.SetCopies
