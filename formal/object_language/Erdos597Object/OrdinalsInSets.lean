import Erdos597Object.OrdinalSemantics

set_option backward.isDefEq.respectTransparency false

/-! Ordinals in the ordinary set interpretation. -/

namespace Erdos597Object.OrdinalsInSets

open Erdos597Object.SetInterpretation

local notation "[]" => Flypitch.dvector.nil

@[simp] theorem emptysetValue_set :
    setStructure.fun_map Flypitch.ZFC.ZFCFunc.emptyset [] = (∅ : ZFSet.{0}) := rfl

theorem subsetValue_set (x y : ZFSet.{0}) : subsetValue setStructure x y ↔ x ⊆ y := by
  simp [subsetValue, ZFSet.subset_def, or_iff_not_imp_left]
  rfl

theorem transitiveValue_set (x : ZFSet.{0}) :
    transitiveValue setStructure x ↔ x.IsTransitive := by
  simp [transitiveValue, subsetValue_set, ZFSet.IsTransitive, or_iff_not_imp_left]
  rfl

theorem trichotomyValue_set (x : ZFSet.{0}) :
    trichotomyValue setStructure x ↔
      ∀ y ∈ x, ∀ z ∈ x, y = z ∨ y ∈ z ∨ z ∈ y := by
  simp [trichotomyValue, or_iff_not_imp_left, or_assoc]
  rfl

theorem wellFoundedValue_set (x : ZFSet.{0}) :
    wellFoundedValue setStructure x ↔
      ∀ y : ZFSet.{0}, y ⊆ x → y ≠ ∅ → ∃ z ∈ y, ∀ w ∈ y, w ∉ z := by
  simp [wellFoundedValue, subsetValue_set, or_iff_not_imp_left]
  rfl

theorem wellFoundedValue_holds (x : ZFSet.{0}) : wellFoundedValue setStructure x := by
  rw [wellFoundedValue_set]
  intro y _ hy
  have hnonempty : (y : Set ZFSet).Nonempty := by
    by_contra h
    apply hy
    apply (ZFSet.eq_empty y).mpr
    intro z hz
    exact h ⟨z, hz⟩
  exact ZFSet.mem_wf.has_min (y : Set ZFSet) hnonempty

theorem ordinalValue_set (x : ZFSet.{0}) : ordinalValue setStructure x ↔ x.IsOrdinal := by
  change ((trichotomyValue setStructure x ∧ wellFoundedValue setStructure x) ∧
    transitiveValue setStructure x) ↔ _
  rw [trichotomyValue_set, transitiveValue_set]
  constructor
  · rintro ⟨⟨htri, _⟩, htrans⟩
    apply ZFSet.isOrdinal_iff_trichotomous.mpr
    refine ⟨htrans, Std.trichotomous_of_rel_or_eq_or_rel_swap ?_⟩
    intro y z
    rcases htri y.val y.property z.val z.property with h | h | h
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · intro h
    refine ⟨⟨?_, wellFoundedValue_holds x⟩, h.isTransitive⟩
    intro y hy z hz
    rcases (h.mem hy).mem_trichotomous (h.mem hz) with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

end Erdos597Object.OrdinalsInSets
