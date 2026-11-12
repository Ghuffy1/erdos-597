import Erdos597Object.SetAxioms

set_option backward.isDefEq.respectTransparency false

/-! Collection for arbitrary predicates in the ordinary set structure. -/

namespace Erdos597Object.SetCollection

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open Erdos597Object.SetInterpretation Erdos597Object.SetFunctions

theorem set_collection_property (relation : ZFSet.{0} → ZFSet.{0} → Prop)
    (domain : ZFSet.{0}) (h : ∀ x ∈ domain, ∃ y, relation x y) :
    ∃ image : ZFSet.{0},
      (∀ x ∈ domain, ∃ y ∈ image, relation x y) ∧
      (∀ y ∈ image, ∃ x ∈ domain, relation x y) := by
  have hchoice (x : Members domain) : ∃ y, relation x.val y := h x.val x.property
  choose f hf using hchoice
  refine ⟨ZFSet.range f, ?_, ?_⟩
  · intro x hx
    exact ⟨f ⟨x, hx⟩, ZFSet.mem_range_self _, hf ⟨x, hx⟩⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := ZFSet.mem_range.mp hy
    exact ⟨x.val, x.property, hf x⟩

theorem collectionValue_set (relation : ZFSet.{0} → ZFSet.{0} → Prop) (domain : ZFSet.{0}) :
    collectionValue setStructure relation domain ↔
      (∀ x ∈ domain, ∃ y, relation x y) →
        ∃ image : ZFSet.{0},
          (∀ x ∈ domain, ∃ y ∈ image, relation x y) ∧
          (∀ y ∈ image, ∃ x ∈ domain, relation x y) := by
  simp [collectionValue, or_iff_not_imp_left]
  rfl

theorem set_models_collection {n : ℕ} (f : bounded_formula L_ZFC (n + 2)) :
    boolean_realize_sentence setStructure (axiomOfCollection f) := by
  rw [realize_collection, iInf_Prop_eq]
  intro xs
  rw [iInf_Prop_eq]
  intro domain
  apply (collectionValue_set _ _).mpr
  exact set_collection_property _ domain

end Erdos597Object.SetCollection
