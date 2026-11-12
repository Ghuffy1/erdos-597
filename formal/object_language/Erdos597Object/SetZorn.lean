import Erdos597Object.SetAxioms
import Mathlib.Order.Zorn

set_option backward.isDefEq.respectTransparency false

/-! Zorn's lemma for the set-coded inclusion order. -/

namespace Erdos597Object.SetZorn

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open Erdos597Object.SetInterpretation Erdos597Object.OrdinalsInSets
open Erdos597Object.SetAxioms

theorem maximal_of_union_closed (A : ZFSet.{0})
    (hclosed : ∀ c : ZFSet.{0}, c ⊆ A →
      (∀ x y : ZFSet.{0}, x ∈ c → y ∈ c → x ⊆ y ∨ y ⊆ x) → ZFSet.sUnion c ∈ A) :
    ∃ m ∈ A, ∀ z ∈ A, m ⊆ z → m = z := by
  haveI : Small.{0} (A : Set ZFSet.{0}) := ZFSet.small_coe A
  have hbound : ∀ c ⊆ (A : Set ZFSet.{0}), IsChain (· ≤ ·) c →
      ∃ upper ∈ (A : Set ZFSet.{0}), ∀ z ∈ c, z ≤ upper := by
    intro c hc hchain
    haveI : Small.{0} c := small_subset hc
    let code : ZFSet.{0} := ZFSet.range fun x : c => x.val
    have hcode : code ⊆ A := by
      intro x hx
      obtain ⟨y, rfl⟩ := ZFSet.mem_range.mp hx
      exact hc y.property
    have hcodeChain : ∀ x y : ZFSet.{0}, x ∈ code → y ∈ code → x ⊆ y ∨ y ⊆ x := by
      intro x y hx hy
      obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hx
      obtain ⟨b, rfl⟩ := ZFSet.mem_range.mp hy
      by_cases hab : a.val = b.val
      · exact Or.inl (hab ▸ le_rfl)
      · exact hchain a.property b.property hab
    refine ⟨ZFSet.sUnion code, hclosed code hcode hcodeChain, ?_⟩
    intro z hz y hy
    exact ZFSet.mem_sUnion.mpr ⟨z, ZFSet.mem_range.mpr ⟨⟨z, hz⟩, rfl⟩, hy⟩
  obtain ⟨m, hm⟩ := zorn_le₀ (A : Set ZFSet.{0}) hbound
  exact ⟨m, hm.1, fun z hz hmz => le_antisymm hmz (hm.2 hz hmz)⟩

theorem set_models_zorn : boolean_realize_sentence setStructure zornsLemma := by
  simp [zornsLemma, boolean_realize_sentence, realize_subset, subsetValue_set,
    unionValue_set, var0, var1, var2, var3, lattice.imp, or_iff_not_imp_left, and_imp]
  intro A _ hclosed
  apply maximal_of_union_closed A
  intro c hc hchain
  apply hclosed c hc
  intro x hx y hy hxy
  exact (hchain x y hx hy).resolve_left hxy

end Erdos597Object.SetZorn
