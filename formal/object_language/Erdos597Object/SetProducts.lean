import Erdos597Object.GraphCopies

set_option backward.isDefEq.respectTransparency false

/-! Set products and their lexicographic order in the ordinary interpretation. -/

namespace Erdos597Object.SetProducts

open Erdos597Object.SetInterpretation Erdos597Object.SetFunctions
open Erdos597Object.GraphCopies

noncomputable section

theorem cartesianProductValue_set (left right product : ZFSet.{0}) :
    cartesianProductValue setStructure left right product ↔
      ∀ entry, entry ∈ product ↔ ∃ x ∈ left, ∃ y ∈ right, entry = ZFSet.pair x y := by
  simp [cartesianProductValue, or_iff_not_imp_left, iff_def]
  constructor
  · intro h entry
    exact h entry
  · intro h entry
    exact h entry

theorem cartesianProductValue_iff (left right product : ZFSet.{0}) :
    cartesianProductValue setStructure left right product ↔ product = ZFSet.prod left right := by
  rw [cartesianProductValue_set]
  constructor
  · intro h
    exact ZFSet.ext fun entry => (h entry).trans ZFSet.mem_prod.symm
  · rintro rfl
    exact fun entry => ZFSet.mem_prod

theorem lexLessValue_pair (a b c d : ZFSet.{0}) :
    lexLessValue setStructure (ZFSet.pair a b) (ZFSet.pair c d) ↔
      a ∈ c ∨ a = c ∧ b ∈ d := by
  simp [lexLessValue, ZFSet.pair_inj]

def productEquiv (left right : ZFSet.{0}) :
    Equiv (Members left × Members right) (Members (ZFSet.prod left right)) :=
  Equiv.ofBijective
    (fun xy => ⟨ZFSet.pair xy.1.val xy.2.val,
      ZFSet.pair_mem_prod.mpr ⟨xy.1.property, xy.2.property⟩⟩)
    (by
      constructor
      · intro x y h
        obtain ⟨hleft, hright⟩ := ZFSet.pair_inj.mp (congrArg Subtype.val h)
        exact Prod.ext (Subtype.ext hleft) (Subtype.ext hright)
      · intro entry
        obtain ⟨x, hx, y, hy, hentry⟩ := ZFSet.mem_prod.mp entry.property
        exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hentry.symm⟩)

@[simp] theorem productEquiv_value (left right : ZFSet.{0})
    (xy : Members left × Members right) :
    (productEquiv left right xy).val = ZFSet.pair xy.1.val xy.2.val := rfl

def lexOrderSet (left right : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.pairSep (fun x y => lexLessValue setStructure x y)
    (ZFSet.prod left right) (ZFSet.prod left right)

theorem pair_mem_lexOrderSet (left right x y : ZFSet.{0}) :
    ZFSet.pair x y ∈ lexOrderSet left right ↔
      x ∈ ZFSet.prod left right ∧ y ∈ ZFSet.prod left right ∧
        lexLessValue setStructure x y := by
  change ZFSet.pair x y ∈ ZFSet.pairSep _ _ _ ↔ _
  rw [ZFSet.mem_pairSep]
  constructor
  · rintro ⟨a, ha, b, hb, hpair, hless⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp hpair
    exact ⟨ha, hb, hless⟩
  · rintro ⟨hx, hy, hless⟩
    exact ⟨x, hx, y, hy, rfl, hless⟩

theorem lexOrderValue_set (vertices order : ZFSet.{0}) :
    lexOrderValue setStructure vertices order ↔
      relationBetweenValue setStructure vertices vertices order ∧
        ∀ x ∈ vertices, ∀ y ∈ vertices,
          (ZFSet.pair x y ∈ order ↔ lexLessValue setStructure x y) := by
  simp [lexOrderValue, or_iff_not_imp_left, iff_def]
  tauto

theorem lexOrderSet_spec (left right : ZFSet.{0}) :
    lexOrderValue setStructure (ZFSet.prod left right) (lexOrderSet left right) := by
  rw [lexOrderValue_set]
  constructor
  · rw [relationBetweenValue_set]
    intro entry hentry
    obtain ⟨x, hx, y, hy, hentry, _⟩ := ZFSet.mem_pairSep.mp hentry
    exact ⟨x, hx, y, hy, hentry⟩
  · intro x hx y hy
    simpa only [hx, hy, true_and] using pair_mem_lexOrderSet left right x y

theorem product_relation (left right : ZFSet.{0})
    (x y : Members left × Members right) :
    relationOn (ZFSet.prod left right) (lexOrderSet left right)
        (productEquiv left right x) (productEquiv left right y) ↔
      Prod.Lex (fun a b : Members left => a.val ∈ b.val)
        (fun a b : Members right => a.val ∈ b.val) x y := by
  change ZFSet.pair (productEquiv left right x).val (productEquiv left right y).val
    ∈ lexOrderSet left right ↔ _
  rw [pair_mem_lexOrderSet]
  simp only [productEquiv_value, lexLessValue_pair, Prod.lex_def]
  rw [Subtype.ext_iff]
  simp only [ZFSet.pair_mem_prod, x.1.property, x.2.property,
    y.1.property, y.2.property, true_and]

def productOrderIso (left right : ZFSet.{0}) :
    (Prod.Lex (fun a b : Members left => a.val ∈ b.val)
      (fun a b : Members right => a.val ∈ b.val)) ≃r
        relationOn (ZFSet.prod left right) (lexOrderSet left right) where
  toEquiv := productEquiv left right
  map_rel_iff' := product_relation left right _ _

end

end Erdos597Object.SetProducts
