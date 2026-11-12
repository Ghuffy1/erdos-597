import Erdos597Object.BooleanGoodPairs

set_option backward.isDefEq.respectTransparency false

/-! Ordered separation of two set names and its extensionality. -/

namespace Erdos597Object.BooleanRowOrder

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def allBefore (order left right : bSet B) : B :=
  ⨅ x : bSet B, ⨅ y : bSet B,
    lattice.imp ((x ∈ᴮ left) ⊓ (y ∈ᴮ right)) (edgeValue (V B) order x y)

theorem allBefore_intro (context : B) (order left right : bSet B)
    (h : ∀ x y : bSet B, context ⊓ ((x ∈ᴮ left) ⊓ (y ∈ᴮ right)) ≤
      edgeValue (V B) order x y) : context ≤ allBefore order left right := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  exact lattice.bv_imp_intro (h x y)

theorem allBefore_elim (context : B) (order left right : bSet B)
    (h : context ≤ allBefore order left right) (x y : bSet B) :
    context ⊓ ((x ∈ᴮ left) ⊓ (y ∈ᴮ right)) ≤ edgeValue (V B) order x y := by
  exact lattice.bv_context_apply
    ((inf_le_left.trans h).trans ((iInf_le _ x).trans (iInf_le _ y))) inf_le_right

theorem allBefore_left_ext (order right : bSet B) :
    bSet.B_ext (fun left => allBefore order left right) := by
  apply bSet.B_ext_iInf
  intro x
  apply bSet.B_ext_iInf
  intro y
  exact bSet.B_ext_imp
    (bSet.B_ext_inf (bSet.B_ext_mem_right x) (bSet.B_ext_const (y ∈ᴮ right)))
    (bSet.B_ext_const _)

theorem allBefore_right_ext (order left : bSet B) :
    bSet.B_ext (fun right => allBefore order left right) := by
  apply bSet.B_ext_iInf
  intro x
  apply bSet.B_ext_iInf
  intro y
  exact bSet.B_ext_imp
    (bSet.B_ext_inf (bSet.B_ext_const (x ∈ᴮ left)) (bSet.B_ext_mem_right y))
    (bSet.B_ext_const _)

theorem allBefore_restrict (context : B) (order left right smallLeft smallRight : bSet B)
    (hleft : context ≤ smallLeft ⊆ᴮ left) (hright : context ≤ smallRight ⊆ᴮ right)
    (hbefore : context ≤ allBefore order left right) :
    context ≤ allBefore order smallLeft smallRight := by
  apply allBefore_intro
  intro x y
  let part := context ⊓ ((x ∈ᴮ smallLeft) ⊓ (y ∈ᴮ smallRight))
  have hx : part ≤ x ∈ᴮ left :=
    bSet.mem_of_mem_subset' (inf_le_left.trans hleft) (inf_le_right.trans inf_le_left)
  have hy : part ≤ y ∈ᴮ right :=
    bSet.mem_of_mem_subset' (inf_le_left.trans hright) (inf_le_right.trans inf_le_right)
  exact (le_inf le_rfl (le_inf hx hy)).trans
    (allBefore_elim part order left right (inf_le_left.trans hbefore) x y)

end Erdos597Object.BooleanRowOrder
