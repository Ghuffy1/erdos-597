import Erdos597Object.BooleanFunctionBridge

set_option backward.isDefEq.respectTransparency false

/-! Reindex a Boolean-valued set name without changing its equality value. -/

namespace Erdos597Object.BooleanSetRelabeling

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets

variable {B I J : Type} [CompleteBooleanAlgebra B]

theorem weighted_relabel (e : J ≃ I) (element : I → bSet B) (weight : I → B) :
    ⊤ ≤ weightedSet (fun j => element (e j)) (fun j => weight (e j)) =ᴮ weightedSet element weight := by
  apply bSet.subset_ext
  · apply bSet.subset_intro
    intro j
    exact inf_le_right.trans (weight_le_member element weight (e j))
  · apply bSet.subset_intro
    intro i
    have h := weight_le_member (fun j => element (e j)) (fun j => weight (e j)) (e.symm i)
    simpa only [e.apply_symm_apply] using! (inf_le_right.trans h : ⊤ ⊓ weight (e (e.symm i)) ≤ _)

theorem check_weighted (x : pSet.{0}) :
    (bSet.check x : bSet B) = weightedSet (fun i : x.Type => bSet.check (x.Func i)) (fun _ => ⊤) := by
  cases x
  rfl

theorem ordinal_elements_discrete (o : Ordinal.{0}) :
    ∀ i j : o.toPSet.Type, i ≠ j →
      ((bSet.check (o.toPSet.Func i) : bSet B) =ᴮ bSet.check (o.toPSet.Func j)) = ⊥ := by
  rw [Ordinal.toPSet.eq_1 o]
  intro i j hij
  apply bSet.check_bv_eq_bot_of_not_equiv
  intro h
  apply hij
  apply Ordinal.ToType.mk.symm.injective
  apply Subtype.ext
  exact Flypitch.ordinal.mk_inj h

end Erdos597Object.BooleanSetRelabeling
