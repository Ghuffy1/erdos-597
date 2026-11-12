import Erdos597Object.BooleanUncountability

set_option backward.isDefEq.respectTransparency false

/-! Identify the object-language function predicates with the Boolean set-theory library. -/

namespace Erdos597Object.BooleanFunctionBridge

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections

variable {B : Type} [CompleteBooleanAlgebra B]

theorem product_membership (domain codomain entry : bSet B) :
    (entry ∈ᴮ bSet.prod domain codomain) =
      ⨆ x : bSet B, (x ∈ᴮ domain) ⊓
        ⨆ y : bSet B, (y ∈ᴮ codomain) ⊓ (entry =ᴮ bSet.pair x y) := by
  calc
    _ = ⨆ i : domain.type, ⨆ j : codomain.type,
        (domain.bval i ⊓ codomain.bval j) ⊓ (entry =ᴮ bSet.pair (domain.func i) (codomain.func j)) := by
      change (⨆ ij : domain.type × codomain.type,
        (domain.bval ij.1 ⊓ codomain.bval ij.2) ⊓
          (entry =ᴮ bSet.pair (domain.func ij.1) (codomain.func ij.2))) = _
      rw [iSup_prod]
    _ = ⨆ i : domain.type, domain.bval i ⊓
        ⨆ j : codomain.type, codomain.bval j ⊓ (entry =ᴮ bSet.pair (domain.func i) (codomain.func j)) := by
      simp only [inf_iSup_eq, inf_assoc]
    _ = ⨆ i : domain.type, domain.bval i ⊓
        ⨆ y : bSet B, (y ∈ᴮ codomain) ⊓ (entry =ᴮ bSet.pair (domain.func i) y) := by
      apply iSup_congr
      intro i
      rw [bSet.bounded_exists codomain _
        (bSet.B_ext_pair_right (bSet.B_ext_eq_right entry) (domain.func i))]
    _ = _ := bSet.bounded_exists domain _
      (bSet.B_ext_iSup fun y => bSet.B_ext_inf (bSet.B_ext_const _)
        (bSet.B_ext_pair_left (bSet.B_ext_eq_right entry) y))

theorem relationBetween_eq_subset_prod (domain codomain relation : bSet B) :
    relationBetweenValue (V B) domain codomain relation = relation ⊆ᴮ bSet.prod domain codomain := by
  calc
    _ = subsetValue (V B) relation (bSet.prod domain codomain) := by
      unfold relationBetweenValue subsetValue
      apply iInf_congr
      intro entry
      simp only [memberValue_bSet, pairValue_bSet, eqValue_bSet]
      rw [product_membership]
      rfl
    _ = _ := subsetValue_bSet relation (bSet.prod domain codomain)

theorem singleValued_eq_is_func (relation : bSet B) :
    singleValuedValue (V B) relation = bSet.is_func relation := by
  apply le_antisymm
  · unfold bSet.is_func
    apply le_iInf
    intro x
    apply le_iInf
    intro y
    apply le_iInf
    intro u
    apply le_iInf
    intro v
    apply lattice.bv_imp_intro
    apply lattice.bv_imp_intro
    let part := (singleValuedValue (V B) relation ⊓
      (edgeValue (V B) relation x u ⊓ edgeValue (V B) relation y v)) ⊓ (x =ᴮ y)
    have hxu : part ≤ edgeValue (V B) relation x u :=
      inf_le_left.trans (inf_le_right.trans inf_le_left)
    have hyv : part ≤ edgeValue (V B) relation y v :=
      inf_le_left.trans (inf_le_right.trans inf_le_right)
    have hyu : part ≤ edgeValue (V B) relation y u :=
      (le_inf inf_le_right hxu).trans (edge_left_ext relation u x y)
    exact (le_inf (inf_le_left.trans inf_le_left) (le_inf hyu hyv)).trans
      (singleValued_outputs relation le_rfl y u v)
  · unfold singleValuedValue
    apply le_iInf
    intro x
    apply le_iInf
    intro y
    apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    have h := (inf_le_left : bSet.is_func relation ⊓
      (edgeValue (V B) relation x y ⊓ edgeValue (V B) relation x z) ≤ bSet.is_func relation).trans
        ((iInf_le _ x).trans ((iInf_le _ x).trans ((iInf_le _ y).trans (iInf_le _ z))))
    exact lattice.bv_context_apply (lattice.bv_context_apply h inf_le_right) bSet.bv_refl

theorem injective_eq_is_inj (relation : bSet B) :
    injectiveValue (V B) relation = bSet.is_inj relation := by
  apply le_antisymm
  · unfold bSet.is_inj
    apply le_iInf
    intro x
    apply le_iInf
    intro y
    apply le_iInf
    intro u
    apply le_iInf
    intro v
    apply lattice.bv_imp_intro
    let part := injectiveValue (V B) relation ⊓
      (edgeValue (V B) relation x u ⊓ edgeValue (V B) relation y v ⊓ (u =ᴮ v))
    have hxu : part ≤ edgeValue (V B) relation x u :=
      inf_le_right.trans (inf_le_left.trans inf_le_left)
    have hyv : part ≤ edgeValue (V B) relation y v :=
      inf_le_right.trans (inf_le_left.trans inf_le_right)
    have hyu : part ≤ edgeValue (V B) relation y u :=
      (le_inf (bSet.bv_symm (inf_le_right.trans inf_le_right)) hyv).trans
        (edge_right_ext relation y v u)
    exact (le_inf inf_le_left (le_inf hxu hyu)).trans (injective_outputs relation le_rfl x y u)
  · unfold injectiveValue
    apply le_iInf
    intro x
    apply le_iInf
    intro y
    apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    have h := (inf_le_left : bSet.is_inj relation ⊓
      (edgeValue (V B) relation x z ⊓ edgeValue (V B) relation y z) ≤ bSet.is_inj relation).trans
        ((iInf_le _ x).trans ((iInf_le _ y).trans ((iInf_le _ z).trans (iInf_le _ z))))
    exact lattice.bv_context_apply h (le_inf inf_le_right bSet.bv_refl)

theorem totalOn_eq_is_total (domain codomain relation : bSet B) :
    totalOnValue (V B) domain codomain relation = bSet.is_total domain codomain relation := rfl

theorem functionFrom_eq_is_function (domain codomain relation : bSet B) :
    functionFromValue (V B) domain codomain relation = bSet.is_function domain codomain relation := by
  rw [functionFromValue, relationBetween_eq_subset_prod, singleValued_eq_is_func, totalOn_eq_is_total]
  exact inf_comm _ _

theorem injectsInto_eq_injects_into (domain codomain : bSet B) :
    injectsIntoValue (V B) domain codomain = bSet.injects_into domain codomain := by
  unfold injectsIntoValue
  simp only [functionFrom_eq_is_function, injective_eq_is_inj]
  change bSet.injection_into domain codomain = bSet.injects_into domain codomain
  exact le_antisymm (bSet.injects_into_of_injection_into le_rfl)
    (bSet.injection_into_of_injects_into le_rfl)

end Erdos597Object.BooleanFunctionBridge
