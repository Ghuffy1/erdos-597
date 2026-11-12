import Erdos597Object.BooleanSets

set_option backward.isDefEq.respectTransparency false

/-! Fibres of a Boolean-valued injection into omega provide a countable cover. -/

namespace Erdos597Object.BooleanFunctionFibres

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open scoped Flypitch.bSet
open Erdos597Object.BooleanSets Erdos597Object.BooleanIteration

variable {B : Type} [CompleteBooleanAlgebra B]

theorem totalAt_naturals (domain relation : bSet B)
    (hfunction : ⊤ ≤ functionFromValue (V B) domain bSet.omega relation)
    (x : bSet B) :
    (x ∈ᴮ domain) ≤ ⨆ n : ℕ, edgeValue (V B) relation x (bSet.ofNat n) := by
  have htotal : ⊤ ≤ totalOnValue (V B) domain bSet.omega relation :=
    hfunction.trans (inf_le_right.trans inf_le_right)
  have himp : (x ∈ᴮ domain) ≤ lattice.imp (x ∈ᴮ domain)
      (⨆ y : bSet B, (y ∈ᴮ bSet.omega) ⊓ edgeValue (V B) relation x y) :=
    le_top.trans (htotal.trans (iInf_le _ x))
  have houtput := lattice.bv_context_apply himp le_rfl
  rw [omega_bounded_exists (fun y => edgeValue (V B) relation x y)
    bSet.B_ext_pair_mem_right] at houtput
  exact houtput

theorem injective_equal_outputs (relation : bSet B)
    (hinjective : ⊤ ≤ injectiveValue (V B) relation) (x y z : bSet B) :
    edgeValue (V B) relation x z ⊓ edgeValue (V B) relation y z ≤ x =ᴮ y := by
  have himp : ⊤ ≤ lattice.imp
      (edgeValue (V B) relation x z ⊓ edgeValue (V B) relation y z) (x =ᴮ y) :=
    hinjective.trans ((iInf_le _ x).trans ((iInf_le _ y).trans (iInf_le _ z)))
  exact lattice.bv_context_apply (le_top.trans himp) le_rfl

theorem countable_cover_of_injection {I : Type}
    (element : I → bSet B) (weight : I → B)
    (hseparate : ∀ i j, i ≠ j → weight i ⊓ weight j ⊓ (element i =ᴮ element j) = ⊥)
    (hcountable : ⊤ ≤ injectsIntoValue (V B) (weightedSet element weight) bSet.omega) :
    HasCountableCover weight := by
  obtain ⟨relation, hfunction, hinjective⟩ :=
    injectsInto_witness (weightedSet element weight) bSet.omega hcountable
  let rows : ℕ → I → B :=
    fun n i => weight i ⊓ edgeValue (V B) relation (element i) (bSet.ofNat n)
  refine ⟨rows, ?_, ?_⟩
  · intro n i j hne
    let context : B := rows n i ⊓ rows n j
    have hi : context ≤ edgeValue (V B) relation (element i) (bSet.ofNat n) :=
      inf_le_left.trans inf_le_right
    have hj : context ≤ edgeValue (V B) relation (element j) (bSet.ofNat n) :=
      inf_le_right.trans inf_le_right
    have heq : context ≤ element i =ᴮ element j :=
      (le_inf hi hj).trans (injective_equal_outputs relation hinjective _ _ _)
    have hweights : context ≤ weight i ⊓ weight j :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    exact bot_unique ((le_inf hweights heq).trans_eq (hseparate i j hne))
  · intro i
    change weight i ≤ ⨆ n : ℕ, weight i ⊓ edgeValue (V B) relation (element i) (bSet.ofNat n)
    rw [← inf_iSup_eq]
    exact le_inf le_rfl ((weight_le_member element weight i).trans
      (totalAt_naturals (weightedSet element weight) relation hfunction (element i)))

end Erdos597Object.BooleanFunctionFibres
