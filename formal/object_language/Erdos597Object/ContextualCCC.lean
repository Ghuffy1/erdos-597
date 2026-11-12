import Erdos597Object.PresentedCompatibility

set_option backward.isDefEq.respectTransparency false

/-! Countable-chain-condition transfer for names presented below a Boolean context. -/

namespace Erdos597Object.ContextualCCC

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanIteration BooleanAntichains
open PresentedPosets PresentedCompatibility

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem cover_of_injected_members {context : B}
    (element : I → bSet B) (weight : I → B) (domain : bSet B)
    (hcontext : ∀ i, weight i ≤ context)
    (hmembers : ∀ i, weight i ≤ element i ∈ᴮ domain)
    (hseparate : ∀ i j, i ≠ j → weight i ⊓ weight j ⊓ (element i =ᴮ element j) = ⊥)
    (hinjects : context ≤ injectsIntoValue (V B) domain bSet.omega) :
    HasCountableCover weight := by
  obtain ⟨relation, hfunction, hinjective⟩ :=
    injectsInto_witness domain bSet.omega hinjects
  let rows : ℕ → I → B := fun n i => weight i ⊓ edgeValue (V B) relation (element i) (bSet.ofNat n)
  refine ⟨rows, ?_, ?_⟩
  · intro n i j hij
    let part := rows n i ⊓ rows n j
    have hi : part ≤ weight i := inf_le_left.trans inf_le_left
    have hj : part ≤ weight j := inf_le_right.trans inf_le_left
    have hei : part ≤ edgeValue (V B) relation (element i) (bSet.ofNat n) :=
      inf_le_left.trans inf_le_right
    have hej : part ≤ edgeValue (V B) relation (element j) (bSet.ofNat n) :=
      inf_le_right.trans inf_le_right
    have heq := (le_inf (hi.trans (hcontext i)) (le_inf hei hej)).trans
      (injective_outputs relation hinjective _ _ _)
    exact bot_unique ((le_inf (le_inf hi hj) heq).trans_eq (hseparate i j hij))
  · intro i
    have ht := totalAt_labels domain relation
      (fun n : ULift ℕ => bSet.ofNat n.down) hfunction (element i)
    have hlabel : weight i ≤ ⨆ n : ULift ℕ, edgeValue (V B) relation (element i) (bSet.ofNat n.down) :=
      (le_inf (hcontext i) (hmembers i)).trans ht
    have hnat : weight i ≤ ⨆ n : ℕ, edgeValue (V B) relation (element i) (bSet.ofNat n) :=
      hlabel.trans (iSup_le fun n => le_iSup_of_le n.down le_rfl)
    change weight i ≤ ⨆ n : ℕ, weight i ⊓ edgeValue (V B) relation (element i) (bSet.ofNat n)
    rw [← inf_iSup_eq]
    exact le_inf le_rfl hnat

theorem cover_of_contextual_injection {context : B}
    (element : I → bSet B) (weight : I → B)
    (hcontext : ∀ i, weight i ≤ context)
    (hseparate : ∀ i j, i ≠ j → weight i ⊓ weight j ⊓ (element i =ᴮ element j) = ⊥)
    (hinjects : context ≤ injectsIntoValue (V B) (weightedSet element weight) bSet.omega) :
    HasCountableCover weight :=
  cover_of_injected_members element weight (weightedSet element weight) hcontext
    (weight_le_member element weight) hseparate hinjects

theorem cover_of_contextual_ccc {context : B}
    (element : I → bSet B) (weight : I → B) (domain relation : bSet B)
    (hcontext : ∀ i, weight i ≤ context)
    (hmembers : ∀ i, weight i ≤ element i ∈ᴮ domain)
    (hreflexive : ∀ i, weight i ≤ edgeValue (V B) relation (element i) (element i))
    (hincompatible : ∀ i j, i ≠ j → weight i ⊓ weight j ⊓
      Erdos597Object.compatibleValue (V B) domain relation (element i) (element j) = ⊥)
    (hccc : context ≤ countableChainConditionValue (V B) domain relation) :
    HasCountableCover weight := by
  have hanti : ⊤ ≤ antichainValue (V B) domain relation (weightedSet element weight) :=
    weighted_antichain element weight domain relation hmembers hincompatible
  have himp : context ≤ lattice.imp
      (antichainValue (V B) domain relation (weightedSet element weight))
      (injectsIntoValue (V B) (weightedSet element weight) bSet.omega) :=
    hccc.trans (iInf_le _ (weightedSet element weight))
  have hcountable := lattice.bv_context_apply himp (le_top.trans hanti)
  exact cover_of_contextual_injection element weight hcontext
    (BooleanCCCSemantics.separated_weights_of_incompatible element weight domain relation
      hmembers hreflexive hincompatible) hcountable

theorem ofNames_booleanCCC (context : B) (domain relation : bSet B)
    (element : I → bSet B) (weight : I → B)
    (hvalid : ∀ i, weight i ≤ context ∧ weight i ≤ element i ∈ᴮ domain)
    (hseparate : ∀ i j, i ≠ j → weight i ⊓ weight j ⊓ (element i =ᴮ element j) = ⊥)
    (horder : context ≤ partialOrderValue (V B) domain relation)
    (heq : context ≤ domain =ᴮ weightedSet element weight)
    (hccc : context ≤ countableChainConditionValue (V B) domain relation) :
    BooleanCountableChainCondition (ofNames context domain relation element weight hvalid hseparate horder) := by
  intro J label values hvalues hincompatible
  apply cover_of_contextual_ccc (fun j => element (label j)) values domain relation
  · intro j
    exact (hvalues j).trans (hvalid (label j)).1
  · intro j
    exact (hvalues j).trans (hvalid (label j)).2
  · intro j
    exact reflexive_at domain relation (element (label j))
      (((hvalues j).trans (hvalid (label j)).1).trans horder)
      ((hvalues j).trans (hvalid (label j)).2)
  · intro j k hjk
    let part := values j ⊓ values k ⊓
      Erdos597Object.compatibleValue (V B) domain relation (element (label j)) (element (label k))
    have hbound : part ≤ weight (label j) ⊓ weight (label k) ⊓
        Erdos597Object.compatibleValue (V B) domain relation (element (label j)) (element (label k)) :=
      le_inf (le_inf ((inf_le_left.trans inf_le_left).trans (hvalues j))
        ((inf_le_left.trans inf_le_right).trans (hvalues k))) inf_le_right
    have hcomp := hbound.trans_eq
      (compatibility_below_weights context domain relation element weight hvalid hseparate horder heq
        (label j) (label k))
    exact bot_unique ((le_inf inf_le_left hcomp).trans_eq (hincompatible j k hjk))
  · exact hccc

theorem ofNames_ccc (hB : Flypitch.BA_CCC B) (context : B) (domain relation : bSet B)
    (element : I → bSet B) (weight : I → B)
    (hvalid : ∀ i, weight i ≤ context ∧ weight i ≤ element i ∈ᴮ domain)
    (hseparate : ∀ i j, i ≠ j → weight i ⊓ weight j ⊓ (element i =ᴮ element j) = ⊥)
    (horder : context ≤ partialOrderValue (V B) domain relation)
    (heq : context ≤ domain =ᴮ weightedSet element weight)
    (hccc : context ≤ countableChainConditionValue (V B) domain relation) :
    MartinTransport.CountableChainCondition
      (Condition (ofNames context domain relation element weight hvalid hseparate horder)) :=
  two_step_ccc hB _ (ofNames_booleanCCC context domain relation element weight hvalid hseparate horder heq hccc)

end Erdos597Object.ContextualCCC
