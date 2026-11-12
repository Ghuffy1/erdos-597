import Erdos597Object.BooleanAntichains

set_option backward.isDefEq.respectTransparency false

/-! The first-order CCC formula gives countable covers of weighted antichains. -/

namespace Erdos597Object.BooleanCCCSemantics

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open scoped Flypitch.bSet
open Erdos597Object.BooleanSets Erdos597Object.BooleanAntichains
open Erdos597Object.BooleanFunctionFibres Erdos597Object.BooleanIteration

variable {B : Type} [CompleteBooleanAlgebra B]

theorem separated_weights_of_incompatible {I : Type}
    (element : I → bSet B) (weight : I → B) (conditions order : bSet B)
    (hmembers : ∀ i, weight i ≤ element i ∈ᴮ conditions)
    (hreflexive : ∀ i, weight i ≤ edgeValue (V B) order (element i) (element i))
    (hincompatible : ∀ i j, i ≠ j → weight i ⊓ weight j ⊓
      Erdos597Object.compatibleValue (V B) conditions order (element i) (element j) = ⊥) :
    ∀ i j, i ≠ j → weight i ⊓ weight j ⊓ (element i =ᴮ element j) = ⊥ := by
  intro i j hne
  let context : B := weight i ⊓ weight j ⊓ (element i =ᴮ element j)
  have hweight : context ≤ weight i := inf_le_left.trans inf_le_left
  have hmember : context ≤ element i ∈ᴮ conditions := hweight.trans (hmembers i)
  have hself : context ≤ edgeValue (V B) order (element i) (element i) :=
    hweight.trans (hreflexive i)
  have hedge : context ≤ edgeValue (V B) order (element i) (element j) :=
    (le_inf inf_le_right hself).trans
      (bSet.B_ext_pair_mem_right (x := element i) (y := order) (element i) (element j))
  have hcommon : context ≤ Erdos597Object.compatibleValue (V B) conditions order
      (element i) (element j) :=
    le_iSup_of_le (element i) (le_inf hmember (le_inf hself hedge))
  exact bot_unique ((le_inf inf_le_left hcommon).trans_eq (hincompatible i j hne))

theorem countable_cover_of_firstOrder_ccc {I : Type}
    (element : I → bSet B) (weight : I → B) (conditions order : bSet B)
    (hmembers : ∀ i, weight i ≤ element i ∈ᴮ conditions)
    (hreflexive : ∀ i, weight i ≤ edgeValue (V B) order (element i) (element i))
    (hincompatible : ∀ i j, i ≠ j → weight i ⊓ weight j ⊓
      Erdos597Object.compatibleValue (V B) conditions order (element i) (element j) = ⊥)
    (hccc : ⊤ ≤ countableChainConditionValue (V B) conditions order) :
    HasCountableCover weight := by
  have hA : ⊤ ≤ antichainValue (V B) conditions order (weightedSet element weight) :=
    weighted_antichain element weight conditions order hmembers hincompatible
  have himp : ⊤ ≤ lattice.imp
      (antichainValue (V B) conditions order (weightedSet element weight))
      (injectsIntoValue (V B) (weightedSet element weight) bSet.omega) :=
    hccc.trans (iInf_le _ (weightedSet element weight))
  have hcountable := lattice.bv_context_apply himp hA
  exact countable_cover_of_injection element weight
    (separated_weights_of_incompatible element weight conditions order hmembers hreflexive hincompatible)
    hcountable

end Erdos597Object.BooleanCCCSemantics
