import Erdos597Object.BooleanWeightedSupports

set_option backward.isDefEq.respectTransparency false

/-! Simultaneous empty rectangles with shared Boolean index weights. -/

namespace Erdos597Object.BooleanWeightedRectangles

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanPosetCoding BooleanRectangles BooleanGoodPairs BooleanWeightedSupports

variable {B I J K : Type} [CompleteBooleanAlgebra B]

theorem refine_weights (hB : Flypitch.BA_CCC B) (context : B)
    (relation leftDomain rightDomain : bSet B) (left : I → bSet B) (right : J → bSet B)
    (hleft : ∀ i j, i ≠ j → (left i =ᴮ left j) = ⊥)
    (hright : ∀ i j, i ≠ j → (right i =ᴮ right j) = ⊥)
    (leftWeight : I → B) (rightWeight : J → B)
    (hleftMember : ∀ i, context ⊓ leftWeight i ≤ left i ∈ᴮ leftDomain)
    (hrightMember : ∀ j, context ⊓ rightWeight j ≤ right j ∈ᴮ rightDomain)
    (hleftLarge : context ≤
      (injectsIntoValue (V B) (weightedSet (checkLabel (B := B)) leftWeight) bSet.omega)ᶜ)
    (hrightLarge : context ≤
      (injectsIntoValue (V B) (weightedSet (checkLabel (B := B)) rightWeight) bSet.omega)ᶜ)
    (hgood : context ≤ goodPair relation leftDomain rightDomain) :
    ∃ newLeft : I → B, ∃ newRight : J → B,
      (∀ i, newLeft i ≤ leftWeight i) ∧ (∀ j, newRight j ≤ rightWeight j) ∧
      context ≤ (injectsIntoValue (V B) (weightedSet (checkLabel (B := B)) newLeft) bSet.omega)ᶜ ∧
      context ≤ (injectsIntoValue (V B) (weightedSet (checkLabel (B := B)) newRight) bSet.omega)ᶜ ∧
      ∀ i j, (context ⊓ newLeft i) ⊓ newRight j ≤
        (edgeValue (V B) relation (left i) (right j))ᶜ := by
  have hleftSubset : context ≤ weightedSet left leftWeight ⊆ᴮ leftDomain := by
    apply bSet.subset_intro
    exact hleftMember
  have hrightSubset : context ≤ weightedSet right rightWeight ⊆ᴮ rightDomain := by
    apply bSet.subset_intro
    exact hrightMember
  have hleftCount := countability_independent_of_labels hB (checkLabel (B := B)) left
    (fun _ _ h => checkLabel_discrete h) hleft leftWeight
  have hrightCount := countability_independent_of_labels hB (checkLabel (B := B)) right
    (fun _ _ h => checkLabel_discrete h) hright rightWeight
  have hleftUncountable : context ≤
      (injectsIntoValue (V B) (weightedSet left leftWeight) bSet.omega)ᶜ := by
    rwa [← hleftCount]
  have hrightUncountable : context ≤
      (injectsIntoValue (V B) (weightedSet right rightWeight) bSet.omega)ᶜ := by
    rwa [← hrightCount]
  obtain ⟨smallLeft, smallRight, hsmallLeft, hsmallRight, hnone⟩ :=
    goodPair_refine context relation leftDomain rightDomain
      (weightedSet left leftWeight) (weightedSet right rightWeight) hgood
      (le_inf hleftSubset hleftUncountable) (le_inf hrightSubset hrightUncountable)
  let newLeft := fun i => leftWeight i ⊓ (left i ∈ᴮ smallLeft)
  let newRight := fun j => rightWeight j ⊓ (right j ∈ᴮ smallRight)
  refine ⟨newLeft, newRight, fun _ => inf_le_left, fun _ => inf_le_left, ?_, ?_, ?_⟩
  · exact restriction_uncountable hB context left (checkLabel (B := B)) hleft
      (fun _ _ h => checkLabel_discrete h) leftWeight smallLeft
      (hsmallLeft.trans inf_le_left) (hsmallLeft.trans inf_le_right)
  · exact restriction_uncountable hB context right (checkLabel (B := B)) hright
      (fun _ _ h => checkLabel_discrete h) rightWeight smallRight
      (hsmallRight.trans inf_le_left) (hsmallRight.trans inf_le_right)
  · intro i j
    let part := (context ⊓ newLeft i) ⊓ newRight j
    exact emptyRectangle_no_edge part relation smallLeft smallRight (left i) (right j)
      ((inf_le_left.trans inf_le_left).trans hnone)
      (inf_le_left.trans (inf_le_right.trans inf_le_right))
      (inf_le_right.trans inf_le_right)

theorem finite_refinement [DecidableEq K] (hB : Flypitch.BA_CCC B) (context : B)
    (relation : bSet B) (leftDomain rightDomain : K → bSet B)
    (left : K → I → bSet B) (right : K → J → bSet B)
    (hleft : ∀ k i j, i ≠ j → (left k i =ᴮ left k j) = ⊥)
    (hright : ∀ k i j, i ≠ j → (right k i =ᴮ right k j) = ⊥)
    (hgood : ∀ k, context ≤ goodPair relation (leftDomain k) (rightDomain k))
    (indices : Finset K) (leftWeight : I → B) (rightWeight : J → B)
    (hleftMember : ∀ k i, context ⊓ leftWeight i ≤ left k i ∈ᴮ leftDomain k)
    (hrightMember : ∀ k j, context ⊓ rightWeight j ≤ right k j ∈ᴮ rightDomain k)
    (hleftLarge : context ≤
      (injectsIntoValue (V B) (weightedSet (checkLabel (B := B)) leftWeight) bSet.omega)ᶜ)
    (hrightLarge : context ≤
      (injectsIntoValue (V B) (weightedSet (checkLabel (B := B)) rightWeight) bSet.omega)ᶜ) :
    ∃ newLeft : I → B, ∃ newRight : J → B,
      (∀ i, newLeft i ≤ leftWeight i) ∧ (∀ j, newRight j ≤ rightWeight j) ∧
      context ≤ (injectsIntoValue (V B) (weightedSet (checkLabel (B := B)) newLeft) bSet.omega)ᶜ ∧
      context ≤ (injectsIntoValue (V B) (weightedSet (checkLabel (B := B)) newRight) bSet.omega)ᶜ ∧
      ∀ k ∈ indices, ∀ i j, (context ⊓ newLeft i) ⊓ newRight j ≤
        (edgeValue (V B) relation (left k i) (right k j))ᶜ := by
  induction indices using Finset.induction_on generalizing leftWeight rightWeight with
  | empty =>
    exact ⟨leftWeight, rightWeight, fun _ => le_rfl, fun _ => le_rfl,
      hleftLarge, hrightLarge, by simp⟩
  | @insert k indices hk ih =>
    obtain ⟨middleLeft, middleRight, hmiddleLeft, hmiddleRight, hlargeLeft, hlargeRight, hrest⟩ :=
      ih leftWeight rightWeight hleftMember hrightMember hleftLarge hrightLarge
    obtain ⟨newLeft, newRight, hnewLeft, hnewRight, hnewLargeLeft, hnewLargeRight, hnewNone⟩ :=
      refine_weights hB context relation (leftDomain k) (rightDomain k) (left k) (right k)
        (hleft k) (hright k) middleLeft middleRight
        (fun i => (inf_le_inf_left context (hmiddleLeft i)).trans (hleftMember k i))
        (fun j => (inf_le_inf_left context (hmiddleRight j)).trans (hrightMember k j))
        hlargeLeft hlargeRight (hgood k)
    refine ⟨newLeft, newRight, fun i => (hnewLeft i).trans (hmiddleLeft i),
      fun j => (hnewRight j).trans (hmiddleRight j), hnewLargeLeft, hnewLargeRight, ?_⟩
    intro l hl i j
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact hnewNone i j
    · exact (inf_le_inf (inf_le_inf_left context (hnewLeft i)) (hnewRight j)).trans (hrest l hl i j)

end Erdos597Object.BooleanWeightedRectangles
