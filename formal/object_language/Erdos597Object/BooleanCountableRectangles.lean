import Erdos597Object.BooleanRectangles

set_option backward.isDefEq.respectTransparency false

/-! Empty uncountable rectangles for relations with countable fibres on both sides. -/

namespace Erdos597Object.BooleanCountableRectangles

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanLocalGraphs BooleanGraphNeighborhoods BooleanCountableNames
open BooleanUncountableSequences BooleanRectangles

variable {B I J : Type} [CompleteBooleanAlgebra B]

noncomputable def predecessors (domain relation name : bSet B) : bSet B :=
  bSet.comprehend (fun other => edgeValue (V B) relation other name) domain

theorem member_predecessors (domain relation name other : bSet B) :
    other ∈ᴮ predecessors domain relation name =
      (other ∈ᴮ domain) ⊓ edgeValue (V B) relation other name :=
  member_comprehend _ (edge_left_ext relation name) domain other

theorem weighted_neighborhood_subset (context : B) (domain relation name : bSet B)
    (names : I → bSet B) (hmembers : ∀ i, context ≤ names i ∈ᴮ domain) :
    context ≤ weightedSet names (fun i => context ⊓ edgeValue (V B) relation name (names i))
      ⊆ᴮ neighborhood domain relation name := by
  apply bSet.subset_intro
  intro i
  rw [member_neighborhood]
  exact le_inf (inf_le_left.trans (hmembers i)) (inf_le_right.trans inf_le_right)

theorem weighted_predecessors_subset (context : B) (domain relation name : bSet B)
    (names : I → bSet B) (hmembers : ∀ i, context ≤ names i ∈ᴮ domain) :
    context ≤ weightedSet names (fun i => context ⊓ edgeValue (V B) relation (names i) name)
      ⊆ᴮ predecessors domain relation name := by
  apply bSet.subset_intro
  intro i
  rw [member_predecessors]
  exact le_inf (inf_le_left.trans (hmembers i)) (inf_le_right.trans inf_le_right)

theorem subsetName_in_domain (context : B) (domain : bSet B) (names : I → bSet B)
    (hmembers : ∀ i, context ≤ names i ∈ᴮ domain) (indices : Set I) :
    context ≤ subsetName context names indices ⊆ᴮ domain := by
  apply bSet.subset_intro
  intro i
  exact inf_le_left.trans (hmembers i.val)

theorem subsetName_empty_rectangle (context : B) (relation : bSet B)
    (leftNames : I → bSet B) (rightNames : J → bSet B) (leftIndices : Set I) (rightIndices : Set J)
    (hnone : ∀ i ∈ leftIndices, ∀ j ∈ rightIndices,
      context ⊓ edgeValue (V B) relation (leftNames i) (rightNames j) = ⊥) :
    context ≤ emptyRectangle relation (subsetName context leftNames leftIndices)
      (subsetName context rightNames rightIndices) := by
  rw [emptyRectangle_spec]
  unfold subsetName
  rw [weighted_bounded_forall _ _ _ (bSet.B_ext_iInf fun y =>
    bSet.B_ext_imp (bSet.B_ext_const _) (bSet.B_ext_compl (edge_left_ext relation y)))]
  apply le_iInf
  intro i
  apply lattice.bv_imp_intro
  rw [weighted_bounded_forall _ _ _ (bSet.B_ext_compl (edge_right_ext relation (leftNames i.val)))]
  apply le_iInf
  intro j
  apply lattice.bv_imp_intro
  have hred : context ≤ (edgeValue (V B) relation (leftNames i.val) (rightNames j.val))ᶜ := by
    rw [le_compl_iff_disjoint_right, disjoint_iff]
    exact hnone i.val i.property j.val j.property
  exact (inf_le_left.trans inf_le_left).trans hred

theorem countable_named_rectangle (hB : Flypitch.BA_CCC B) (context : B)
    (relation left right : bSet B) (leftNames rightNames : Erdos597.One → bSet B)
    (hleftMembers : ∀ i, context ≤ leftNames i ∈ᴮ left)
    (hrightMembers : ∀ i, context ≤ rightNames i ∈ᴮ right)
    (hleftDiscrete : ∀ i j, i ≠ j → context ⊓ (leftNames i =ᴮ leftNames j) = ⊥)
    (hrightDiscrete : ∀ i j, i ≠ j → context ⊓ (rightNames i =ᴮ rightNames j) = ⊥)
    (hleftCountable : ∀ i, context ≤ injectsIntoValue (V B)
      (neighborName context rightNames (fun i j => edgeValue (V B) relation (leftNames i) (rightNames j)) i)
      bSet.omega)
    (hrightCountable : ∀ j, context ≤ injectsIntoValue (V B)
      (neighborName context leftNames (fun j i => edgeValue (V B) relation (leftNames i) (rightNames j)) j)
      bSet.omega) :
    ∃ smallLeft smallRight : bSet B, context ≤ largeSubset left smallLeft ∧
      context ≤ largeSubset right smallRight ∧ context ≤ emptyRectangle relation smallLeft smallRight := by
  classical
  let possible := fun i j => context ⊓ edgeValue (V B) relation (leftNames i) (rightNames j) ≠ ⊥
  have hleft (i : Erdos597.One) : {j | possible i j}.Countable :=
    possible_neighbors_countable hB context rightNames hrightDiscrete
      (fun i j => edgeValue (V B) relation (leftNames i) (rightNames j)) i (hleftCountable i)
  have hright (j : Erdos597.One) : {i | possible i j}.Countable :=
    possible_neighbors_countable hB context leftNames hleftDiscrete
      (fun j i => edgeValue (V B) relation (leftNames i) (rightNames j)) j (hrightCountable j)
  obtain ⟨leftIndices, _, hlargeLeft, rightIndices, _, hlargeRight, hnone⟩ :=
    Erdos597.uncountable_empty_rectangle possible Set.univ Set.univ
      Set.not_countable_univ Set.not_countable_univ
      (fun i _ => by simpa only [Set.mem_univ, true_and] using hleft i)
      (fun j _ => by simpa only [Set.mem_univ, true_and] using hright j)
  refine ⟨subsetName context leftNames leftIndices, subsetName context rightNames rightIndices,
    le_inf (subsetName_in_domain context left leftNames hleftMembers leftIndices)
      (subsetName_not_countable hB context leftNames hleftDiscrete leftIndices hlargeLeft),
    le_inf (subsetName_in_domain context right rightNames hrightMembers rightIndices)
      (subsetName_not_countable hB context rightNames hrightDiscrete rightIndices hlargeRight), ?_⟩
  apply subsetName_empty_rectangle
  intro i hi j hj
  by_contra hnonzero
  exact hnone i hi j hj hnonzero

theorem countable_fibres_rectangle (hB : Flypitch.BA_CCC B) (context : B)
    (relation left right : bSet B) (leftLabels rightLabels : Erdos597.One → bSet B)
    (hleftDiscrete : ∀ i j, i ≠ j → (leftLabels i =ᴮ leftLabels j) = ⊥)
    (hrightDiscrete : ∀ i j, i ≠ j → (rightLabels i =ᴮ rightLabels j) = ⊥)
    (hleftSubset : context ≤ left ⊆ᴮ weightedSet leftLabels (fun _ => ⊤))
    (hrightSubset : context ≤ right ⊆ᴮ weightedSet rightLabels (fun _ => ⊤))
    (hleftLarge : context ≤ (injectsIntoValue (V B) left bSet.omega)ᶜ)
    (hrightLarge : context ≤ (injectsIntoValue (V B) right bSet.omega)ᶜ)
    (hleftCountable : ∀ x, context ≤ x ∈ᴮ left →
      context ≤ injectsIntoValue (V B) (neighborhood right relation x) bSet.omega)
    (hrightCountable : ∀ y, context ≤ y ∈ᴮ right →
      context ≤ injectsIntoValue (V B) (predecessors left relation y) bSet.omega) :
    ∃ smallLeft smallRight : bSet B, context ≤ largeSubset left smallLeft ∧
      context ≤ largeSubset right smallRight ∧ context ≤ emptyRectangle relation smallLeft smallRight := by
  obtain ⟨leftNames, hleftMembers, hleftSeparate⟩ :=
    exists_discrete_sequence hB context leftLabels hleftDiscrete left hleftSubset hleftLarge
  obtain ⟨rightNames, hrightMembers, hrightSeparate⟩ :=
    exists_discrete_sequence hB context rightLabels hrightDiscrete right hrightSubset hrightLarge
  apply countable_named_rectangle hB context relation left right leftNames rightNames
    hleftMembers hrightMembers hleftSeparate hrightSeparate
  · intro i
    exact subset_countable _ _
      (weighted_neighborhood_subset context right relation (leftNames i) rightNames hrightMembers)
      (hleftCountable (leftNames i) (hleftMembers i))
  · intro j
    exact subset_countable _ _
      (weighted_predecessors_subset context left relation (rightNames j) leftNames hleftMembers)
      (hrightCountable (rightNames j) (hrightMembers j))

end Erdos597Object.BooleanCountableRectangles
