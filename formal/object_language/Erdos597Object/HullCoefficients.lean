import Erdos597Object.BooleanNameHull
import Erdos597Object.SeparatedNames

set_option backward.isDefEq.respectTransparency false

/-! Transfer compatibility and density from a witness-closed family to its separated presentation. -/

namespace Erdos597Object.HullCoefficients

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanAntichains PresentedPosets PresentedCompatibility

variable {B I D : Type} [CompleteBooleanAlgebra B]

theorem covered_predicate {bound : B} (element : I → bSet B) (weight : I → B)
    (x : bSet B) (predicate : bSet B → B) (hext : bSet.B_ext predicate)
    (hcover : bound ≤ x ∈ᴮ weightedSet element weight) (hpredicate : bound ≤ predicate x) :
    bound ≤ ⨆ i, weight i ⊓ predicate (element i) := by
  have h : bound ≤ ⨆ y : bSet B, (y ∈ᴮ weightedSet element weight) ⊓ predicate y :=
    le_iSup_of_le x (le_inf hcover hpredicate)
  rw [weighted_bounded_exists element weight predicate hext] at h
  exact h

theorem compatible_le (context : B) (domain relation : bSet B)
    (element : I → bSet B) (weight : I → B)
    (hvalid : ∀ i, weight i ≤ context ∧ weight i ≤ element i ∈ᴮ domain)
    (hseparate : ∀ i j, i ≠ j → weight i ⊓ weight j ⊓ (element i =ᴮ element j) = ⊥)
    (horder : context ≤ partialOrderValue (V B) domain relation)
    (hcover : ∀ i, context ≤ element i ∈ᴮ weightedSet element weight)
    (hcommon : ∀ i j, ∃ k, context ⊓ Erdos597Object.compatibleValue (V B) domain relation
      (element i) (element j) ≤ edgeValue (V B) relation (element k) (element i) ⊓
        edgeValue (V B) relation (element k) (element j)) (i j : I) :
    weight i ⊓ weight j ⊓ Erdos597Object.compatibleValue (V B) domain relation (element i) (element j) ≤
      BooleanIteration.compatibleValue (ofNames context domain relation element weight hvalid hseparate horder) i j := by
  let part := weight i ⊓ weight j ⊓
    Erdos597Object.compatibleValue (V B) domain relation (element i) (element j)
  have hi : part ≤ weight i := inf_le_left.trans inf_le_left
  have hj : part ≤ weight j := inf_le_left.trans inf_le_right
  have hc : part ≤ context := hi.trans (hvalid i).1
  obtain ⟨k, hk⟩ := hcommon i j
  have hsum := covered_predicate element weight (element k) _
    (compatibleWitness_ext relation (element i) (element j)) (hc.trans (hcover k))
    ((le_inf hc inf_le_right).trans hk)
  rw [ofNames_compatibility]
  exact le_inf (le_inf hi hj) hsum

theorem booleanCCC (context : B) (domain relation : bSet B)
    (element : I → bSet B) (weight : I → B)
    (hvalid : ∀ i, weight i ≤ context ∧ weight i ≤ element i ∈ᴮ domain)
    (hseparate : ∀ i j, i ≠ j → weight i ⊓ weight j ⊓ (element i =ᴮ element j) = ⊥)
    (horder : context ≤ partialOrderValue (V B) domain relation)
    (hcover : ∀ i, context ≤ element i ∈ᴮ weightedSet element weight)
    (hcommon : ∀ i j, ∃ k, context ⊓ Erdos597Object.compatibleValue (V B) domain relation
      (element i) (element j) ≤ edgeValue (V B) relation (element k) (element i) ⊓
        edgeValue (V B) relation (element k) (element j))
    (hccc : context ≤ countableChainConditionValue (V B) domain relation) :
    BooleanIteration.BooleanCountableChainCondition (ofNames context domain relation element weight hvalid hseparate horder) := by
  intro J label values hvalues hincompatible
  apply ContextualCCC.cover_of_contextual_ccc (fun j => element (label j)) values domain relation
  · intro j
    exact (hvalues j).trans (hvalid (label j)).1
  · intro j
    exact (hvalues j).trans (hvalid (label j)).2
  · intro j
    exact reflexive_at domain relation (element (label j))
      (((hvalues j).trans (hvalid (label j)).1).trans horder)
      ((hvalues j).trans (hvalid (label j)).2)
  · intro j k hjk
    let part := values j ⊓ values k ⊓ Erdos597Object.compatibleValue (V B) domain relation
      (element (label j)) (element (label k))
    have hbound : part ≤ weight (label j) ⊓ weight (label k) ⊓
        Erdos597Object.compatibleValue (V B) domain relation (element (label j)) (element (label k)) :=
      le_inf (le_inf ((inf_le_left.trans inf_le_left).trans (hvalues j))
        ((inf_le_left.trans inf_le_right).trans (hvalues k))) inf_le_right
    have hcomp := hbound.trans (compatible_le context domain relation element weight
      hvalid hseparate horder hcover hcommon (label j) (label k))
    exact bot_unique ((le_inf inf_le_left hcomp).trans_eq (hincompatible j k hjk))
  · exact hccc

theorem dense_coefficients (context : B) (domain relation : bSet B)
    (element : I → bSet B) (weight : I → B)
    (hcontext : ∀ i, weight i ≤ context)
    (hcover : ∀ i, context ≤ element i ∈ᴮ weightedSet element weight)
    (active : D → B) (denseSet : D → bSet B)
    (hdense : ∀ d j, ∃ k, context ⊓ active d ≤
      (element k ∈ᴮ denseSet d) ⊓ edgeValue (V B) relation (element k) (element j)) (d : D) (j : I) :
    active d ⊓ weight j ≤ ⨆ i, (weight i ⊓ (element i ∈ᴮ denseSet d)) ⊓
      (weight i ⊓ weight j ⊓ edgeValue (V B) relation (element i) (element j)) := by
  let part := active d ⊓ weight j
  have hc : part ≤ context := inf_le_right.trans (hcontext j)
  obtain ⟨k, hk⟩ := hdense d j
  have hsum := covered_predicate element weight (element k)
    (fun x => (x ∈ᴮ denseSet d) ⊓ edgeValue (V B) relation x (element j))
    (bSet.B_ext_inf (bSet.B_ext_mem_left (denseSet d)) (edge_left_ext relation (element j)))
    (hc.trans (hcover k)) ((le_inf hc inf_le_left).trans hk)
  calc
    part ≤ weight j ⊓ (⨆ i, weight i ⊓
        ((element i ∈ᴮ denseSet d) ⊓ edgeValue (V B) relation (element i) (element j))) :=
      le_inf inf_le_right hsum
    _ = _ := by
      rw [inf_iSup_eq]
      apply iSup_congr
      intro i
      simp only [inf_assoc, inf_left_comm, inf_comm, inf_left_idem]

end Erdos597Object.HullCoefficients
