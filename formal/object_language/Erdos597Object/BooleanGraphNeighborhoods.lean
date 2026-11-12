import Erdos597Object.BooleanUncountableSequences

set_option backward.isDefEq.respectTransparency false

/-! Countable graph neighborhoods inside arbitrary uncountable subset names. -/

namespace Erdos597Object.BooleanGraphNeighborhoods

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanLocalGraphs BooleanCountableNames

variable {B : Type} [CompleteBooleanAlgebra B]

theorem member_comprehend (predicate : bSet B → B) (hext : bSet.B_ext predicate)
    (domain name : bSet B) :
    name ∈ᴮ bSet.comprehend predicate domain = (name ∈ᴮ domain) ⊓ predicate name := by
  apply le_antisymm
  · apply ((bSet.mem_comprehend_iff₂ hext).mp le_rfl).trans
    apply iSup_le
    intro other
    apply le_inf
    · exact bSet.subst_congr_mem_left'
        (bSet.bv_symm (inf_le_right.trans inf_le_left)) inf_le_left
    · exact (le_inf (bSet.bv_symm (inf_le_right.trans inf_le_left))
        (inf_le_right.trans inf_le_right)).trans (hext other name)
  · apply (bSet.mem_comprehend_iff₂ hext).mpr
    apply le_iSup_of_le name
    exact le_inf inf_le_left (le_inf bSet.bv_refl inf_le_right)

noncomputable def neighborhood (domain relation name : bSet B) : bSet B :=
  bSet.comprehend (fun other => edgeValue (V B) relation name other) domain

theorem member_neighborhood (domain relation name other : bSet B) :
    other ∈ᴮ neighborhood domain relation name =
      (other ∈ᴮ domain) ⊓ edgeValue (V B) relation name other :=
  member_comprehend _ (edge_right_ext relation name) domain other

theorem neighborhood_subset (domain relation name : bSet B) :
    ⊤ ≤ neighborhood domain relation name ⊆ᴮ domain := bSet.comprehend_subset

theorem graph_symmetry (context : B) (ambient relation x y : bSet B)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hx : context ≤ x ∈ᴮ ambient) (hy : context ≤ y ∈ᴮ ambient) :
    context ⊓ edgeValue (V B) relation x y ≤ edgeValue (V B) relation y x := by
  have hsym := hgraph.trans (inf_le_right.trans inf_le_right)
  have hleft := lattice.bv_context_apply (hsym.trans (iInf_le _ x)) hx
  have hright := lattice.bv_context_apply (hleft.trans (iInf_le _ y)) hy
  exact lattice.le_imp_iff.mp (hright.trans inf_le_left)

theorem names_neighborhood_subset (context : B) (domain relation : bSet B)
    (names : Erdos597.One → bSet B) (hmembers : ∀ i, context ≤ names i ∈ᴮ domain)
    (i : Erdos597.One) :
    context ≤ neighborName context names (fun j k => edgeValue (V B) relation (names j) (names k)) i
      ⊆ᴮ neighborhood domain relation (names i) := by
  apply bSet.subset_intro
  intro j
  change Erdos597.One at j
  change context ⊓ (context ⊓ edgeValue (V B) relation (names i) (names j)) ≤
    names j ∈ᴮ neighborhood domain relation (names i)
  rw [member_neighborhood]
  exact le_inf (inf_le_left.trans (hmembers j)) (inf_le_right.trans inf_le_right)

theorem uncountable_independent_subname_in_ambient (hB : Flypitch.BA_CCC B) (context : B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (domain ambient relation : bSet B)
    (hsubset : context ≤ domain ⊆ᴮ weightedSet label (fun _ => ⊤))
    (hambientSubset : context ≤ domain ⊆ᴮ ambient)
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hcountable : ∀ x, context ≤ x ∈ᴮ domain →
      context ≤ injectsIntoValue (V B) (neighborhood domain relation x) bSet.omega) :
    ∃ independent : bSet B, context ≤ independent ⊆ᴮ domain ∧
      context ≤ (injectsIntoValue (V B) independent bSet.omega)ᶜ ∧
      context ≤ independentValue independent relation := by
  obtain ⟨names, hmembers, hseparate⟩ :=
    BooleanUncountableSequences.exists_discrete_sequence hB context label hdiscrete domain hsubset hlarge
  have hambient (i : Erdos597.One) : context ≤ names i ∈ᴮ ambient :=
    bSet.mem_of_mem_subset' hambientSubset (hmembers i)
  have hsymm (i j : Erdos597.One) :
      context ⊓ edgeValue (V B) relation (names i) (names j) =
        context ⊓ edgeValue (V B) relation (names j) (names i) := by
    apply le_antisymm
    · exact le_inf inf_le_left (graph_symmetry context _ relation _ _ hgraph (hambient i) (hambient j))
    · exact le_inf inf_le_left (graph_symmetry context _ relation _ _ hgraph (hambient j) (hambient i))
  have hcount (i : Erdos597.One) : context ≤ injectsIntoValue (V B)
      (neighborName context names (fun j k => edgeValue (V B) relation (names j) (names k)) i) bSet.omega :=
    subset_countable _ _ (names_neighborhood_subset context domain relation names hmembers i)
      (hcountable (names i) (hmembers i))
  obtain ⟨independent, hsub, huncountable, hindependent⟩ :=
    uncountable_independent_name hB context names hseparate relation hsymm hcount
  have hnamesSubset : context ≤ weightedSet names (fun _ => ⊤) ⊆ᴮ domain := by
    apply bSet.subset_intro
    intro i
    exact inf_le_left.trans (hmembers i)
  refine ⟨independent, ?_, huncountable, hindependent⟩
  apply bSet.subset_unfold'.mpr
  apply le_iInf
  intro x
  apply lattice.le_imp_iff.mpr
  have hx : context ⊓ (x ∈ᴮ independent) ≤ x ∈ᴮ weightedSet names (fun _ => ⊤) :=
    bSet.mem_of_mem_subset' (inf_le_left.trans hsub) inf_le_right
  exact bSet.mem_of_mem_subset' (inf_le_left.trans hnamesSubset) hx

theorem uncountable_independent_subname (hB : Flypitch.BA_CCC B) (context : B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (domain relation : bSet B)
    (hsubset : context ≤ domain ⊆ᴮ weightedSet label (fun _ => ⊤))
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ)
    (hgraph : context ≤ graphValue (V B) (weightedSet label (fun _ => ⊤)) relation)
    (hcountable : ∀ x, context ≤ x ∈ᴮ domain →
      context ≤ injectsIntoValue (V B) (neighborhood domain relation x) bSet.omega) :
    ∃ independent : bSet B, context ≤ independent ⊆ᴮ domain ∧
      context ≤ (injectsIntoValue (V B) independent bSet.omega)ᶜ ∧
      context ≤ independentValue independent relation :=
  uncountable_independent_subname_in_ambient hB context label hdiscrete domain
    (weightedSet label (fun _ => ⊤)) relation hsubset hsubset hlarge hgraph hcountable

end Erdos597Object.BooleanGraphNeighborhoods
