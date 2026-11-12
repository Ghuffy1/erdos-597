import Erdos597Object.BooleanUncountableSequences

set_option backward.isDefEq.respectTransparency false

/-! Avoid a countable family of countable names inside an uncountable domain. -/

namespace Erdos597Object.BooleanCountableAvoidance

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanIteration ContextualCCC BooleanUncountableSequences

variable {B I J : Type} [CompleteBooleanAlgebra B]

theorem possible_members_countable (hB : Flypitch.BA_CCC B) (context : B)
    (names : I → bSet B) (hdiscrete : ∀ i j, i ≠ j → context ⊓ (names i =ᴮ names j) = ⊥)
    (small : bSet B) (hsmall : context ≤ injectsIntoValue (V B) small bSet.omega) :
    {i | context ⊓ (names i ∈ᴮ small) ≠ ⊥}.Countable := by
  have hseparate : ∀ i j, i ≠ j →
      (context ⊓ (names i ∈ᴮ small)) ⊓ (context ⊓ (names j ∈ᴮ small)) ⊓ (names i =ᴮ names j) = ⊥ := by
    intro i j hij
    exact bot_unique ((le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
      inf_le_right).trans_eq (hdiscrete i j hij))
  exact countable_support_of_cover hB _
    (cover_of_injected_members names (fun i => context ⊓ (names i ∈ᴮ small)) small
      (fun _ => inf_le_left) (fun _ => inf_le_right) hseparate hsmall)

theorem exists_avoiding_family [Countable J] (hB : Flypitch.BA_CCC B) (context : B)
    (domain : bSet B) (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (hsubset : context ≤ domain ⊆ᴮ weightedSet label (fun _ => ⊤))
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ)
    (small : J → bSet B) (hsmall : ∀ j, context ≤ injectsIntoValue (V B) (small j) bSet.omega) :
    ∃ name : bSet B, context ≤ name ∈ᴮ domain ∧ ∀ j, context ≤ (name ∈ᴮ small j)ᶜ := by
  classical
  obtain ⟨names, hmembers, hseparate⟩ :=
    exists_discrete_sequence hB context label hdiscrete domain hsubset hlarge
  have hforbidden : (⋃ j : J, {i | context ⊓ (names i ∈ᴮ small j) ≠ ⊥}).Countable :=
    Set.countable_iUnion fun j => possible_members_countable hB context names hseparate (small j) (hsmall j)
  obtain ⟨index, _, hindex⟩ := Erdos597.exists_mem_outside_countable
    (A := Set.univ) Set.not_countable_univ hforbidden
  refine ⟨names index, hmembers index, ?_⟩
  intro j
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  by_contra hnonzero
  exact hindex (Set.mem_iUnion.mpr ⟨j, hnonzero⟩)

end Erdos597Object.BooleanCountableAvoidance
