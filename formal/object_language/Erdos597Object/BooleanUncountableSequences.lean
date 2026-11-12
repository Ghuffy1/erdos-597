import Erdos597Object.BooleanCountableNames

set_option backward.isDefEq.respectTransparency false

/-! Sequences of distinct names inside internally uncountable subsets of omega-one. -/

namespace Erdos597Object.BooleanUncountableSequences

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanNameSupports BooleanCountableNames

variable {B J : Type} [CompleteBooleanAlgebra B]

theorem fresh_member [Countable J] (hB : Flypitch.BA_CCC B) (context : B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (domain : bSet B) (hsubset : context ≤ domain ⊆ᴮ weightedSet label (fun _ => ⊤))
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ)
    (previous : J → bSet B) :
    ∃ name : bSet B, context ≤ name ∈ᴮ domain ∧
      ∀ j, context ≤ (name =ᴮ previous j)ᶜ := by
  obtain ⟨bound, hbound⟩ := family_labels_bounded hB context label hdiscrete previous
  obtain ⟨name, hname⟩ := uncountable_member_outside_countable context domain
    (boundedName label bound) hlarge (le_top.trans (bounded_countable label hdiscrete bound))
  have hmember : context ≤ name ∈ᴮ domain := hname.trans inf_le_left
  have hlabel : context ≤ name ∈ᴮ weightedSet label (fun _ => ⊤) :=
    bSet.mem_of_mem_subset' hsubset hmember
  refine ⟨name, hmember, ?_⟩
  intro j
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  let part : B := context ⊓ (name =ᴮ previous j)
  change part = ⊥
  have hprevious : part ≤ previous j ∈ᴮ weightedSet label (fun _ => ⊤) :=
    bSet.subst_congr_mem_left' inf_le_right (inf_le_left.trans hlabel)
  have hbounded : part ≤ previous j ∈ᴮ boundedName label bound := by
    apply member_boundedName part label (previous j) bound hprevious
    intro i hi
    apply hbound j i
    intro hzero
    apply hi
    apply bot_unique
    exact (inf_le_inf_right _ (show part ≤ context from inf_le_left)).trans_eq hzero
  have hnameBounded : part ≤ name ∈ᴮ boundedName label bound :=
    bSet.subst_congr_mem_left' (bSet.bv_symm inf_le_right) hbounded
  exact bot_unique ((le_inf hnameBounded (inf_le_left.trans (hname.trans inf_le_right))).trans_eq
    inf_compl_eq_bot)

noncomputable def sequence (hB : Flypitch.BA_CCC B) (context : B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (domain : bSet B) (hsubset : context ≤ domain ⊆ᴮ weightedSet label (fun _ => ⊤))
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ) :
    Erdos597.One → bSet B :=
  wellFounded_lt.fix fun i previous => by
    letI : Countable (Set.Iio i) := below_countable i
    exact Classical.choose (fresh_member hB context label hdiscrete domain hsubset hlarge
      (fun j : Set.Iio i => previous j.val j.property))

theorem sequence_spec (hB : Flypitch.BA_CCC B) (context : B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (domain : bSet B) (hsubset : context ≤ domain ⊆ᴮ weightedSet label (fun _ => ⊤))
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ) (i : Erdos597.One) :
    context ≤ sequence hB context label hdiscrete domain hsubset hlarge i ∈ᴮ domain ∧
      ∀ j : Set.Iio i, context ≤
        (sequence hB context label hdiscrete domain hsubset hlarge i =ᴮ
          sequence hB context label hdiscrete domain hsubset hlarge j.val)ᶜ := by
  have : Countable (Set.Iio i) := below_countable i
  have hseq : sequence hB context label hdiscrete domain hsubset hlarge i =
      Classical.choose (fresh_member hB context label hdiscrete domain hsubset hlarge
        (fun j : Set.Iio i => sequence hB context label hdiscrete domain hsubset hlarge j.val)) := by
    rw [sequence, WellFounded.fix_eq]
  rw [hseq]
  exact Classical.choose_spec (fresh_member hB context label hdiscrete domain hsubset hlarge
    (fun j : Set.Iio i => sequence hB context label hdiscrete domain hsubset hlarge j.val))

theorem exists_discrete_sequence (hB : Flypitch.BA_CCC B) (context : B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (domain : bSet B) (hsubset : context ≤ domain ⊆ᴮ weightedSet label (fun _ => ⊤))
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ) :
    ∃ names : Erdos597.One → bSet B, (∀ i, context ≤ names i ∈ᴮ domain) ∧
      ∀ i j, i ≠ j → context ⊓ (names i =ᴮ names j) = ⊥ := by
  let names := sequence hB context label hdiscrete domain hsubset hlarge
  have hspec := sequence_spec hB context label hdiscrete domain hsubset hlarge
  refine ⟨names, fun i => (hspec i).1, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · have h := (hspec j).2 ⟨i, hij⟩
    rw [le_compl_iff_disjoint_right, disjoint_iff] at h
    exact bot_unique ((le_inf inf_le_left (bSet.bv_symm inf_le_right)).trans_eq h)
  · have h := (hspec i).2 ⟨j, hji⟩
    rwa [le_compl_iff_disjoint_right, disjoint_iff] at h

end Erdos597Object.BooleanUncountableSequences
