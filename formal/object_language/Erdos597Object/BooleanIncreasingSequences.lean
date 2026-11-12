import Erdos597Object.BooleanRowSlices

set_option backward.isDefEq.respectTransparency false

/-! Increasing omega-one sequences inside uncountable subsets of an ordered row. -/

namespace Erdos597Object.BooleanIncreasingSequences

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanNameSupports BooleanCountableNames

variable {B J : Type} [CompleteBooleanAlgebra B]

theorem bounded_before_outside (context : B) (label : Erdos597.One → bSet B)
    (order : bSet B)
    (horder : ∀ i j, i < j → (⊤ : B) ≤ edgeValue (V B) order (label i) (label j))
    (bound : Erdos597.One) (x y : bSet B)
    (hx : context ≤ x ∈ᴮ boundedName label bound)
    (hy : context ≤ y ∈ᴮ weightedSet label (fun _ => ⊤))
    (hout : context ≤ (y ∈ᴮ boundedName label bound)ᶜ) :
    context ≤ edgeValue (V B) order x y := by
  classical
  change context ≤ ⨆ i, (if i < bound then ⊤ else ⊥) ⊓ (x =ᴮ label i) at hx
  have hy' : context ≤ ⨆ j, y =ᴮ label j := by
    simpa only [member_weightedSet, top_inf_eq] using hy
  apply (le_inf le_rfl hx).trans
  apply lattice.bv_cases_right
  intro i
  by_cases hi : i < bound
  · simp only [ite_eq_left hi, top_inf_eq]
    apply (le_inf le_rfl (inf_le_left.trans hy')).trans
    apply lattice.bv_cases_right
    intro j
    let part := (context ⊓ (x =ᴮ label i)) ⊓ (y =ᴮ label j)
    change part ≤ edgeValue (V B) order x y
    have hpart : part ≤ context := inf_le_left.trans inf_le_left
    by_cases hj : j < bound
    · have hmember : part ≤ y ∈ᴮ boundedName label bound := by
        apply le_iSup_of_le j
        simpa only [ite_eq_left hj, top_inf_eq] using
          (inf_le_right : part ≤ y =ᴮ label j)
      exact ((le_inf hmember (hpart.trans hout)).trans_eq inf_compl_eq_bot).trans bot_le
    · have hij : i < j := hi.trans_le (not_lt.mp hj)
      have hground : part ≤ edgeValue (V B) order (label i) (label j) :=
        le_top.trans (horder i j hij)
      exact bSet.subst_congr_mem_left'
        (bSet.pair_congr (bSet.bv_symm (inf_le_left.trans inf_le_right))
          (bSet.bv_symm inf_le_right)) hground
  · simp only [ite_eq_right hi, bot_inf_eq, inf_bot_eq, bot_le]

theorem fresh_above [Countable J] (hB : Flypitch.BA_CCC B) (context : B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (domain order : bSet B)
    (hsubset : context ≤ domain ⊆ᴮ weightedSet label (fun _ => ⊤))
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ)
    (horder : ∀ i j, i < j → (⊤ : B) ≤ edgeValue (V B) order (label i) (label j))
    (previous : J → bSet B) :
    ∃ name : bSet B, context ≤ name ∈ᴮ domain ∧
      (∀ j, context ⊓ (previous j ∈ᴮ weightedSet label (fun _ => ⊤)) ≤
        edgeValue (V B) order (previous j) name) ∧
      ∀ j, context ⊓ (name =ᴮ previous j) = ⊥ := by
  obtain ⟨bound, hbound⟩ := family_labels_bounded hB context label hdiscrete previous
  obtain ⟨name, hname⟩ := uncountable_member_outside_countable context domain
    (boundedName label bound) hlarge (le_top.trans (bounded_countable label hdiscrete bound))
  have hmember : context ≤ name ∈ᴮ domain := hname.trans inf_le_left
  have hlabel : context ≤ name ∈ᴮ weightedSet label (fun _ => ⊤) :=
    bSet.mem_of_mem_subset' hsubset hmember
  refine ⟨name, hmember, ?_, ?_⟩
  · intro j
    let part := context ⊓ (previous j ∈ᴮ weightedSet label (fun _ => ⊤))
    have hprevious : part ≤ previous j ∈ᴮ boundedName label bound := by
      apply member_boundedName part label (previous j) bound inf_le_right
      intro i hi
      apply hbound j i
      intro hzero
      apply hi
      exact bot_unique ((inf_le_inf_right _ (show part ≤ context from inf_le_left)).trans_eq hzero)
    exact bounded_before_outside part label order horder bound (previous j) name hprevious
      (inf_le_left.trans hlabel) (inf_le_left.trans (hname.trans inf_le_right))
  · intro j
    let part := context ⊓ (name =ᴮ previous j)
    have hpreviousLabel : part ≤ previous j ∈ᴮ weightedSet label (fun _ => ⊤) :=
      bSet.subst_congr_mem_left' inf_le_right (inf_le_left.trans hlabel)
    have hpreviousBounded : part ≤ previous j ∈ᴮ boundedName label bound := by
      apply member_boundedName part label (previous j) bound hpreviousLabel
      intro i hi
      apply hbound j i
      intro hzero
      apply hi
      exact bot_unique ((inf_le_inf_right _ (show part ≤ context from inf_le_left)).trans_eq hzero)
    have hnameBounded : part ≤ name ∈ᴮ boundedName label bound :=
      bSet.subst_congr_mem_left' (bSet.bv_symm inf_le_right) hpreviousBounded
    exact bot_unique ((le_inf hnameBounded
      (inf_le_left.trans (hname.trans inf_le_right))).trans_eq inf_compl_eq_bot)

noncomputable def sequence (hB : Flypitch.BA_CCC B) (context : B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (domain order : bSet B)
    (hsubset : context ≤ domain ⊆ᴮ weightedSet label (fun _ => ⊤))
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ)
    (horder : ∀ i j, i < j → (⊤ : B) ≤ edgeValue (V B) order (label i) (label j)) :
    Erdos597.One → bSet B :=
  wellFounded_lt.fix fun i previous => by
    let : Countable (Set.Iio i) := below_countable i
    exact Classical.choose (fresh_above hB context label hdiscrete domain order hsubset hlarge horder
      (fun j : Set.Iio i => previous j.val j.property))

theorem sequence_spec (hB : Flypitch.BA_CCC B) (context : B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (domain order : bSet B)
    (hsubset : context ≤ domain ⊆ᴮ weightedSet label (fun _ => ⊤))
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ)
    (horder : ∀ i j, i < j → (⊤ : B) ≤ edgeValue (V B) order (label i) (label j))
    (i : Erdos597.One) :
    context ≤ sequence hB context label hdiscrete domain order hsubset hlarge horder i ∈ᴮ domain ∧
      (∀ j : Set.Iio i, context ⊓
        (sequence hB context label hdiscrete domain order hsubset hlarge horder j.val ∈ᴮ
          weightedSet label (fun _ => ⊤)) ≤
        edgeValue (V B) order
          (sequence hB context label hdiscrete domain order hsubset hlarge horder j.val)
          (sequence hB context label hdiscrete domain order hsubset hlarge horder i)) ∧
      ∀ j : Set.Iio i, context ⊓
        (sequence hB context label hdiscrete domain order hsubset hlarge horder i =ᴮ
          sequence hB context label hdiscrete domain order hsubset hlarge horder j.val) = ⊥ := by
  let : Countable (Set.Iio i) := below_countable i
  have heq : sequence hB context label hdiscrete domain order hsubset hlarge horder i =
      Classical.choose (fresh_above hB context label hdiscrete domain order hsubset hlarge horder
        (fun j : Set.Iio i => sequence hB context label hdiscrete domain order hsubset hlarge horder j.val)) := by
    rw [sequence, WellFounded.fix_eq]
  rw [heq]
  exact Classical.choose_spec (fresh_above hB context label hdiscrete domain order hsubset hlarge horder
    (fun j : Set.Iio i => sequence hB context label hdiscrete domain order hsubset hlarge horder j.val))

theorem exists_increasing_sequence (hB : Flypitch.BA_CCC B) (context : B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (domain order : bSet B)
    (hsubset : context ≤ domain ⊆ᴮ weightedSet label (fun _ => ⊤))
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ)
    (horder : ∀ i j, i < j → (⊤ : B) ≤ edgeValue (V B) order (label i) (label j)) :
    ∃ names : Erdos597.One → bSet B, (∀ i, context ≤ names i ∈ᴮ domain) ∧
      (∀ i j, i < j → context ≤ edgeValue (V B) order (names i) (names j)) ∧
      ∀ i j, i ≠ j → context ⊓ (names i =ᴮ names j) = ⊥ := by
  let names := sequence hB context label hdiscrete domain order hsubset hlarge horder
  have hspec := sequence_spec hB context label hdiscrete domain order hsubset hlarge horder
  refine ⟨names, fun i => (hspec i).1, ?_, ?_⟩
  · intro i j hij
    exact (le_inf le_rfl (bSet.mem_of_mem_subset' hsubset (hspec i).1)).trans
      ((hspec j).2.1 ⟨i, hij⟩)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have h := (hspec j).2.2 ⟨i, hij⟩
      exact bot_unique ((le_inf inf_le_left (bSet.bv_symm inf_le_right)).trans_eq h)
    · exact (hspec i).2.2 ⟨j, hji⟩

end Erdos597Object.BooleanIncreasingSequences
