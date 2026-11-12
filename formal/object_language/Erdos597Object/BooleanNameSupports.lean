import Erdos597Object.BooleanLocalGraphs

set_option backward.isDefEq.respectTransparency false

/-! Countable sets of possible ordinal labels for Boolean-valued names. -/

namespace Erdos597Object.BooleanNameSupports

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanIteration

variable {B I J : Type} [CompleteBooleanAlgebra B]

theorem possible_labels_countable (hB : Flypitch.BA_CCC B) (context : B)
    (label : I → bSet B) (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (name : bSet B) : {i | context ⊓ (name =ᴮ label i) ≠ ⊥}.Countable := by
  apply disjoint_family_support_countable hB
  intro i j hij
  have hi : (context ⊓ (name =ᴮ label i)) ⊓ (context ⊓ (name =ᴮ label j)) ≤ name =ᴮ label i :=
    inf_le_left.trans inf_le_right
  have hj : (context ⊓ (name =ᴮ label i)) ⊓ (context ⊓ (name =ᴮ label j)) ≤ name =ᴮ label j :=
    inf_le_right.trans inf_le_right
  exact bot_unique ((bSet.bv_trans (bSet.bv_symm hi) hj).trans_eq (hdiscrete i j hij))

theorem family_labels_countable [Countable J] (hB : Flypitch.BA_CCC B) (context : B)
    (label : I → bSet B) (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (names : J → bSet B) :
    (⋃ j : J, {i | context ⊓ (names j =ᴮ label i) ≠ ⊥}).Countable :=
  Set.countable_iUnion fun j => possible_labels_countable hB context label hdiscrete (names j)

theorem family_labels_bounded [Countable J] (hB : Flypitch.BA_CCC B) (context : B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥) (names : J → bSet B) :
    ∃ bound : Erdos597.One, ∀ j i, context ⊓ (names j =ᴮ label i) ≠ ⊥ → i < bound := by
  let support : Set Erdos597.One := ⋃ j : J, {i | context ⊓ (names j =ᴮ label i) ≠ ⊥}
  have hcount : support.Countable := family_labels_countable hB context label hdiscrete names
  have : Countable support := hcount.to_subtype
  obtain ⟨bound, hbound⟩ := Erdos597.countable_family_bounded (fun i : support => i.val)
  refine ⟨bound, ?_⟩
  intro j i hi
  exact hbound ⟨i, Set.mem_iUnion.mpr ⟨j, hi⟩⟩

noncomputable def boundedName (label : Erdos597.One → bSet B) (bound : Erdos597.One) : bSet B :=
  weightedSet label (fun i => if i < bound then ⊤ else ⊥)

theorem member_boundedName (context : B) (label : Erdos597.One → bSet B) (name : bSet B)
    (bound : Erdos597.One)
    (hmember : context ≤ name ∈ᴮ weightedSet label (fun _ => ⊤))
    (hbound : ∀ i, context ⊓ (name =ᴮ label i) ≠ ⊥ → i < bound) :
    context ≤ name ∈ᴮ boundedName label bound := by
  have hcover : context ≤ ⨆ i, name =ᴮ label i := by
    simpa only [member_weightedSet, top_inf_eq] using hmember
  apply (le_inf le_rfl hcover).trans
  apply lattice.bv_cases_right
  intro i
  by_cases hi : i < bound
  · exact le_iSup_of_le i (by simpa only [hi, ↓reduceIte, top_inf_eq] using
      (inf_le_right : context ⊓ (name =ᴮ label i) ≤ name =ᴮ label i))
  · have hz : context ⊓ (name =ᴮ label i) = ⊥ := by
      by_contra hne
      exact hi (hbound i hne)
    exact hz.le.trans bot_le

theorem family_members_bounded [Countable J] (hB : Flypitch.BA_CCC B) (context : B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥) (names : J → bSet B)
    (hmembers : ∀ j, context ≤ names j ∈ᴮ weightedSet label (fun _ => ⊤)) :
    ∃ bound : Erdos597.One, ∀ j, context ≤ names j ∈ᴮ boundedName label bound := by
  obtain ⟨bound, hbound⟩ := family_labels_bounded hB context label hdiscrete names
  exact ⟨bound, fun j => member_boundedName context label (names j) bound (hmembers j) (hbound j)⟩

end Erdos597Object.BooleanNameSupports
