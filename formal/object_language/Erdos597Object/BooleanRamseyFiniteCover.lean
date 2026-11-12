import Erdos597Object.BooleanRamseyColorRules

set_option backward.isDefEq.respectTransparency false

/-! Every finite subset of the selected set is covered by one selected history. -/

namespace Erdos597Object.BooleanRamseyFiniteCover

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanRamseyTree BooleanRamseyForcing BooleanRamseySelection
open BooleanRamseyHistories BooleanRamseyColorRules BooleanPosetCoding

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def coverValue (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (filter : bSet B) (subset : Finset ℕ) : B :=
  ⨆ history : List Choice, if subset ⊆ points history then
    FilterCoefficients.values (forcing arity color initial) filter history else ⊥

theorem values_le_cover (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (filter : bSet B) (subset : Finset ℕ) (history : List Choice)
    (hsubset : subset ⊆ points history) :
    FilterCoefficients.values (forcing arity color initial) filter history ≤
      coverValue arity color initial filter subset := by
  apply le_iSup_of_le history
  simp only [hsubset, ↓reduceIte, le_refl]

theorem cover_empty (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (filter : bSet B) : coverValue arity color initial filter ∅ =
      ⨆ history : List Choice, FilterCoefficients.values (forcing arity color initial) filter history := by
  simp only [coverValue, Finset.empty_subset, ↓reduceIte]

theorem cover_singleton (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (filter : bSet B) (n : ℕ) : coverValue arity color initial filter {n} =
      selectedWeight arity color initial filter n := by
  simp only [coverValue, selectedWeight, state_points, Finset.singleton_subset_iff,
    FilterCoefficients.values, forcing]

theorem pair_cover (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (left right : List Choice) (leftSet rightSet : Finset ℕ)
    (hleft : leftSet ⊆ points left) (hright : rightSet ⊆ points right) :
    context ⊓ (FilterCoefficients.values (forcing arity color initial) filter left ⊓
      FilterCoefficients.values (forcing arity color initial) filter right) ≤
      coverValue arity color initial filter (leftSet ∪ rightSet) := by
  apply (FilterCoefficients.values_directed_at context (forcing arity color initial)
    filter hfilter left right).trans
  apply iSup_le
  intro history
  change FilterCoefficients.values (forcing arity color initial) filter history ⊓
    ((if left.IsPrefix history then weight arity color initial history else ⊥) ⊓
      (if right.IsPrefix history then weight arity color initial history else ⊥)) ≤ _
  by_cases hl : left.IsPrefix history
  · by_cases hr : right.IsPrefix history
    · have hsubset : leftSet ∪ rightSet ⊆ points history :=
        Finset.union_subset (hleft.trans (points_prefix hl)) (hright.trans (points_prefix hr))
      exact inf_le_left.trans (values_le_cover arity color initial filter _ history hsubset)
    · simp only [hr, ↓reduceIte, inf_bot_eq, bot_le]
  · simp only [hl, ↓reduceIte, bot_inf_eq, inf_bot_eq, bot_le]

theorem cover_inf (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (leftSet rightSet : Finset ℕ) :
    context ⊓ (coverValue arity color initial filter leftSet ⊓
      coverValue arity color initial filter rightSet) ≤
      coverValue arity color initial filter (leftSet ∪ rightSet) := by
  change context ⊓ ((⨆ left : List Choice, if leftSet ⊆ points left then
    FilterCoefficients.values (forcing arity color initial) filter left else ⊥) ⊓
    (⨆ right : List Choice, if rightSet ⊆ points right then
    FilterCoefficients.values (forcing arity color initial) filter right else ⊥)) ≤ _
  simp only [iSup_inf_eq, inf_iSup_eq]
  apply iSup_le
  intro right
  apply iSup_le
  intro left
  by_cases hl : leftSet ⊆ points left
  · by_cases hr : rightSet ⊆ points right
    · simpa only [hl, hr, ↓reduceIte] using
        pair_cover context arity color initial filter hfilter left right leftSet rightSet hl hr
    · simp only [hr, ↓reduceIte, inf_bot_eq, bot_le]
  · simp only [hl, ↓reduceIte, bot_inf_eq, inf_bot_eq, bot_le]

theorem finite_selected_cover (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (subset : Finset ℕ) :
    context ⊓ subset.inf (selectedWeight arity color initial filter) ≤
      coverValue arity color initial filter subset := by
  classical
  induction subset using Finset.induction_on with
  | empty =>
    rw [Finset.inf_empty, inf_top_eq, cover_empty]
    exact FilterCoefficients.values_cover_at context (forcing arity color initial) filter hfilter
  | @insert n subset hn ih =>
    rw [Finset.inf_insert]
    have hsingle : context ⊓ (selectedWeight arity color initial filter n ⊓
        subset.inf (selectedWeight arity color initial filter)) ≤
        coverValue arity color initial filter {n} := by
      rw [cover_singleton]
      exact inf_le_right.trans inf_le_left
    have hrest : context ⊓ (selectedWeight arity color initial filter n ⊓
        subset.inf (selectedWeight arity color initial filter)) ≤
        coverValue arity color initial filter subset :=
      (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans ih
    have h := (le_inf inf_le_left (le_inf hsingle hrest)).trans
      (cover_inf context arity color initial filter hfilter {n} subset)
    simpa only [Finset.singleton_union] using h

end Erdos597Object.BooleanRamseyFiniteCover
