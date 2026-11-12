import Erdos597Object.BooleanOrderedMixedRows

set_option backward.isDefEq.respectTransparency false

/-! Properties retained when a good row family is refined by new history blocks. -/

namespace Erdos597Object.BooleanRowRefinements

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanInfiniteSets BooleanRamseyTree BooleanRamseyForcing BooleanRamseySelection
open BooleanRamseyHistories BooleanHistoryPoints BooleanHistoryMixtures BooleanPosetCoding
open BooleanWeakFamilies BooleanGoodPairs BooleanMixedRows
open Erdos597.WeakFamilies (tupleIndex first first_tuple)

variable {B : Type} [CompleteBooleanAlgebra B]

theorem rows_preserve_good (base context : B) (hcontext : context ≤ base)
    (domain : ℕ → bSet B) (refinementRelation relation : bSet B)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (hgood : ∀ r s, r < s → base ≤ goodPair relation (domain r) (domain s))
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing 1 (fun _ => ⊤) initial) checkLabel)
      (orderName (forcing 1 (fun _ => ⊤) initial) checkLabel) filter)
    (hinfinite : context ≤ infiniteValue (selectedWeight 1 (fun _ => ⊤) initial filter))
    (k : ℕ) (hk : 0 < k) (i j : ℕ) (hij : i < j) :
    context ≤ goodPair relation
      (rowName base context domain refinementRelation hlarge initial filter k hk i)
      (rowName base context domain refinementRelation hlarge initial filter k hk j) := by
  unfold rowName
  apply blockMixture_binary_property context 1 (fun _ => ⊤) initial filter hfilter hinfinite
    k i j ((j + 1) * k) (Nat.mul_le_mul_right k (by omega)) le_rfl _ _ (goodPair relation)
  · intro right
    exact goodPair_left_ext relation right
  · intro left
    exact goodPair_right_ext relation left
  · intro history
    let part := historyWeight context 1 (fun _ => ⊤) initial filter ((j + 1) * k) history
    by_cases hzero : part = ⊥
    · change part ≤ _
      rw [hzero]
      exact bot_le
    · have hlength := historyWeight_long context 1 (fun _ => ⊤) initial filter _ history hzero
      have hleftLength : (i + 1) * k ≤ history.length :=
        (Nat.mul_le_mul_right k (by omega)).trans hlength
      have hweight : part ≤ weight 1 (fun _ => ⊤) initial history :=
        (historyWeight_le_value context 1 (fun _ => ⊤) initial filter _ history).trans inf_le_left
      have hincreasing : Increasing history := weight_nonzero_increasing 1 (fun _ => ⊤) initial history (by
        intro hz
        exact hzero (bot_unique (hweight.trans_eq hz)))
      let leftIndex := tupleIndex hk (historyBlock history k i)
      let rightIndex := tupleIndex hk (historyBlock history k j)
      have hfirst : first leftIndex < first rightIndex := by
        change first (tupleIndex hk (historyBlock history k i)) <
          first (tupleIndex hk (historyBlock history k j))
        rw [first_tuple hk _ (historyBlock_strict history hincreasing k i hleftLength),
          first_tuple hk _ (historyBlock_strict history hincreasing k j hlength)]
        exact historyBlock_cross_lt history hincreasing k i j hij hlength ⟨0, hk⟩ ⟨0, hk⟩
      have hrefined := goodPair_restrict base relation (domain (first leftIndex))
        (domain (first rightIndex))
        (sets base domain (fun _ _ => refinementRelation) hlarge leftIndex)
        (sets base domain (fun _ _ => refinementRelation) hlarge rightIndex)
        (sets_subset base domain (fun _ _ => refinementRelation) hlarge leftIndex)
        (sets_subset base domain (fun _ _ => refinementRelation) hlarge rightIndex)
        (hgood _ _ hfirst)
      exact ((historyWeight_le_context context 1 (fun _ => ⊤) initial filter _ history).trans hcontext).trans hrefined

theorem row_subset_some_target (base context : B) (hcontext : context ≤ base)
    (domain target : ℕ → bSet B) (relation : bSet B)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (htarget : ∀ r, base ≤ domain r ⊆ᴮ target r)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing 1 (fun _ => ⊤) initial) checkLabel)
      (orderName (forcing 1 (fun _ => ⊤) initial) checkLabel) filter)
    (hinfinite : context ≤ infiniteValue (selectedWeight 1 (fun _ => ⊤) initial filter))
    (k : ℕ) (hk : 0 < k) (index : ℕ) :
    context ≤ ⨆ r : ℕ,
      rowName base context domain relation hlarge initial filter k hk index ⊆ᴮ target r := by
  unfold rowName
  apply blockMixture_property context 1 (fun _ => ⊤) initial filter hfilter hinfinite k index _
    (fun name => ⨆ r : ℕ, name ⊆ᴮ target r)
  · exact bSet.B_ext_iSup fun r => bSet.B_ext_subset_left (target r)
  · intro history
    let selectedIndex := tupleIndex hk (historyBlock history k index)
    apply le_iSup_of_le (first selectedIndex)
    apply ((historyWeight_le_context context 1 (fun _ => ⊤) initial filter _ history).trans hcontext).trans
    exact BooleanUncountableRamsey.subset_trans
      (sets_subset base domain (fun _ _ => relation) hlarge selectedIndex) (htarget _)

end Erdos597Object.BooleanRowRefinements
