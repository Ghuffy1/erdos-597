import Erdos597Object.BooleanHistoryMixtures

set_option backward.isDefEq.respectTransparency false

/-! Uncountable good row names assembled from weighted finite history blocks. -/

namespace Erdos597Object.BooleanMixedRows

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanInfiniteSets BooleanFiniteSelections BooleanRamseyTree BooleanRamseyForcing
open BooleanRamseySelection BooleanRamseyHistories BooleanHistoryPoints BooleanHistoryMixtures
open BooleanPosetCoding BooleanWeakFamilies BooleanGoodBlocks BooleanGoodPairs
open Erdos597.WeakFamilies (tupleIndex appendTuple appendTuple_left appendTuple_right appendTuple_strictMono)

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def rowName (base context : B) (domain : ℕ → bSet B) (relation : bSet B)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (initial : ℕ → B) (filter : bSet B) (k : ℕ) (hk : 0 < k) (index : ℕ) : bSet B :=
  blockMixture context 1 (fun _ => ⊤) initial filter k index
    (fun tuple => sets base domain (fun _ _ => relation) hlarge (tupleIndex hk tuple))

theorem row_uncountable (base context : B) (hcontext : context ≤ base)
    (domain : ℕ → bSet B) (relation : bSet B)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing 1 (fun _ => ⊤) initial) checkLabel)
      (orderName (forcing 1 (fun _ => ⊤) initial) checkLabel) filter)
    (hinfinite : context ≤ infiniteValue (selectedWeight 1 (fun _ => ⊤) initial filter))
    (k : ℕ) (hk : 0 < k) (index : ℕ) :
    context ≤ (injectsIntoValue (V B)
      (rowName base context domain relation hlarge initial filter k hk index) bSet.omega)ᶜ := by
  unfold rowName
  apply blockMixture_property context 1 (fun _ => ⊤) initial filter hfilter hinfinite k index _
    (fun name => (injectsIntoValue (V B) name bSet.omega)ᶜ)
  · apply bSet.B_ext_compl
    simp_rw [BooleanFunctionBridge.injectsInto_eq_injects_into]
    exact bSet.B_ext_injects_into_left
  · intro history
    exact ((historyWeight_le_context context 1 (fun _ => ⊤) initial filter _ history).trans hcontext).trans
      (sets_uncountable base domain (fun _ _ => relation) hlarge _)

theorem row_subset (base context : B) (hcontext : context ≤ base)
    (ambient : bSet B) (domain : ℕ → bSet B) (relation : bSet B)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (hambient : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing 1 (fun _ => ⊤) initial) checkLabel)
      (orderName (forcing 1 (fun _ => ⊤) initial) checkLabel) filter)
    (hinfinite : context ≤ infiniteValue (selectedWeight 1 (fun _ => ⊤) initial filter))
    (k : ℕ) (hk : 0 < k) (index : ℕ) :
    context ≤ rowName base context domain relation hlarge initial filter k hk index ⊆ᴮ ambient := by
  unfold rowName
  apply blockMixture_property context 1 (fun _ => ⊤) initial filter hfilter hinfinite k index _ (fun name => name ⊆ᴮ ambient)
  · exact bSet.B_ext_subset_left ambient
  · intro history
    apply ((historyWeight_le_context context 1 (fun _ => ⊤) initial filter _ history).trans hcontext).trans
    exact BooleanUncountableRamsey.subset_trans
      (sets_subset base domain (fun _ _ => relation) hlarge _) (hambient _)

theorem rows_good (base context : B) (domain : ℕ → bSet B) (relation : bSet B)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing 1 (fun _ => ⊤) initial) checkLabel)
      (orderName (forcing 1 (fun _ => ⊤) initial) checkLabel) filter)
    (hinfinite : context ≤ infiniteValue (selectedWeight 1 (fun _ => ⊤) initial filter))
    (k : ℕ) (hk : 0 < k)
    (hgood : ∀ tuple : Fin (k + k) → ℕ, StrictMono tuple →
      context ⊓ tupleWeight initial tuple ≤ goodHalves base domain (fun _ _ => relation) hlarge k hk tuple)
    (i j : ℕ) (hij : i < j) :
    context ≤ goodPair relation
      (rowName base context domain relation hlarge initial filter k hk i)
      (rowName base context domain relation hlarge initial filter k hk j) := by
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
      let left := historyBlock history k i
      let right := historyBlock history k j
      let tuple := appendTuple left right
      have htuple : StrictMono tuple := appendTuple_strictMono left right
        (historyBlock_strict history hincreasing k i hleftLength)
        (historyBlock_strict history hincreasing k j hlength)
        (historyBlock_cross_lt history hincreasing k i j hij hlength)
      have htupleWeight : part ≤ tupleWeight initial tuple := by
        apply Finset.le_inf
        intro a _
        change part ≤ initial (appendTuple left right a)
        unfold appendTuple
        split_ifs with ha
        · have hmem : left ⟨a.val, ha⟩ ∈ (state 1 (fun _ => ⊤) initial history).1 := by
            rw [state_points]
            exact historyBlock_mem_points history k i hleftLength _
          exact hweight.trans (weight_le_point_member 1 (fun _ => ⊤) initial history _ hmem)
        · have hbound : a.val - k < k := by
            have := a.isLt
            omega
          have hmem : right ⟨a.val - k, hbound⟩ ∈ (state 1 (fun _ => ⊤) initial history).1 := by
            rw [state_points]
            exact historyBlock_mem_points history k j hlength _
          exact hweight.trans (weight_le_point_member 1 (fun _ => ⊤) initial history _ hmem)
      have hresult := (le_inf (historyWeight_le_context context 1 (fun _ => ⊤) initial filter _ history)
        htupleWeight).trans (hgood tuple htuple)
      simpa only [tuple, goodHalves, appendTuple_left, appendTuple_right] using hresult

end Erdos597Object.BooleanMixedRows
