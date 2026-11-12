import Erdos597Object.BooleanMixedRows
import Erdos597Object.BooleanRowOrder

set_option backward.isDefEq.respectTransparency false

/-! Ordered, uncountable, pairwise good row names from homogeneous blocks. -/

namespace Erdos597Object.BooleanOrderedMixedRows

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanInfiniteSets BooleanFiniteSelections BooleanRamseyTree BooleanRamseyForcing
open BooleanRamseySelection BooleanRamseyHistories BooleanHistoryPoints BooleanHistoryMixtures
open BooleanPosetCoding BooleanWeakFamilies BooleanGoodBlocks BooleanGoodPairs BooleanMixedRows
open BooleanRowOrder
open Erdos597.WeakFamilies (tupleIndex first first_tuple)

variable {B : Type} [CompleteBooleanAlgebra B]

theorem rows_before (base context : B) (hcontext : context ≤ base)
    (domain : ℕ → bSet B) (relation order : bSet B)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (hordered : ∀ r s, r < s → base ≤ allBefore order (domain r) (domain s))
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing 1 (fun _ => ⊤) initial) checkLabel)
      (orderName (forcing 1 (fun _ => ⊤) initial) checkLabel) filter)
    (hinfinite : context ≤ infiniteValue (selectedWeight 1 (fun _ => ⊤) initial filter))
    (k : ℕ) (hk : 0 < k) (i j : ℕ) (hij : i < j) :
    context ≤ allBefore order
      (rowName base context domain relation hlarge initial filter k hk i)
      (rowName base context domain relation hlarge initial filter k hk j) := by
  unfold rowName
  apply blockMixture_binary_property context 1 (fun _ => ⊤) initial filter hfilter hinfinite
    k i j ((j + 1) * k) (Nat.mul_le_mul_right k (by omega)) le_rfl _ _ (allBefore order)
  · intro right
    exact allBefore_left_ext order right
  · intro left
    exact allBefore_right_ext order left
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
      have hbefore := allBefore_restrict base order (domain (first leftIndex))
        (domain (first rightIndex))
        (sets base domain (fun _ _ => relation) hlarge leftIndex)
        (sets base domain (fun _ _ => relation) hlarge rightIndex)
        (sets_subset base domain (fun _ _ => relation) hlarge leftIndex)
        (sets_subset base domain (fun _ _ => relation) hlarge rightIndex)
        (hordered _ _ hfirst)
      exact ((historyWeight_le_context context 1 (fun _ => ⊤) initial filter _ history).trans hcontext).trans hbefore

theorem exists_ordered_rows (base context : ScheduledIteration.finalAlgebra) (hcontext : context ≤ base)
    (ambient relation order : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra) (domain r) bSet.omega)ᶜ)
    (hambient : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hordered : ∀ r s, r < s → base ≤ allBefore order (domain r) (domain s))
    (initial : ℕ → ScheduledIteration.finalAlgebra)
    (hinfinite : context ≤ infiniteValue initial) (k : ℕ) (hk : 0 < k)
    (hgood : ∀ tuple : Fin (k + k) → ℕ, StrictMono tuple →
      context ⊓ tupleWeight initial tuple ≤ goodHalves base domain (fun _ _ => relation) hlarge k hk tuple) :
    ∃ rows : ℕ → bSet ScheduledIteration.finalAlgebra,
      (∀ i, context ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra) (rows i) bSet.omega)ᶜ) ∧
      (∀ i, context ≤ rows i ⊆ᴮ ambient) ∧
      (∀ i j, i < j → context ≤ goodPair relation (rows i) (rows j)) ∧
      (∀ i j, i < j → context ≤ allBefore order (rows i) (rows j)) := by
  obtain ⟨filter, hfilter, _hsub, hselected⟩ :=
    selection_exists context 1 (fun _ => ⊤) initial hinfinite
  refine ⟨fun i => rowName base context domain relation hlarge initial filter k hk i, ?_, ?_, ?_, ?_⟩
  · intro i
    exact row_uncountable base context hcontext domain relation hlarge initial filter hfilter hselected k hk i
  · intro i
    exact row_subset base context hcontext ambient domain relation hlarge hambient initial filter
      hfilter hselected k hk i
  · intro i j hij
    exact rows_good base context domain relation hlarge initial filter hfilter hselected k hk hgood i j hij
  · intro i j hij
    exact rows_before base context hcontext domain relation order hlarge hordered initial filter
      hfilter hselected k hk i j hij

end Erdos597Object.BooleanOrderedMixedRows
