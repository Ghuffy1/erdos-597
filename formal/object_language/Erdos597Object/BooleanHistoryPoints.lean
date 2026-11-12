import Erdos597Object.BooleanGoodSupport

set_option backward.isDefEq.respectTransparency false

/-! Ordered finite blocks extracted from compatible histories. -/

namespace Erdos597Object.BooleanHistoryPoints

open BooleanRamseyTree BooleanRamseyHistories

def historyPoint (history : List Choice) (index : ℕ) : ℕ :=
  if h : index < history.length then (history[index]'h).1 else 0

def historyBlock (history : List Choice) (k index : ℕ) : Fin k → ℕ :=
  fun a => historyPoint history (index * k + a.val)

theorem historyPoint_of_lt (history : List Choice) (index : ℕ)
    (h : index < history.length) : historyPoint history index = (history[index]'h).1 := by
  simp only [historyPoint, dite_eq_left h]

theorem historyPoint_prefix (left right : List Choice) (hprefix : left.IsPrefix right)
    (index : ℕ) (hindex : index < left.length) :
    historyPoint left index = historyPoint right index := by
  obtain ⟨extra, rfl⟩ := hprefix
  have hlarge : index < (left ++ extra).length := by
    simpa only [List.length_append] using hindex.trans_le (Nat.le_add_right left.length extra.length)
  rw [historyPoint_of_lt left index hindex, historyPoint_of_lt (left ++ extra) index hlarge]
  simp only [List.getElem_append_left hindex]

theorem historyPoint_lt (history : List Choice) (hincreasing : Increasing history)
    (left right : ℕ) (hlt : left < right) (hright : right < history.length) :
    historyPoint history left < historyPoint history right := by
  have hleft : left < history.length := hlt.trans hright
  rw [historyPoint_of_lt history left hleft, historyPoint_of_lt history right hright]
  exact hincreasing.rel_get_of_lt (a := ⟨left, hleft⟩) (b := ⟨right, hright⟩) hlt

theorem historyBlock_strict (history : List Choice) (hincreasing : Increasing history)
    (k index : ℕ) (hbound : (index + 1) * k ≤ history.length) :
    StrictMono (historyBlock history k index) := by
  intro a b hab
  apply historyPoint_lt history hincreasing _ _ (Nat.add_lt_add_left hab (index * k))
  have hinside : index * k + b.val < index * k + k := Nat.add_lt_add_left b.isLt _
  have hlength : index * k + k ≤ history.length := by
    simpa only [Nat.add_mul, Nat.one_mul] using hbound
  exact hinside.trans_le hlength

theorem historyBlock_prefix (left right : List Choice) (hprefix : left.IsPrefix right)
    (k index : ℕ) (hbound : (index + 1) * k ≤ left.length) :
    historyBlock left k index = historyBlock right k index := by
  funext a
  apply historyPoint_prefix left right hprefix
  have hinside : index * k + a.val < index * k + k := Nat.add_lt_add_left a.isLt _
  have hlength : index * k + k ≤ left.length := by
    simpa only [Nat.add_mul, Nat.one_mul] using hbound
  exact hinside.trans_le hlength

theorem historyBlock_cross_lt (history : List Choice) (hincreasing : Increasing history)
    (k i j : ℕ) (hij : i < j) (hbound : (j + 1) * k ≤ history.length)
    (a b : Fin k) : historyBlock history k i a < historyBlock history k j b := by
  have hleftBlock : i * k + a.val < (i + 1) * k := by
    simpa only [Nat.add_mul, Nat.one_mul] using Nat.add_lt_add_left a.isLt (i * k)
  have hblocks : (i + 1) * k ≤ j * k := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hij)
  have hindices : i * k + a.val < j * k + b.val :=
    (hleftBlock.trans_le hblocks).trans_le (Nat.le_add_right _ _)
  apply historyPoint_lt history hincreasing _ _ hindices
  have hinside : j * k + b.val < j * k + k := Nat.add_lt_add_left b.isLt _
  have hlength : j * k + k ≤ history.length := by
    simpa only [Nat.add_mul, Nat.one_mul] using hbound
  exact hinside.trans_le hlength

theorem historyBlock_mem_points (history : List Choice) (k index : ℕ)
    (hbound : (index + 1) * k ≤ history.length) (a : Fin k) :
    historyBlock history k index a ∈ points history := by
  have hinside : index * k + a.val < index * k + k := Nat.add_lt_add_left a.isLt _
  have hlength : index * k + k ≤ history.length := by
    simpa only [Nat.add_mul, Nat.one_mul] using hbound
  have hindex := hinside.trans_le hlength
  apply (point_mem history _).mpr
  refine ⟨history[index * k + a.val]'hindex, List.getElem_mem hindex, ?_⟩
  exact (historyPoint_of_lt history (index * k + a.val) hindex).symm

end Erdos597Object.BooleanHistoryPoints
