import Erdos597Object.BooleanFamilyMixing
import Erdos597Object.BooleanRowRefinements

set_option backward.isDefEq.respectTransparency false

/-! Boolean values for whole ordered row families and their maximum principle. -/

namespace Erdos597Object.BooleanRowValues

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanRectangles BooleanGoodPairs BooleanRowOrder BooleanFamilyMixing

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def rowFamilyValue (ambient relation order : bSet B) (rows : ℕ → bSet B) : B :=
  (⨅ i, largeSubset ambient (rows i)) ⊓
    ⨅ i, ⨅ j, ⨅ (_ : i < j),
      goodPair relation (rows i) (rows j) ⊓ allBefore order (rows i) (rows j)

theorem rowFamilyValue_intro (context : B) (ambient relation order : bSet B)
    (rows : ℕ → bSet B)
    (hlarge : ∀ i, context ≤ (injectsIntoValue (V B) (rows i) bSet.omega)ᶜ)
    (hsubset : ∀ i, context ≤ rows i ⊆ᴮ ambient)
    (hgood : ∀ i j, i < j → context ≤ goodPair relation (rows i) (rows j))
    (hordered : ∀ i j, i < j → context ≤ allBefore order (rows i) (rows j)) :
    context ≤ rowFamilyValue ambient relation order rows :=
  le_inf (le_iInf fun i => le_inf (hsubset i) (hlarge i))
    (le_iInf fun i => le_iInf fun j => le_iInf fun hij => le_inf (hgood i j hij) (hordered i j hij))

theorem rowFamilyValue_spec (context : B) (ambient relation order : bSet B)
    (rows : ℕ → bSet B) :
    context ≤ rowFamilyValue ambient relation order rows ↔
      (∀ i, context ≤ (injectsIntoValue (V B) (rows i) bSet.omega)ᶜ) ∧
      (∀ i, context ≤ rows i ⊆ᴮ ambient) ∧
      (∀ i j, i < j → context ≤ goodPair relation (rows i) (rows j)) ∧
      (∀ i j, i < j → context ≤ allBefore order (rows i) (rows j)) := by
  constructor
  · intro h
    have hrow (i : ℕ) : context ≤ largeSubset ambient (rows i) :=
      (h.trans inf_le_left).trans (iInf_le _ i)
    have hpair (i j : ℕ) (hij : i < j) : context ≤
        goodPair relation (rows i) (rows j) ⊓ allBefore order (rows i) (rows j) :=
      (h.trans inf_le_right).trans ((iInf_le _ i).trans ((iInf_le _ j).trans (iInf_le _ hij)))
    exact ⟨fun i => (hrow i).trans inf_le_right, fun i => (hrow i).trans inf_le_left,
      fun i j hij => (hpair i j hij).trans inf_le_left,
      fun i j hij => (hpair i j hij).trans inf_le_right⟩
  · rintro ⟨hlarge, hsubset, hgood, hordered⟩
    exact rowFamilyValue_intro context ambient relation order rows hlarge hsubset hgood hordered

theorem rowFamilyValue_congr (context : B) (ambient relation order : bSet B)
    (left right : ℕ → bSet B) (hequal : ∀ i, context ≤ left i =ᴮ right i)
    (hleft : context ≤ rowFamilyValue ambient relation order left) :
    context ≤ rowFamilyValue ambient relation order right := by
  apply le_inf
  · apply le_iInf
    intro i
    have hrow : context ≤ largeSubset ambient (left i) :=
      (hleft.trans inf_le_left).trans (iInf_le _ i)
    exact (le_inf (hequal i) hrow).trans (largeSubset_ext ambient (left i) (right i))
  · apply le_iInf
    intro i
    apply le_iInf
    intro j
    apply le_iInf
    intro hij
    have hpair : context ≤ goodPair relation (left i) (left j) ⊓
        allBefore order (left i) (left j) :=
      (hleft.trans inf_le_right).trans ((iInf_le _ i).trans ((iInf_le _ j).trans (iInf_le _ hij)))
    have hgoodLeft : context ≤ goodPair relation (right i) (left j) :=
      (le_inf (hequal i) (hpair.trans inf_le_left)).trans
        (goodPair_left_ext relation (left j) (left i) (right i))
    have horderLeft : context ≤ allBefore order (right i) (left j) :=
      (le_inf (hequal i) (hpair.trans inf_le_right)).trans
        (allBefore_left_ext order (left j) (left i) (right i))
    exact le_inf
      ((le_inf (hequal j) hgoodLeft).trans (goodPair_right_ext relation (right i) (left j) (right j)))
      ((le_inf (hequal j) horderLeft).trans (allBefore_right_ext order (right i) (left j) (right j)))

theorem exists_rowFamily_of_cover (context : B) (ambient relation order : bSet B)
    (hcover : context ≤ ⨆ rows : ℕ → bSet B, rowFamilyValue ambient relation order rows) :
    ∃ rows : ℕ → bSet B, context ≤ rowFamilyValue ambient relation order rows :=
  family_fullness (rowFamilyValue ambient relation order)
    (fun part left right hequal hleft =>
      rowFamilyValue_congr part ambient relation order left right hequal hleft) context hcover

theorem exists_two_rowFamilies_of_cover (context : B) (ambient first second order : bSet B)
    (hcover : context ≤ ⨆ rows : ℕ → bSet B,
      rowFamilyValue ambient first order rows ⊓ rowFamilyValue ambient second order rows) :
    ∃ rows : ℕ → bSet B, context ≤ rowFamilyValue ambient first order rows ∧
      context ≤ rowFamilyValue ambient second order rows := by
  obtain ⟨rows, hrows⟩ := family_fullness
    (fun rows => rowFamilyValue ambient first order rows ⊓ rowFamilyValue ambient second order rows)
    (fun part left right hequal hleft => le_inf
      (rowFamilyValue_congr part ambient first order left right hequal (hleft.trans inf_le_left))
      (rowFamilyValue_congr part ambient second order left right hequal (hleft.trans inf_le_right)))
    context hcover
  exact ⟨rows, hrows.trans inf_le_left, hrows.trans inf_le_right⟩

end Erdos597Object.BooleanRowValues
