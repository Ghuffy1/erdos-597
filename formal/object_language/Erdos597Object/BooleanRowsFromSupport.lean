import Erdos597Object.BooleanRowValues
import Erdos597Object.BooleanOrientedSupport

set_option backward.isDefEq.respectTransparency false

/-! Extract whole ordered row families from each oriented good-block support. -/

namespace Erdos597Object.BooleanRowsFromSupport

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanRowValues BooleanOrderedMixedRows BooleanRowRefinements BooleanMixedRows
open BooleanGoodSupport BooleanGoodBlocks BooleanRamseyAlternatives BooleanFiniteSelections
open BooleanRamseySelection BooleanInfiniteSets BooleanRamseyTree BooleanRamseyForcing
open BooleanPosetCoding BooleanGoodPairs BooleanRowOrder BooleanFamilyMixing

theorem goodSupport_le_rowFamily (base : ScheduledIteration.finalAlgebra)
    (ambient relation order : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra) (domain r) bSet.omega)ᶜ)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hordered : ∀ r s, r < s → base ≤ allBefore order (domain r) (domain s))
    (k : ℕ) (hk : 0 < k) :
    base ⊓ goodSupport (k + k) (goodHalves base domain (fun _ _ => relation) hlarge k hk) ≤
      ⨆ rows, rowFamilyValue ambient relation order rows := by
  unfold goodSupport
  rw [sSup_eq_iSup]
  simp only [inf_iSup_eq]
  apply iSup_le
  intro part
  apply iSup_le
  rintro ⟨initial, hinfinite, hgood⟩
  obtain ⟨rows, hrowLarge, hrowSubset, hrowGood, hrowOrder⟩ :=
    exists_ordered_rows base (base ⊓ part) inf_le_left ambient relation order domain
      hlarge hsubset hordered initial (inf_le_right.trans hinfinite) k hk (by
        intro tuple htuple
        exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans (hgood tuple htuple))
  exact le_iSup_of_le rows
    (rowFamilyValue_intro (base ⊓ part) ambient relation order rows
      hrowLarge hrowSubset hrowGood hrowOrder)

theorem blockSupport_le_rowFamily (base : ScheduledIteration.finalAlgebra)
    (ambient relation order : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra) (domain r) bSet.omega)ᶜ)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hordered : ∀ r s, r < s → base ≤ allBefore order (domain r) (domain s)) (n : ℕ) :
    base ⊓ blockSupport base domain relation hlarge n ≤
      ⨆ rows, rowFamilyValue ambient relation order rows := by
  unfold blockSupport
  simp only [inf_iSup_eq]
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  apply iSup_le
  intro _hkn
  exact goodSupport_le_rowFamily base ambient relation order domain hlarge hsubset hordered k hk

theorem exists_rows_of_blockSupport (base : ScheduledIteration.finalAlgebra)
    (ambient relation order : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra) (domain r) bSet.omega)ᶜ)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hordered : ∀ r s, r < s → base ≤ allBefore order (domain r) (domain s)) (n : ℕ)
    (hsupport : base ≤ blockSupport base domain relation hlarge n) :
    ∃ rows, base ≤ rowFamilyValue ambient relation order rows :=
  exists_rowFamily_of_cover base ambient relation order
    ((le_inf le_rfl hsupport).trans
      (blockSupport_le_rowFamily base ambient relation order domain hlarge hsubset hordered n))

theorem exists_ordered_rows_preserving (base context : ScheduledIteration.finalAlgebra)
    (hcontext : context ≤ base)
    (ambient previous relation order : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra) (domain r) bSet.omega)ᶜ)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hordered : ∀ r s, r < s → base ≤ allBefore order (domain r) (domain s))
    (hprevious : ∀ r s, r < s → base ≤ goodPair previous (domain r) (domain s))
    (initial : ℕ → ScheduledIteration.finalAlgebra) (hinfinite : context ≤ infiniteValue initial)
    (k : ℕ) (hk : 0 < k)
    (hgood : ∀ tuple : Fin (k + k) → ℕ, StrictMono tuple →
      context ⊓ tupleWeight initial tuple ≤ goodHalves base domain (fun _ _ => relation) hlarge k hk tuple) :
    ∃ rows, context ≤ rowFamilyValue ambient previous order rows ∧
      context ≤ rowFamilyValue ambient relation order rows := by
  obtain ⟨filter, hfilter, _hsub, hselected⟩ :=
    selection_exists context 1 (fun _ => ⊤) initial hinfinite
  let rows := fun i => rowName base context domain relation hlarge initial filter k hk i
  have hrowLarge (i : ℕ) : context ≤
      (injectsIntoValue (V ScheduledIteration.finalAlgebra) (rows i) bSet.omega)ᶜ :=
    row_uncountable base context hcontext domain relation hlarge initial filter hfilter hselected k hk i
  have hrowSubset (i : ℕ) : context ≤ rows i ⊆ᴮ ambient :=
    row_subset base context hcontext ambient domain relation hlarge hsubset initial filter
      hfilter hselected k hk i
  have hrowOrder (i j : ℕ) (hij : i < j) : context ≤ allBefore order (rows i) (rows j) :=
    rows_before base context hcontext domain relation order hlarge hordered initial filter
      hfilter hselected k hk i j hij
  refine ⟨rows, rowFamilyValue_intro context ambient previous order rows
    hrowLarge hrowSubset ?_ hrowOrder,
    rowFamilyValue_intro context ambient relation order rows hrowLarge hrowSubset ?_ hrowOrder⟩
  · intro i j hij
    exact rows_preserve_good base context hcontext domain relation previous hlarge hprevious initial filter
      hfilter hselected k hk i j hij
  · intro i j hij
    exact rows_good base context domain relation hlarge initial filter hfilter hselected k hk hgood i j hij

theorem goodSupport_le_two_rowFamilies (base : ScheduledIteration.finalAlgebra)
    (ambient previous relation order : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra) (domain r) bSet.omega)ᶜ)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hordered : ∀ r s, r < s → base ≤ allBefore order (domain r) (domain s))
    (hprevious : ∀ r s, r < s → base ≤ goodPair previous (domain r) (domain s))
    (k : ℕ) (hk : 0 < k) :
    base ⊓ goodSupport (k + k) (goodHalves base domain (fun _ _ => relation) hlarge k hk) ≤
      ⨆ rows, rowFamilyValue ambient previous order rows ⊓ rowFamilyValue ambient relation order rows := by
  unfold goodSupport
  rw [sSup_eq_iSup]
  simp only [inf_iSup_eq]
  apply iSup_le
  intro part
  apply iSup_le
  rintro ⟨initial, hinfinite, hgood⟩
  obtain ⟨rows, hfirst, hsecond⟩ :=
    exists_ordered_rows_preserving base (base ⊓ part) inf_le_left ambient previous relation order domain
      hlarge hsubset hordered hprevious initial (inf_le_right.trans hinfinite) k hk (by
        intro tuple htuple
        exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans (hgood tuple htuple))
  exact le_iSup_of_le rows (le_inf hfirst hsecond)

theorem exists_two_rows_of_blockSupport (base : ScheduledIteration.finalAlgebra)
    (ambient previous relation order : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra) (domain r) bSet.omega)ᶜ)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hordered : ∀ r s, r < s → base ≤ allBefore order (domain r) (domain s))
    (hprevious : ∀ r s, r < s → base ≤ goodPair previous (domain r) (domain s)) (n : ℕ)
    (hsupport : base ≤ blockSupport base domain relation hlarge n) :
    ∃ rows, base ≤ rowFamilyValue ambient previous order rows ∧
      base ≤ rowFamilyValue ambient relation order rows := by
  apply exists_two_rowFamilies_of_cover base ambient previous relation order
  apply (le_inf le_rfl hsupport).trans
  unfold blockSupport
  simp only [inf_iSup_eq]
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  apply iSup_le
  intro _hkn
  exact goodSupport_le_two_rowFamilies base ambient previous relation order domain
    hlarge hsubset hordered hprevious k hk

end Erdos597Object.BooleanRowsFromSupport
