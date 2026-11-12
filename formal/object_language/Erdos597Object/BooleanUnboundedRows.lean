import Erdos597Object.BooleanClosedUncountability

set_option backward.isDefEq.respectTransparency false

/-! Unbounded ground-row fibers in internally uncountable bounded-row sets. -/

namespace Erdos597Object.BooleanUnboundedRows

open Erdos597 Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanWeightedSupports

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def tailValue (weight : One → B) (bound : One) : B :=
  ⨆ column : One, ⨆ (_ : bound < column), weight column

noncomputable def unboundedValue (weight : One → B) : B :=
  ⨅ bound : One, tailValue weight bound

theorem unbounded_le_tail (weight : One → B) (bound : One) :
    unboundedValue weight ≤ tailValue weight bound := iInf_le _ bound

theorem weight_le_tail (weight : One → B) (bound column : One) (h : bound < column) :
    weight column ≤ tailValue weight bound := le_iSup_of_le column (le_iSup_of_le h le_rfl)

theorem unbounded_mono (left right : One → B) (h : ∀ i, left i ≤ right i) :
    unboundedValue left ≤ unboundedValue right := by
  apply iInf_mono
  intro bound
  apply iSup_mono
  intro column
  exact iSup_mono fun _ => h column

theorem unboundedRow_cover (hB : has_dense_omega_closed_subset B) (context : B)
    (label : Vertex → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (weight : Vertex → B) (rowBound : One)
    (hrows : ∀ v, rowBound < v.1 → context ⊓ weight v = ⊥)
    (hlarge : context ≤ (injectsIntoValue (V B) (weightedSet label weight) bSet.omega)ᶜ) :
    context ≤ ⨆ row : One, unboundedValue (fun column => weight (row, column)) := by
  classical
  let cover : B := ⨆ row : One, unboundedValue (fun column => weight (row, column))
  by_contra hnot
  let part : B := context ⊓ coverᶜ
  have hpart : part ≠ ⊥ := by
    intro hzero
    apply hnot
    have hle : context ≤ coverᶜᶜ :=
      (le_compl_iff_disjoint_right).mpr (disjoint_iff.mpr hzero)
    simpa only [compl_compl] using hle
  have hcountable : Countable (Set.Iic rowBound) := (countable_initial_segment rowBound).to_subtype
  have hbounded : ∀ row : Set.Iic rowBound, part ≤
      ⨆ bound : One, (tailValue (fun column => weight (row.val, column)) bound)ᶜ := by
    intro row
    have h := (inf_le_right : part ≤ coverᶜ).trans
      (compl_le_compl (le_iSup (fun r => unboundedValue (fun column => weight (r, column))) row.val))
    simpa only [unboundedValue, compl_iInf] using h
  obtain ⟨lower, hlower, hbase, bounds, hbounds⟩ :=
    BooleanCountableDecision.decide_countable_family hB part
      (fun row : Set.Iic rowBound => fun bound => (tailValue (fun column => weight (row.val, column)) bound)ᶜ)
      hpart hbounded
  obtain ⟨columnBound, hcolumnBound⟩ := countable_family_bounded bounds
  have hsupport : {v | lower ⊓ weight v ≠ ⊥}.Countable := by
    apply ((countable_initial_segment rowBound).prod (countable_initial_segment columnBound)).mono
    intro v hv
    have hrow : v.1 ≤ rowBound := by
      by_contra h
      have hz := hrows v (lt_of_not_ge h)
      exact hv (bot_unique ((inf_le_inf_right (weight v) (hbase.trans inf_le_left)).trans_eq hz))
    refine ⟨hrow, ?_⟩
    by_contra hcolumn
    let row : Set.Iic rowBound := ⟨v.1, hrow⟩
    have htail : weight v ≤ tailValue (fun column => weight (row.val, column)) (bounds row) :=
      weight_le_tail (fun column => weight (row.val, column)) _ v.2 ((hcolumnBound row).trans (lt_of_not_ge hcolumn))
    exact hv (bot_unique ((le_inf (inf_le_left.trans (hbounds row))
      (inf_le_right.trans htail)).trans_eq compl_inf_eq_bot))
  have hsmall := countable_of_countable_support lower label hdiscrete weight hsupport
  have hnotSmall := (hbase.trans inf_le_left).trans hlarge
  exact hlower (bot_unique ((le_inf hsmall hnotSmall).trans_eq inf_compl_eq_bot))

end Erdos597Object.BooleanUnboundedRows
