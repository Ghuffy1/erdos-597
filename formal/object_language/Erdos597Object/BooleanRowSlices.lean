import Erdos597Object.BooleanIndependentTail

set_option backward.isDefEq.respectTransparency false

/-! Uncountable canonical-row slices and labels in the actual ordinal order. -/

namespace Erdos597Object.BooleanRowSlices

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanColumns BooleanBlockOrder BooleanWeightedSupports BooleanCountableNames
open CanonicalDomains

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def orderedLabel (row : ℕ) (i : Erdos597.One) : bSet B :=
  blockLabel (row, columnEquiv.symm i)

noncomputable def slice (domain : bSet B) (row : ℕ) : bSet B :=
  weightedSet (fun i : ScheduledIteration.Labels => blockLabel (row, i))
    (fun i => blockLabel (row, i) ∈ᴮ domain)

theorem orderedLabel_discrete (row : ℕ) (i j : Erdos597.One) (hij : i ≠ j) :
    (orderedLabel (B := B) row i =ᴮ orderedLabel row j) = ⊥ := by
  apply blockLabel_discrete
  intro h
  exact hij (columnEquiv.symm.injective (congrArg Prod.snd h))

theorem orderedLabel_member (row : ℕ) (i : Erdos597.One) :
    (⊤ : B) ≤ orderedLabel row i ∈ᴮ blockDomain :=
  weight_le_member blockLabel (fun _ => ⊤) (row, columnEquiv.symm i)

theorem orderedLabel_before (row : ℕ) {i j : Erdos597.One} (hij : i < j) :
    (⊤ : B) ≤ edgeValue (V B) blockOrder (orderedLabel row i) (orderedLabel row j) := by
  rw [orderedLabel, orderedLabel, blockOrder_edge]
  have h : keyLess (row, columnEquiv.symm i) (row, columnEquiv.symm j) := by
    right
    exact ⟨rfl, by simpa only [column, Equiv.apply_symm_apply] using hij⟩
  simp only [ite_eq_left h, le_refl]

theorem slice_subset (domain : bSet B) (row : ℕ) :
    (⊤ : B) ≤ slice domain row ⊆ᴮ domain := by
  apply bSet.subset_intro
  intro i
  exact inf_le_right

theorem slice_ordered_label_cover (domain : bSet B) (row : ℕ) :
    (⊤ : B) ≤ slice domain row ⊆ᴮ weightedSet (orderedLabel row) (fun _ => ⊤) := by
  apply bSet.subset_intro
  intro i
  change (⊤ : B) ⊓ (blockLabel (row, i) ∈ᴮ domain) ≤
    blockLabel (row, i) ∈ᴮ weightedSet (orderedLabel row) (fun _ => ⊤)
  have h := weight_le_member (orderedLabel (B := B) row) (fun _ => (⊤ : B)) (column i)
  simpa only [orderedLabel, column, Equiv.symm_apply_apply] using (le_top.trans h :
    (⊤ : B) ⊓ (blockLabel (row, i) ∈ᴮ domain) ≤ _)

theorem uncountable_slice_cover (hB : Flypitch.BA_CCC B) (context : B)
    (domain : bSet B) (hsubset : context ≤ domain ⊆ᴮ blockDomain)
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ) :
    context ≤ ⨆ row : ℕ, (injectsIntoValue (V B) (slice domain row) bSet.omega)ᶜ := by
  let cover : B := ⨆ row : ℕ, (injectsIntoValue (V B) (slice domain row) bSet.omega)ᶜ
  let part := context ⊓ coverᶜ
  have hsliceCount (row : ℕ) : part ≤ injectsIntoValue (V B) (slice domain row) bSet.omega := by
    have h := compl_le_compl (le_iSup
      (fun row : ℕ => (injectsIntoValue (V B) (slice domain row) bSet.omega)ᶜ) row)
    exact (inf_le_right.trans h).trans_eq (compl_compl _)
  have hrowSupport (row : ℕ) :
      {i : ScheduledIteration.Labels | part ⊓ (blockLabel (row, i) ∈ᴮ domain) ≠ ⊥}.Countable :=
    countable_support_of_countable hB part (fun i => blockLabel (row, i))
      (fun i j hij => blockLabel_discrete _ _ (fun h => hij (congrArg Prod.snd h)))
      (fun i => blockLabel (row, i) ∈ᴮ domain) (hsliceCount row)
  have hsupport : {i : ℕ × ScheduledIteration.Labels | part ⊓ (blockLabel i ∈ᴮ domain) ≠ ⊥}.Countable := by
    have hcount : (⋃ row : ℕ, (fun i : ScheduledIteration.Labels => (row, i)) ''
        {i | part ⊓ (blockLabel (row, i) ∈ᴮ domain) ≠ ⊥}).Countable :=
      Set.countable_iUnion fun row => (hrowSupport row).image (fun i => (row, i))
    apply hcount.mono
    intro i hi
    exact Set.mem_iUnion.mpr ⟨i.1, i.2, hi, rfl⟩
  have hweightedCount := countable_of_countable_support part blockLabel blockLabel_discrete
    (fun i => blockLabel i ∈ᴮ domain) hsupport
  have hweightedSubset : part ≤ domain ⊆ᴮ weightedSet blockLabel (fun i => blockLabel i ∈ᴮ domain) := by
    simpa only [top_inf_eq] using restriction_contains part blockLabel (fun _ => (⊤ : B)) domain
      (inf_le_left.trans hsubset)
  have hcount := subset_countable domain _ hweightedSubset hweightedCount
  have hzero : part = ⊥ := bot_unique
    ((le_inf (inf_le_left.trans hlarge) hcount).trans_eq compl_inf_eq_bot)
  have h : context ≤ coverᶜᶜ := (le_compl_iff_disjoint_right).mpr (disjoint_iff.mpr hzero)
  simpa only [compl_compl] using h

end Erdos597Object.BooleanRowSlices
