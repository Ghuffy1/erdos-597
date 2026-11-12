import Erdos597Object.BooleanIncreasingSequences

set_option backward.isDefEq.respectTransparency false

/-! An increasing omega-one sequence in every uncountable canonical block subset. -/

namespace Erdos597Object.BooleanOrderedSubsets

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanFamilyMixing BooleanRowSlices BooleanIncreasingSequences
open CanonicalDomains

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def sequenceValue (domain order : bSet B) (names : Erdos597.One → bSet B) : B :=
  (⨅ i, names i ∈ᴮ domain) ⊓
    ((⨅ i, ⨅ j, ⨅ (_ : i < j), edgeValue (V B) order (names i) (names j)) ⊓
      ⨅ i, ⨅ j, ⨅ (_ : i ≠ j), (names i =ᴮ names j)ᶜ)

theorem sequenceValue_intro (context : B) (domain order : bSet B)
    (names : Erdos597.One → bSet B)
    (hmembers : ∀ i, context ≤ names i ∈ᴮ domain)
    (horder : ∀ i j, i < j → context ≤ edgeValue (V B) order (names i) (names j))
    (hdiscrete : ∀ i j, i ≠ j → context ⊓ (names i =ᴮ names j) = ⊥) :
    context ≤ sequenceValue domain order names := by
  apply le_inf (le_iInf hmembers)
  apply le_inf
  · exact le_iInf fun i => le_iInf fun j => le_iInf fun hij => horder i j hij
  · exact le_iInf fun i => le_iInf fun j => le_iInf fun hij =>
      (le_compl_iff_disjoint_right).mpr (disjoint_iff.mpr (hdiscrete i j hij))

theorem sequenceValue_spec (context : B) (domain order : bSet B)
    (names : Erdos597.One → bSet B) (h : context ≤ sequenceValue domain order names) :
    (∀ i, context ≤ names i ∈ᴮ domain) ∧
      (∀ i j, i < j → context ≤ edgeValue (V B) order (names i) (names j)) ∧
      ∀ i j, i ≠ j → context ⊓ (names i =ᴮ names j) = ⊥ := by
  refine ⟨fun i => (h.trans inf_le_left).trans (iInf_le _ i), ?_, ?_⟩
  · intro i j hij
    exact (h.trans (inf_le_right.trans inf_le_left)).trans
      ((iInf_le _ i).trans ((iInf_le _ j).trans (iInf_le _ hij)))
  · intro i j hij
    have hnot := (h.trans (inf_le_right.trans inf_le_right)).trans
      ((iInf_le _ i).trans ((iInf_le _ j).trans (iInf_le _ hij)))
    exact disjoint_iff.mp ((le_compl_iff_disjoint_right).mp hnot)

theorem sequenceValue_congr (context : B) (domain order : bSet B)
    (left right : Erdos597.One → bSet B) (heq : ∀ i, context ≤ left i =ᴮ right i)
    (hleft : context ≤ sequenceValue domain order left) :
    context ≤ sequenceValue domain order right := by
  obtain ⟨hmembers, horder, hdiscrete⟩ := sequenceValue_spec context domain order left hleft
  apply sequenceValue_intro
  · intro i
    exact (le_inf (heq i) (hmembers i)).trans (bSet.B_ext_mem_left domain (left i) (right i))
  · intro i j hij
    have hfirst := (le_inf (heq i) (horder i j hij)).trans
      (edge_left_ext order (left j) (left i) (right i))
    exact (le_inf (heq j) hfirst).trans (edge_right_ext order (right i) (left j) (right j))
  · intro i j hij
    let part := context ⊓ (right i =ᴮ right j)
    have hsame : part ≤ left i =ᴮ left j :=
      bSet.bv_trans (inf_le_left.trans (heq i))
        (bSet.bv_trans inf_le_right (bSet.bv_symm (inf_le_left.trans (heq j))))
    exact bot_unique ((le_inf inf_le_left hsame).trans_eq (hdiscrete i j hij))

theorem slice_sequence (hB : Flypitch.BA_CCC B) (context : B) (domain : bSet B) (row : ℕ)
    (hlarge : context ≤ (injectsIntoValue (V B) (slice domain row) bSet.omega)ᶜ) :
    ∃ names : Erdos597.One → bSet B, context ≤ sequenceValue domain blockOrder names := by
  obtain ⟨names, hmembers, horder, hdiscrete⟩ := exists_increasing_sequence hB context
    (orderedLabel row) (orderedLabel_discrete row) (slice domain row) blockOrder
    (le_top.trans (slice_ordered_label_cover domain row)) hlarge
    (fun _ _ hij => orderedLabel_before row hij)
  exact ⟨names, sequenceValue_intro context domain blockOrder names
    (fun i => bSet.mem_of_mem_subset' (le_top.trans (slice_subset domain row)) (hmembers i))
    horder hdiscrete⟩

theorem uncountable_sequence (hB : Flypitch.BA_CCC B) (context : B) (domain : bSet B)
    (hsubset : context ≤ domain ⊆ᴮ blockDomain)
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ) :
    ∃ names : Erdos597.One → bSet B, context ≤ sequenceValue domain blockOrder names := by
  have hrows := uncountable_slice_cover hB context domain hsubset hlarge
  have hcover : context ≤ ⨆ names, sequenceValue domain blockOrder names := by
    have hparts : context ≤ ⨆ row : ℕ,
        context ⊓ (injectsIntoValue (V B) (slice domain row) bSet.omega)ᶜ := by
      rw [← inf_iSup_eq]
      exact le_inf le_rfl hrows
    apply hparts.trans
    apply iSup_le
    intro row
    obtain ⟨names, hnames⟩ := slice_sequence hB
      (context ⊓ (injectsIntoValue (V B) (slice domain row) bSet.omega)ᶜ) domain row inf_le_right
    exact le_iSup_of_le names hnames
  exact family_fullness (sequenceValue domain blockOrder)
    (fun part left right heq hleft => sequenceValue_congr part domain blockOrder left right heq hleft)
    context hcover

end Erdos597Object.BooleanOrderedSubsets
