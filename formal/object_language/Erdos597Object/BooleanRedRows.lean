import Erdos597Object.BooleanOrderMaps

set_option backward.isDefEq.respectTransparency false

/-! The literal ordered red-copy predicate from an independent row family. -/

namespace Erdos597Object.BooleanRedRows

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanGraphMaps BooleanOrderMaps BooleanOrderedSubsets
open BooleanRowValues BooleanRowOrder BooleanRectangles BooleanLocalGraphs BooleanColumns
open BooleanBlockOrder CanonicalDomains

variable {B : Type} [CompleteBooleanAlgebra B]

theorem ordered_names_distinct (context : B) (x y : bSet B)
    (hx : context ≤ x ∈ᴮ blockDomain)
    (hxy : context ≤ edgeValue (V B) blockOrder x y) :
    context ⊓ (x =ᴮ y) = ⊥ := by
  let part := context ⊓ (x =ᴮ y)
  have hloop : part ≤ edgeValue (V B) blockOrder x x :=
    (le_inf (bSet.bv_symm inf_le_right) (inf_le_left.trans hxy)).trans
      (edge_right_ext blockOrder x y x)
  exact bot_unique ((le_inf hloop (inf_le_left.trans (blockOrder_no_loop context x hx))).trans_eq
    inf_compl_eq_bot)

theorem independent_distinct_nonedge (context : B) (domain relation x y : bSet B)
    (hindependent : context ≤ independentValue domain relation)
    (hx : context ≤ x ∈ᴮ domain) (hy : context ≤ y ∈ᴮ domain)
    (hneq : context ⊓ (x =ᴮ y) = ⊥) :
    context ≤ (edgeValue (V B) relation x y)ᶜ := by
  have hfirst := lattice.bv_context_apply (hindependent.trans (iInf_le _ x)) hx
  have hsecond := lattice.bv_context_apply (hfirst.trans (iInf_le _ y)) hy
  apply (le_inf le_rfl hsecond).trans
  apply lattice.bv_or_elim_right
  · exact hneq.le.trans bot_le
  · exact inf_le_right

theorem rows_red_copy (hB : Flypitch.BA_CCC B) (context : B)
    (rows : ℕ → bSet B) (relation : bSet B)
    (hrows : context ≤ rowFamilyValue blockDomain relation blockOrder rows)
    (hindependent : ∀ row, context ≤ independentValue (rows row) relation)
    (hempty : ∀ r s, r ≠ s → context ≤ emptyRectangle relation (rows r) (rows s)) :
    context ≤ redCopyValue (V B) blockDomain blockDomain blockOrder blockOrder relation := by
  classical
  obtain ⟨hlarge, hsubset, _, hordered⟩ :=
    (rowFamilyValue_spec context blockDomain relation blockOrder rows).mp hrows
  have hexists (row : ℕ) : ∃ names : Erdos597.One → bSet B,
      context ≤ sequenceValue (rows row) blockOrder names :=
    uncountable_sequence hB context (rows row) (hsubset row) (hlarge row)
  let names := fun row => Classical.choose (hexists row)
  have hnames (row : ℕ) := sequenceValue_spec context (rows row) blockOrder (names row)
    (Classical.choose_spec (hexists row))
  let output := fun v : ℕ × ScheduledIteration.Labels => names v.1 (column v.2)
  have hmember (v : ℕ × ScheduledIteration.Labels) : context ≤ output v ∈ᴮ rows v.1 :=
    (hnames v.1).1 (column v.2)
  have hambient (v : ℕ × ScheduledIteration.Labels) : context ≤ output v ∈ᴮ blockDomain :=
    bSet.mem_of_mem_subset' (hsubset v.1) (hmember v)
  have hforward (v w : ℕ × ScheduledIteration.Labels) (hvw : keyLess v w) :
      context ≤ edgeValue (V B) blockOrder (output v) (output w) := by
    rcases hvw with hrow | ⟨hrow, hcolumn⟩
    · exact (le_inf le_rfl (le_inf (hmember v) (hmember w))).trans
        (allBefore_elim context blockOrder (rows v.1) (rows w.1) (hordered v.1 w.1 hrow) _ _)
    · have h := (hnames v.1).2.1 (column v.2) (column w.2) hcolumn
      simpa only [output, ← hrow] using h
  have hnotForward (v w : ℕ × ScheduledIteration.Labels) (hvw : ¬ keyLess v w) :
      context ≤ (edgeValue (V B) blockOrder (output v) (output w))ᶜ := by
    rcases keyLess_trichotomy v w with h | rfl | h
    · exact False.elim (hvw h)
    · exact blockOrder_no_loop context (output v) (hambient v)
    · exact blockOrder_reverse_false context (output w) (output v) (hambient w) (hambient v)
        (hforward w v h)
  have hdiscrete (v w : ℕ × ScheduledIteration.Labels) (hvw : v ≠ w) :
      context ⊓ (output v =ᴮ output w) = ⊥ := by
    rcases keyLess_trichotomy v w with h | h | h
    · exact ordered_names_distinct context (output v) (output w) (hambient v) (hforward v w h)
    · exact False.elim (hvw h)
    · have hzero := ordered_names_distinct context (output w) (output v) (hambient w) (hforward w v h)
      exact bot_unique ((le_inf inf_le_left (bSet.bv_symm inf_le_right)).trans_eq hzero)
  have hred (v w : ℕ × ScheduledIteration.Labels) (hvw : v ≠ w) :
      context ≤ (edgeValue (V B) relation (output v) (output w))ᶜ := by
    by_cases hrow : v.1 = w.1
    · apply independent_distinct_nonedge context (rows v.1) relation (output v) (output w)
        (hindependent v.1) (hmember v)
      · simpa only [← hrow] using hmember w
      · exact hdiscrete v w hvw
    · exact emptyRectangle_no_edge context relation (rows v.1) (rows w.1) (output v) (output w)
        (hempty v.1 w.1 hrow) (hmember v) (hmember w)
  apply le_iSup_of_le (mapName blockLabel output)
  refine le_inf (map_function context blockLabel output blockDomain
    (fun v w hvw => by rw [blockLabel_discrete v w hvw, inf_bot_eq]) hambient) ?_
  apply le_inf (map_injective context blockLabel output hdiscrete)
  apply le_inf
  · apply map_respects context blockLabel output blockOrder blockOrder
    · intro v w
      rw [blockOrder_edge]
      by_cases hvw : keyLess v w
      · simpa only [ite_eq_left hvw, inf_top_eq] using hforward v w hvw
      · simp only [ite_eq_right hvw, inf_bot_eq, bot_le]
    · intro v w
      rw [blockOrder_edge]
      by_cases hvw : keyLess v w
      · simp only [ite_eq_left hvw, le_top]
      · rw [ite_eq_right hvw]
        exact (le_inf (inf_le_left.trans (hnotForward v w hvw)) inf_le_right).trans_eq
          compl_inf_eq_bot
  · exact map_avoids context blockLabel output relation hred

end Erdos597Object.BooleanRedRows
