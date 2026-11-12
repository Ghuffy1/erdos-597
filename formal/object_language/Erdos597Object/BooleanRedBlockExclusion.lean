import Erdos597Object.BooleanRedRowSelection

set_option backward.isDefEq.respectTransparency false

/-! Exclusion of the exact red ordinal block in the pattern-collapse graph. -/

namespace Erdos597Object.BooleanRedBlockExclusion

open Erdos597 Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets CanonicalDomains PatternCollapse BooleanScheduledGraph
open BooleanRedImages BooleanRedCopyFamilies BooleanRedRowSelection BooleanUnboundedRows

theorem graph_vertex_edge (u v : Vertex) :
    edgeValue (V Algebra) BooleanScheduledGraph.graphName (vertexLabel u) (vertexLabel v) =
      coefficient u v := by
  rw [vertexLabel, vertexLabel, BooleanScheduledGraph.graph_edge]
  simp only [Equiv.apply_symm_apply]

theorem family_impossible (context : Algebra) (hne : context ≠ ⊥)
    (F : Family context BooleanScheduledGraph.graphName) : False := by
  classical
  obtain ⟨lower, hlower, hcontext, row, pattern, hrows, hunbounded, hpoints⟩ :=
    extract_pattern F closed_basis hne
  obtain ⟨index, hindexPositive⟩ := BooleanWeightedSupports.exists_nonzero_intersection lower
    (fun index => entry index pattern) hlower (by rw [entry_onto]; exact le_top)
  let indexed := lower ⊓ entry index pattern
  obtain ⟨bound, hbound⟩ := pattern.bounded
  have htail : indexed ≤ ⨆ column : Set.Ioi (max index bound),
      imageWeight (F.values 0) (row, column.val) := by
    apply ((inf_le_left.trans hunbounded).trans (unbounded_le_tail _ (max index bound))).trans
    exact iSup_le fun column => iSup_le fun h => le_iSup_of_le ⟨column, h⟩ le_rfl
  obtain ⟨column, hcolumnPositive⟩ := BooleanWeightedSupports.exists_nonzero_intersection indexed
    (fun column : Set.Ioi (max index bound) => imageWeight (F.values 0) (row, column.val))
    hindexPositive htail
  let selected := indexed ⊓ imageWeight (F.values 0) (row, column.val)
  obtain ⟨schedule, hfinalPositive⟩ := BooleanWeightedSupports.exists_nonzero_intersection selected
    (prefixValue column.val) hcolumnPositive (by rw [prefix_cover]; exact le_top)
  let final := selected ⊓ prefixValue column.val schedule
  have hfinalPrefix : final ≤ prefixValue column.val schedule := inf_le_right
  have hfinalSelected : final ≤ selected := inf_le_left
  have hfinalIndexed : final ≤ indexed := hfinalSelected.trans inf_le_left
  have hfinalLower : final ≤ lower := hfinalIndexed.trans inf_le_left
  have hindexBound : index < column.val := (le_max_left _ _).trans_lt column.property
  have hpattern : schedule index = pattern := by
    by_contra hnot
    have hs : final ≤ entry index (schedule index) := hfinalPrefix.trans
      (prefix_le_entry column.val schedule index hindexBound)
    have hp : final ≤ entry index pattern := hfinalIndexed.trans inf_le_right
    exact hfinalPositive (bot_unique ((le_inf hs hp).trans_eq (entry_disjoint index _ _ hnot)))
  have hrow : ∀ n, row < (schedule index).row n := by simpa only [hpattern] using hrows
  have hcolumn : ∀ n m, (schedule index).column n m < column.val := by
    intro n m
    rw [hpattern]
    exact (hbound n m).trans ((le_max_right _ _).trans_lt column.property)
  obtain ⟨n, m, hedge⟩ := ScheduledSparseGraph.hits_index schedule defaultRowCodes
    index row column.val hindexBound hrow hcolumn
  rw [hpattern] at hedge
  have hblue : final ≤ edgeValue (V Algebra) BooleanScheduledGraph.graphName
      (vertexLabel (row, column.val)) (vertexLabel (pattern.point n m)) := by
    rw [graph_vertex_edge]
    exact hfinalPrefix.trans (coefficient_of_adj column.val schedule _ _ le_rfl
      ((hbound n m).trans ((le_max_right _ _).trans_lt column.property)).le hedge)
  have hred : final ≤ (edgeValue (V Algebra) BooleanScheduledGraph.graphName
      (vertexLabel (row, column.val)) (vertexLabel (pattern.point n m)))ᶜ := by
    apply (le_inf (le_inf (hfinalLower.trans hcontext)
      (hfinalSelected.trans inf_le_right)) (hfinalLower.trans (hpoints n m))).trans
    exact F.images_red 0 (n + 1) (Nat.ne_of_lt (Nat.zero_lt_succ n)) _ _
  exact hfinalPositive (bot_unique ((le_inf hblue hred).trans_eq inf_compl_eq_bot))

theorem red_copy_eq_bot :
    redCopyValue (V Algebra) blockDomain squareDomain blockOrder squareOrder
      BooleanScheduledGraph.graphName = ⊥ := by
  apply bot_unique
  unfold redCopyValue
  apply iSup_le
  intro mapping
  let context := functionFromValue (V Algebra) blockDomain squareDomain mapping ⊓
    (injectiveValue (V Algebra) mapping ⊓
      (respectsOrderValue (V Algebra) blockOrder squareOrder mapping ⊓
        avoidsEdgesValue (V Algebra) BooleanScheduledGraph.graphName mapping))
  change context ≤ ⊥
  by_contra hnot
  have hne : context ≠ ⊥ := fun hzero => hnot hzero.le
  obtain ⟨F⟩ := family_of_mapping context BooleanScheduledGraph.graphName mapping
    inf_le_left (inf_le_right.trans inf_le_left)
    (inf_le_right.trans (inf_le_right.trans inf_le_left))
    (inf_le_right.trans (inf_le_right.trans inf_le_right))
  exact family_impossible context hne F

end Erdos597Object.BooleanRedBlockExclusion
