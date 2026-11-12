import Erdos597Object.PatternCollapse

set_option backward.isDefEq.respectTransparency false

/-! The sparse graph name obtained from compatible ground schedule prefixes. -/

namespace Erdos597Object.BooleanScheduledGraph

open Erdos597 Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open PatternCollapse BooleanSets BooleanFiniteGraphs BooleanInjections CanonicalDomains

noncomputable def coefficient (x y : Vertex) : Algebra := by
  classical
  exact ⨆ schedule : One → Pattern,
    if (ScheduledSparseGraph.rules schedule defaultRowCodes).graph.Adj x y then
      prefixValue (max x.2 y.2) schedule else ⊥

theorem coefficient_of_adj (bound : One) (schedule : One → Pattern) (x y : Vertex)
    (hx : x.2 ≤ bound) (hy : y.2 ≤ bound)
    (hadj : (ScheduledSparseGraph.rules schedule defaultRowCodes).graph.Adj x y) :
    prefixValue bound schedule ≤ coefficient x y := by
  classical
  apply (prefix_mono (max x.2 y.2) bound (max_le hx hy) schedule).trans
  apply le_iSup_of_le schedule
  simp only [hadj, ite_true, le_refl]

theorem coefficient_of_nonadj (bound : One) (schedule : One → Pattern) (x y : Vertex)
    (hx : x.2 ≤ bound) (hy : y.2 ≤ bound)
    (hnot : ¬ (ScheduledSparseGraph.rules schedule defaultRowCodes).graph.Adj x y) :
    prefixValue bound schedule ≤ (coefficient x y)ᶜ := by
  classical
  apply (le_compl_iff_disjoint_right).mpr
  apply disjoint_iff.mpr
  apply bot_unique
  rw [coefficient, inf_iSup_eq]
  apply iSup_le
  intro other
  by_cases hadj : (ScheduledSparseGraph.rules other defaultRowCodes).graph.Adj x y
  · rw [ite_eq_left hadj]
    by_contra hbad
    have hne : prefixValue bound schedule ⊓ prefixValue (max x.2 y.2) other ≠ ⊥ :=
      fun hzero => hbad (by rw [hzero])
    have hcommon : prefixValue (max x.2 y.2) schedule ⊓
        prefixValue (max x.2 y.2) other ≠ ⊥ := by
      intro hzero
      apply hne
      exact bot_unique ((inf_le_inf
        (prefix_mono (max x.2 y.2) bound (max_le hx hy) schedule) le_rfl).trans_eq hzero)
    have hagree := prefix_agreement (max x.2 y.2) schedule other hcommon
    exact hnot ((ScheduledSparseGraph.graph_prefix schedule other defaultRowCodes
      (max x.2 y.2) hagree x y (le_max_left _ _) (le_max_right _ _)).mpr hadj)
  · simp only [hadj, ite_false, inf_bot_eq, le_refl]

theorem coefficient_loopless (x : Vertex) : coefficient x x = ⊥ := by
  classical
  simp [coefficient]

theorem coefficient_symmetric (x y : Vertex) : coefficient x y = coefficient y x := by
  classical
  unfold coefficient
  apply iSup_congr
  intro schedule
  rw [max_comm, (ScheduledSparseGraph.rules schedule defaultRowCodes).graph.adj_comm]

noncomputable def vertexEquiv :
    (ScheduledIteration.Labels × ScheduledIteration.Labels) ≃ Vertex :=
  Equiv.prodCongr BooleanColumns.columnEquiv BooleanColumns.columnEquiv

noncomputable def graphName : bSet Algebra := relationName squareLabel
  (fun ij => coefficient (vertexEquiv ij.1) (vertexEquiv ij.2))

theorem graph_edge (i j : ScheduledIteration.Labels × ScheduledIteration.Labels) :
    edgeValue (V Algebra) graphName (squareLabel i) (squareLabel j) =
      coefficient (vertexEquiv i) (vertexEquiv j) :=
  relationName_edge squareLabel squareLabel_discrete _ i j

theorem graph_spec : (⊤ : Algebra) ≤ graphValue (V Algebra) squareDomain graphName := by
  apply le_inf (CanonicalRelations.relationName_between squareLabel _)
  apply le_inf
  · have hself : bSet.B_ext (fun x => edgeValue (V Algebra) graphName x x) := by
      intro x y
      have hpair : (x =ᴮ y) ⊓ (bSet.pair x x ∈ᴮ graphName) ≤ bSet.pair x x =ᴮ bSet.pair y y :=
        bSet.pair_congr inf_le_left inf_le_left
      exact bSet.subst_congr_mem_left' hpair inf_le_right
    change (⊤ : Algebra) ≤ ⨅ x : bSet Algebra, lattice.imp
      (x ∈ᴮ weightedSet squareLabel (fun _ => ⊤)) (edgeValue (V Algebra) graphName x x)ᶜ
    rw [weighted_bounded_forall squareLabel (fun _ => ⊤) _ (bSet.B_ext_compl hself)]
    apply le_iInf
    intro i
    rw [graph_edge, coefficient_loopless]
    simp [lattice.imp]
  · let symmetry : bSet Algebra → bSet Algebra → Algebra := fun x y =>
      lattice.imp (edgeValue (V Algebra) graphName x y) (edgeValue (V Algebra) graphName y x) ⊓
        lattice.imp (edgeValue (V Algebra) graphName y x) (edgeValue (V Algebra) graphName x y)
    have hleft (y : bSet Algebra) : bSet.B_ext (fun x => symmetry x y) :=
      bSet.B_ext_inf
        (bSet.B_ext_imp (edge_left_ext _ y) (edge_right_ext _ y))
        (bSet.B_ext_imp (edge_right_ext _ y) (edge_left_ext _ y))
    have hright (x : bSet Algebra) : bSet.B_ext (symmetry x) :=
      bSet.B_ext_inf
        (bSet.B_ext_imp (edge_right_ext _ x) (edge_left_ext _ x))
        (bSet.B_ext_imp (edge_left_ext _ x) (edge_right_ext _ x))
    change (⊤ : Algebra) ≤ ⨅ x : bSet Algebra, lattice.imp
      (x ∈ᴮ weightedSet squareLabel (fun _ => ⊤))
      (⨅ y : bSet Algebra, lattice.imp (y ∈ᴮ weightedSet squareLabel (fun _ => ⊤)) (symmetry x y))
    rw [BooleanPosetModel.weighted_forall_two squareLabel (fun _ => ⊤) symmetry hleft hright]
    apply le_iInf
    intro i
    simp only [lattice.imp, compl_top, bot_sup_eq]
    apply le_iInf
    intro j
    unfold symmetry
    rw [graph_edge, graph_edge, coefficient_symmetric (vertexEquiv i) (vertexEquiv j)]
    simp [lattice.imp]

end Erdos597Object.BooleanScheduledGraph
