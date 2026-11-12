import Erdos597Object.BooleanScheduledGraph

set_option backward.isDefEq.respectTransparency false

/-! Finite weak copies reflect to one ground schedule completion. -/

namespace Erdos597Object.BooleanSparseFiniteCopies

open Erdos597 Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanFiniteGraphs BooleanInjections PatternCollapse CanonicalDomains
open BooleanScheduledGraph

theorem no_blue_copy {n : Nat} (H : SimpleGraph (Fin n))
    (hno : ∀ schedule : One → Pattern,
      ¬ HasWeakCopy H (ScheduledSparseGraph.rules schedule defaultRowCodes).graph) :
    blueCopyValue (V Algebra) (labelDomain (naturalLabel (n := n))) squareDomain
      (BooleanFiniteGraphs.graphName naturalLabel H) BooleanScheduledGraph.graphName = ⊥ := by
  classical
  apply bot_unique
  unfold blueCopyValue
  apply iSup_le
  intro mapping
  let context : Algebra :=
    functionFromValue (V Algebra) (labelDomain (naturalLabel (n := n))) squareDomain mapping ⊓
      (injectiveValue (V Algebra) mapping ⊓ preservesRelationValue (V Algebra)
        (BooleanFiniteGraphs.graphName naturalLabel H) BooleanScheduledGraph.graphName mapping)
  change context ≤ ⊥
  by_contra hnot
  have hne : context ≠ ⊥ := fun hzero => hnot hzero.le
  have hfunction : context ≤ functionFromValue (V Algebra)
      (labelDomain (naturalLabel (n := n))) squareDomain mapping := inf_le_left
  have hcover : ∀ i : Fin n, context ≤ ⨆ j,
      edgeValue (V Algebra) mapping (naturalLabel i) (squareLabel j) := by
    intro i
    exact (le_inf le_rfl (le_top.trans (weight_le_member naturalLabel (fun _ => ⊤) i))).trans
      (totalAt_labels _ mapping squareLabel hfunction (naturalLabel i))
  obtain ⟨lower, hlower, hbase, images, himages⟩ :=
    BooleanCountableDecision.decide_countable_family closed_basis context
      (fun i j => edgeValue (V Algebra) mapping (naturalLabel i) (squareLabel j)) hne hcover
  obtain ⟨bound, hbound⟩ := countable_family_bounded (fun i : Fin n => (vertexEquiv (images i)).2)
  obtain ⟨schedule, hpart⟩ := BooleanWeightedSupports.exists_nonzero_intersection lower
    (prefixValue bound) hlower (by rw [prefix_cover]; exact le_top)
  let part := lower ⊓ prefixValue bound schedule
  have hpartBase : part ≤ context := inf_le_left.trans hbase
  have hpartImages (i : Fin n) : part ≤
      edgeValue (V Algebra) mapping (naturalLabel i) (squareLabel (images i)) :=
    inf_le_left.trans (himages i)
  have hinjective : Function.Injective images := by
    intro i j heq
    by_contra hij
    have houtputs : part ≤ naturalLabel i =ᴮ naturalLabel j := by
      apply (le_inf hpartBase (le_inf (hpartImages i) ?_)).trans
        (injective_outputs mapping (inf_le_right.trans inf_le_left) _ _ _)
      simpa only [heq] using hpartImages j
    exact hpart (bot_unique (houtputs.trans_eq (naturalLabel_discrete i j hij)))
  have hedges : ∀ i j, H.Adj i j →
      (ScheduledSparseGraph.rules schedule defaultRowCodes).graph.Adj
        (vertexEquiv (images i)) (vertexEquiv (images j)) := by
    intro i j hij
    have hsource : part ≤ edgeValue (V Algebra) (BooleanFiniteGraphs.graphName naturalLabel H)
        (naturalLabel i) (naturalLabel j) := by
      rw [graphName_edge naturalLabel naturalLabel_discrete]
      simp [graphCoefficient, hij]
    have hpreserves := hpartBase.trans (inf_le_right.trans inf_le_right)
    have himp := hpreserves.trans ((iInf_le _ (naturalLabel i)).trans
      ((iInf_le _ (naturalLabel j)).trans ((iInf_le _ (squareLabel (images i))).trans
        (iInf_le _ (squareLabel (images j))))))
    have htarget : part ≤ edgeValue (V Algebra) BooleanScheduledGraph.graphName
        (squareLabel (images i)) (squareLabel (images j)) :=
      lattice.bv_context_apply (lattice.bv_context_apply himp
        (le_inf (hpartImages i) (hpartImages j))) hsource
    rw [BooleanScheduledGraph.graph_edge] at htarget
    by_contra hnotAdj
    have hcomplement : part ≤ (coefficient (vertexEquiv (images i)) (vertexEquiv (images j)))ᶜ :=
      inf_le_right.trans (coefficient_of_nonadj bound schedule _ _
        (hbound i).le (hbound j).le hnotAdj)
    exact hpart (bot_unique ((le_inf htarget hcomplement).trans_eq inf_compl_eq_bot))
  exact hno schedule ⟨fun i => vertexEquiv (images i), vertexEquiv.injective.comp hinjective, hedges⟩

theorem exists_finite_target : ∃ (n : Nat) (H : SimpleGraph (Fin n)), H.CliqueFree 4 ∧
    blueCopyValue (V Algebra) (labelDomain (naturalLabel (n := n))) squareDomain
      (BooleanFiniteGraphs.graphName naturalLabel H) BooleanScheduledGraph.graphName = ⊥ := by
  classical
  obtain ⟨W, hW, H, hclique, horder⟩ := FiniteTarget.exists_finite_ordering_target
  have : Finite W := hW
  let : Fintype W := Fintype.ofFinite W
  let e := Fintype.equivFin W
  let : LinearOrder W := LinearOrder.lift' e e.injective
  let target := H.comap e.symm
  have htarget : target.CliqueFree 4 :=
    hclique.comap ⟨(SimpleGraph.Iso.comap e.symm H).toEmbedding.toCopy⟩
  refine ⟨Fintype.card W, target, htarget, no_blue_copy target ?_⟩
  intro schedule hcopy
  apply (ScheduledSparseGraph.rules schedule defaultRowCodes).no_weakCopy_of_orderingProperty H horder
  obtain ⟨f, hf, hedge⟩ := hcopy
  refine ⟨f ∘ e, hf.comp e.injective, ?_⟩
  intro x y hxy
  apply hedge (e x) (e y)
  simpa only [target, SimpleGraph.comap_adj, Equiv.symm_apply_apply] using hxy

end Erdos597Object.BooleanSparseFiniteCopies
