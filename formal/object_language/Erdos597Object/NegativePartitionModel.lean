import Erdos597Object.BooleanFiniteCliqueFree
import Erdos597Object.BooleanSparseFiniteCopies
import Erdos597Object.PositivePartitionModel

set_option backward.isDefEq.respectTransparency false

/-! The negative model and first-order finite-target independence for Erdos 597. -/

namespace Erdos597Object.NegativePartitionModel

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanFiniteGraphs CanonicalDomains PatternCollapse

theorem canonical_partition_eq_bot :
    finitePartitionValue (V Algebra) squareDomain blockDomain squareOrder blockOrder = ⊥ := by
  obtain ⟨n, H, hH, hnoBlue⟩ := BooleanSparseFiniteCopies.exists_finite_target
  let vertices : bSet Algebra := labelDomain (naturalLabel (n := n))
  let edges : bSet Algebra := graphName naturalLabel H
  have hvertices : (⊤ : Algebra) ≤ vertices ∈ᴮ bSet.omega :=
    bSet.subst_congr_mem_left' (natural_domain n) bSet.of_nat_mem_omega
  have hgraph : (⊤ : Algebra) ≤ graphValue (V Algebra) vertices edges :=
    graphName_spec naturalLabel naturalLabel_discrete H
  have hclique : (⊤ : Algebra) ≤ cliqueFreeFourValue (V Algebra) vertices edges :=
    BooleanFiniteCliqueFree.graphName_cliqueFree naturalLabel naturalLabel_discrete H hH
  let value := finitePartitionValue (V Algebra) squareDomain blockDomain squareOrder blockOrder
  have hfirst : value ≤ ⨅ relation : bSet Algebra,
      lattice.imp (graphValue (V Algebra) vertices relation ⊓ cliqueFreeFourValue (V Algebra) vertices relation)
        (⨅ blue : bSet Algebra, lattice.imp (graphValue (V Algebra) squareDomain blue)
          (redCopyValue (V Algebra) blockDomain squareDomain blockOrder squareOrder blue ⊔
            blueCopyValue (V Algebra) vertices squareDomain relation blue)) :=
    lattice.bv_context_apply (iInf_le _ vertices) (le_top.trans hvertices)
  have hsecond : value ≤ ⨅ blue : bSet Algebra, lattice.imp (graphValue (V Algebra) squareDomain blue)
      (redCopyValue (V Algebra) blockDomain squareDomain blockOrder squareOrder blue ⊔
        blueCopyValue (V Algebra) vertices squareDomain edges blue) :=
    lattice.bv_context_apply (hfirst.trans (iInf_le _ edges)) (le_top.trans (le_inf hgraph hclique))
  have hfinal : value ≤ redCopyValue (V Algebra) blockDomain squareDomain blockOrder squareOrder
      BooleanScheduledGraph.graphName ⊔ blueCopyValue (V Algebra) vertices squareDomain edges
        BooleanScheduledGraph.graphName :=
    lattice.bv_context_apply (hsecond.trans (iInf_le _ BooleanScheduledGraph.graphName))
      (le_top.trans BooleanScheduledGraph.graph_spec)
  rw [BooleanRedBlockExclusion.red_copy_eq_bot, hnoBlue, sup_bot_eq] at hfinal
  exact bot_unique hfinal

theorem finite_assertion_eq_bot : boolean_realize_sentence (V Algebra) finiteAssertion = ⊥ := by
  rw [realize_finiteAssertion]
  exact bot_unique ((CanonicalPartition.assertion_le_canonical_of_omegaOne omegaOne_preserved).trans_eq
    canonical_partition_eq_bot)

theorem negative_sentence : forces (⊤ : Algebra) (V Algebra) (∼finiteAssertion) := by
  change (⊤ : Algebra) ≤ boolean_realize_bounded_formula (S := V Algebra) dvector.nil
    (bd_not finiteAssertion) dvector.nil
  rw [boolean_realize_bounded_formula_not]
  change (⊤ : Algebra) ≤ (boolean_realize_sentence (V Algebra) finiteAssertion)ᶜ
  rw [finite_assertion_eq_bot, compl_bot]

theorem models_negative :
    forces_theory (⊤ : Algebra) (V Algebra) (insert (∼finiteAssertion) Flypitch.ZFC.ZFC) := by
  apply le_iInf
  intro formula
  apply le_iInf
  intro hformula
  change formula = (∼finiteAssertion) ∨ formula ∈ Flypitch.ZFC.ZFC at hformula
  rcases hformula with rfl | hformula
  · exact negative_sentence
  · exact ((bSet_models_ZFC (β := Algebra)).trans (iInf_le _ formula)).trans (iInf_le _ hformula)

theorem negative_extension_consistent : is_consistent (insert (∼finiteAssertion) Flypitch.ZFC.ZFC) :=
  ModelConsequences.consistent_of_model (V Algebra) models_negative

theorem finiteAssertion_unprovable : ¬ (Flypitch.ZFC.ZFC ⊢' finiteAssertion) :=
  unprovable_of_model_neg (V Algebra) bSet_models_ZFC (hNonzero := bot_lt_top) negative_sentence

theorem full_finite_independence : finiteIndependence :=
  ⟨finiteAssertion_unprovable, PositivePartitionModel.neg_finiteAssertion_unprovable⟩

theorem relative_finite_independence : relativeFiniteIndependence :=
  fun _ => full_finite_independence

end Erdos597Object.NegativePartitionModel
