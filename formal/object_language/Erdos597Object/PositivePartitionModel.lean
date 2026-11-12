import Erdos597Object.CanonicalBlockInclusion
import Erdos597Object.ModelConsequences
import Erdos597Object.FiniteCliqueReduction

set_option backward.isDefEq.respectTransparency false

/-! The full positive finite-target sentence in the constructed Martin model. -/

namespace Erdos597Object.PositivePartitionModel

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanFiniteGraphs BooleanIndependentTail BooleanRedRows
open BooleanInducedGraphs BooleanCopyExtensions CanonicalBlockInclusion CanonicalDomains
open FinitePartitionReduction

theorem block_red_of_no_blue (context : ScheduledIteration.finalAlgebra) (n : ℕ)
    (blue : bSet ScheduledIteration.finalAlgebra)
    (hgraph : context ≤ graphValue (V ScheduledIteration.finalAlgebra) blockDomain blue)
    (hno : context ≤ (blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n) blockDomain
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) blue)ᶜ) :
    context ≤ redCopyValue (V ScheduledIteration.finalAlgebra) blockDomain blockDomain blockOrder blockOrder blue := by
  obtain ⟨rows, hrows, hindependent, hempty⟩ := canonical_independent_rows context n blue hgraph hno
  exact rows_red_copy ScheduledIteration.finalAlgebra.ccc context rows blue hrows hindependent hempty

theorem square_red_of_no_blue (context : ScheduledIteration.finalAlgebra) (n : ℕ)
    (blue : bSet ScheduledIteration.finalAlgebra)
    (hgraph : context ≤ graphValue (V ScheduledIteration.finalAlgebra) squareDomain blue)
    (hno : context ≤ (blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n) squareDomain
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) blue)ᶜ) :
    context ≤ redCopyValue (V ScheduledIteration.finalAlgebra) blockDomain squareDomain blockOrder squareOrder blue := by
  have hsub : context ≤ blockDomain ⊆ᴮ squareDomain := le_top.trans block_subset_square
  have hrestricted : context ≤ graphValue (V ScheduledIteration.finalAlgebra) blockDomain
      (restrictGraph blockDomain blue) := restricted_graph context blockDomain squareDomain blue hsub hgraph
  have hrestrictedNo : context ≤ (blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n) blockDomain
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) (restrictGraph blockDomain blue))ᶜ := by
    apply (le_compl_iff_disjoint_right).mpr
    apply disjoint_iff.mpr
    exact bot_unique ((le_inf
      (blueCopy_enlarge context (bSet.ofNat n) blockDomain squareDomain
        (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) blue hsub)
      (inf_le_left.trans hno)).trans_eq inf_compl_eq_bot)
  have hred := block_red_of_no_blue context n (restrictGraph blockDomain blue) hrestricted hrestrictedNo
  exact (le_inf le_rfl hred).trans (redCopy_enlarge context blockDomain blockDomain squareDomain
    blockOrder blockOrder squareOrder blue hsub (orders_agree context))

theorem finite_clique_partition (n : ℕ) :
    (⊤ : ScheduledIteration.finalAlgebra) ≤
      partitionForGraphValue squareDomain blockDomain squareOrder blockOrder (bSet.ofNat n)
        (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) := by
  apply le_iInf
  intro blue
  apply lattice.bv_imp_intro
  let context := (⊤ : ScheduledIteration.finalAlgebra) ⊓
    graphValue (V ScheduledIteration.finalAlgebra) squareDomain blue
  let clique := blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n) squareDomain
    (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) blue
  have hred : context ⊓ cliqueᶜ ≤ redCopyValue (V ScheduledIteration.finalAlgebra)
      blockDomain squareDomain blockOrder squareOrder blue :=
    square_red_of_no_blue (context ⊓ cliqueᶜ) n blue (inf_le_left.trans inf_le_right) inf_le_right
  exact (sup_inf_inf_compl (x := context) (y := clique)).symm.le.trans
    (sup_le (inf_le_right.trans le_sup_right) (hred.trans le_sup_left))

theorem final_finite_assertion :
    (⊤ : ScheduledIteration.finalAlgebra) ≤
      boolean_realize_sentence (V ScheduledIteration.finalAlgebra) finiteAssertion :=
  FiniteCliqueReduction.finiteAssertion_of_cliques ScheduledIteration.finalAlgebra.ccc finite_clique_partition

theorem final_models_finite_assertion :
    forces_theory (⊤ : ScheduledIteration.finalAlgebra) (V ScheduledIteration.finalAlgebra)
      (insert finiteAssertion Flypitch.ZFC.ZFC) := by
  apply le_iInf
  intro formula
  apply le_iInf
  intro hformula
  change formula = finiteAssertion ∨ formula ∈ Flypitch.ZFC.ZFC at hformula
  rcases hformula with rfl | hformula
  · exact final_finite_assertion
  · exact ((bSet_models_ZFC (β := ScheduledIteration.finalAlgebra)).trans
      (iInf_le _ formula)).trans (iInf_le _ hformula)

theorem positive_extension_consistent :
    is_consistent (insert finiteAssertion Flypitch.ZFC.ZFC) :=
  ModelConsequences.consistent_of_model (V ScheduledIteration.finalAlgebra) final_models_finite_assertion

theorem neg_finiteAssertion_unprovable : ¬ (Flypitch.ZFC.ZFC ⊢' (∼finiteAssertion)) :=
  unprovable_of_model_neg (V ScheduledIteration.finalAlgebra) bSet_models_ZFC
    (hNonzero := bot_lt_top) (forced_not_not_of_forced final_finite_assertion)

end Erdos597Object.PositivePartitionModel
