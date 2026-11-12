import Erdos597Object.CanonicalPartition

set_option backward.isDefEq.respectTransparency false

/-! Reduce the positive finite-target statement to finite complete graphs. -/

namespace Erdos597Object.FiniteCliqueReduction

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanFiniteGraphs FinitePartitionReduction CanonicalDomains

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem relationName_mono (label : I → bSet B) (left right : I × I → B)
    (hvalues : ∀ ij, left ij ≤ right ij) :
    ⊤ ≤ relationName label left ⊆ᴮ relationName label right := by
  apply bSet.subset_intro
  intro ij
  exact le_iSup_of_le ij (le_inf (inf_le_right.trans (hvalues ij)) bSet.bv_refl)

theorem graphName_mono (label : I → bSet B) (left right : SimpleGraph I) (hgraphs : left ≤ right) :
    ⊤ ≤ graphName label left ⊆ᴮ graphName label right := by
  classical
  apply relationName_mono
  intro ij
  by_cases h : left.Adj ij.1 ij.2
  · have hright : right.Adj ij.1 ij.2 := hgraphs h
    simp [graphCoefficient, h, hright]
  · simp [graphCoefficient, h]

theorem preservesRelation_mono_source (context : B) (small large target mapping : bSet B)
    (hsub : context ≤ small ⊆ᴮ large) :
    context ⊓ preservesRelationValue (V B) large target mapping ≤
      preservesRelationValue (V B) small target mapping := by
  unfold preservesRelationValue
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  apply le_iInf
  intro a
  apply le_iInf
  intro b
  apply lattice.bv_imp_intro
  apply lattice.bv_imp_intro
  have hc : ((context ⊓ preservesRelationValue (V B) large target mapping) ⊓
      (edgeValue (V B) mapping x a ⊓ edgeValue (V B) mapping y b)) ⊓
      edgeValue (V B) small x y ≤ context := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hp := (inf_le_left.trans (inf_le_left.trans inf_le_right) :
      ((context ⊓ preservesRelationValue (V B) large target mapping) ⊓
        (edgeValue (V B) mapping x a ⊓ edgeValue (V B) mapping y b)) ⊓
        edgeValue (V B) small x y ≤ preservesRelationValue (V B) large target mapping)
  have hlarge := bSet.mem_of_mem_subset' (hc.trans hsub) inf_le_right
  have hpoint := hp.trans ((iInf_le _ x).trans
    ((iInf_le _ y).trans ((iInf_le _ a).trans (iInf_le _ b))))
  exact lattice.bv_context_apply
    (lattice.bv_context_apply hpoint (inf_le_left.trans inf_le_right)) hlarge

theorem blueCopy_mono_source (context : B) (vertices host small large blue : bSet B)
    (hsub : context ≤ small ⊆ᴮ large) :
    context ⊓ blueCopyValue (V B) vertices host large blue ≤ blueCopyValue (V B) vertices host small blue := by
  unfold blueCopyValue
  apply lattice.bv_cases_right
  intro mapping
  apply le_iSup_of_le mapping
  apply le_inf (inf_le_right.trans inf_le_left)
  apply le_inf (inf_le_right.trans (inf_le_right.trans inf_le_left))
  exact (le_inf inf_le_left (inf_le_right.trans (inf_le_right.trans inf_le_right))).trans
    (preservesRelation_mono_source context small large blue mapping hsub)

theorem partition_mono_target (context : B) (host redDomain hostOrder redOrder vertices small large : bSet B)
    (hsub : context ≤ small ⊆ᴮ large)
    (hlarge : context ≤ partitionForGraphValue host redDomain hostOrder redOrder vertices large) :
    context ≤ partitionForGraphValue host redDomain hostOrder redOrder vertices small := by
  apply le_iInf
  intro blue
  apply lattice.bv_imp_intro
  have hpoint := lattice.bv_context_apply
    ((inf_le_left.trans hlarge).trans (iInf_le _ blue)) inf_le_right
  apply (le_inf le_rfl hpoint).trans
  apply lattice.bv_or_elim_right
  · exact inf_le_right.trans le_sup_left
  · exact ((le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans
      (blueCopy_mono_source context vertices host small large blue hsub)).trans le_sup_right

theorem finiteAssertion_of_cliques (hB : Flypitch.BA_CCC B)
    (hcliques : ∀ n : ℕ, (⊤ : B) ≤
      partitionForGraphValue squareDomain blockDomain squareOrder blockOrder (bSet.ofNat n)
        (graphName naturalLabel (⊤ : SimpleGraph (Fin n)))) :
    ⊤ ≤ Flypitch.fol.bfol.boolean_realize_sentence (V B) finiteAssertion := by
  apply CanonicalPartition.finiteAssertion_of_ground_targets hB
  intro n graph
  exact partition_mono_target ⊤ _ _ _ _ _ _ _
    (graphName_mono naturalLabel graph ⊤ le_top) (hcliques n)

end Erdos597Object.FiniteCliqueReduction
