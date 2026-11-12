import Erdos597Object.BooleanGraphMaps
import Erdos597Object.BooleanUncountableRamsey
import Erdos597Object.FinitePartitionReduction

set_option backward.isDefEq.respectTransparency false

/-! Relate the finite clique dichotomy to the original weak-copy predicate. -/

namespace Erdos597Object.BooleanCliqueCopies

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanGraphMaps BooleanUncountableRamsey
open BooleanLocalGraphs BooleanGraphNeighborhoods BooleanFiniteGraphs

variable {B : Type} [CompleteBooleanAlgebra B]

theorem graph_irreflexive (context : B) (ambient relation name : bSet B)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hmember : context ≤ name ∈ᴮ ambient) :
    context ≤ (edgeValue (V B) relation name name)ᶜ := by
  have hloop := hgraph.trans (inf_le_right.trans inf_le_left)
  exact lattice.bv_context_apply (hloop.trans (iInf_le _ name)) hmember

theorem cliqueMap_to_blueCopy (context : B) (ambient domain relation : bSet B) (n : ℕ)
    (hsubset : context ≤ domain ⊆ᴮ ambient)
    (hgraph : context ≤ graphValue (V B) ambient relation) :
    context ⊓ cliqueMapValue domain relation n ≤ blueCopyValue (V B) (bSet.ofNat n) ambient
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation := by
  classical
  unfold cliqueMapValue
  rw [inf_iSup_eq]
  apply iSup_le
  intro names
  let part : B := context ⊓ ((⨅ i, names i ∈ᴮ domain) ⊓
    (⨅ i, ⨅ j, ⨅ (_ : i ≠ j), edgeValue (V B) relation (names i) (names j)))
  change part ≤ _
  have hdomain (i : Fin n) : part ≤ names i ∈ᴮ domain :=
    (inf_le_right.trans inf_le_left).trans (iInf_le _ i)
  have hmembers (i : Fin n) : part ≤ names i ∈ᴮ ambient :=
    bSet.mem_of_mem_subset' (inf_le_left.trans hsubset) (hdomain i)
  have hedges (i j : Fin n) (hij : i ≠ j) :
      part ≤ edgeValue (V B) relation (names i) (names j) :=
    (inf_le_right.trans inf_le_right).trans
      ((iInf_le _ i).trans ((iInf_le _ j).trans (iInf_le _ hij)))
  have houtput : ∀ i j, i ≠ j → part ⊓ (names i =ᴮ names j) = ⊥ := by
    intro i j hij
    have hloop := graph_irreflexive part ambient relation (names i)
      (inf_le_left.trans hgraph) (hmembers i)
    have hedge : part ⊓ (names i =ᴮ names j) ≤
        edgeValue (V B) relation (names i) (names i) :=
      (le_inf (bSet.bv_symm inf_le_right) (inf_le_left.trans (hedges i j hij))).trans
        (edge_right_ext relation (names i) (names j) (names i))
    exact bot_unique ((le_inf hedge (inf_le_left.trans hloop)).trans_eq inf_compl_eq_bot)
  have hinput : ∀ i j : Fin n, i ≠ j → part ⊓ (naturalLabel i =ᴮ naturalLabel j) = ⊥ := by
    intro i j hij
    rw [naturalLabel_discrete i j hij, inf_bot_eq]
  have hpreserves : ∀ i j : Fin n,
      part ⊓ edgeValue (V B) (graphName naturalLabel (⊤ : SimpleGraph (Fin n)))
        (naturalLabel i) (naturalLabel j) ≤ edgeValue (V B) relation (names i) (names j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [natural_graph_edge]
      simp [graphCoefficient]
    · exact inf_le_left.trans (hedges i j hij)
  have hcopy : part ≤ blueCopyValue (V B) (labelDomain (naturalLabel (n := n))) ambient
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation := by
    apply le_iSup_of_le (mapName naturalLabel names)
    exact le_inf (map_function part naturalLabel names ambient hinput hmembers)
      (le_inf (map_injective part naturalLabel names houtput)
        (map_preserves part naturalLabel names _ relation hpreserves))
  exact (le_inf (le_top.trans (bSet.bv_symm (natural_domain n))) hcopy).trans
    (FinitePartitionReduction.blueCopy_vertices_ext ambient
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation _ _)

theorem independentValue_ext (relation : bSet B) :
    bSet.B_ext (fun domain => independentValue domain relation) := by
  apply bSet.B_ext_iInf
  intro x
  apply bSet.B_ext_imp (bSet.B_ext_mem_right x)
  apply bSet.B_ext_iInf
  intro y
  exact bSet.B_ext_imp (bSet.B_ext_mem_right y) (bSet.B_ext_const _)

theorem independentSubset_witness (context : B) (domain relation : bSet B)
    (h : context ≤ independentSubsetValue domain relation) :
    ∃ independent : bSet B, context ≤ independent ⊆ᴮ domain ∧
      context ≤ (injectsIntoValue (V B) independent bSet.omega)ᶜ ∧
      context ≤ independentValue independent relation := by
  have hinjects : bSet.B_ext (fun subset : bSet B => injectsIntoValue (V B) subset bSet.omega) := by
    simp_rw [BooleanFunctionBridge.injectsInto_eq_injects_into]
    exact bSet.B_ext_injects_into_left
  obtain ⟨independent, hi⟩ := bSet.exists_convert h
    (bSet.B_ext_inf (bSet.B_ext_subset_left domain)
      (bSet.B_ext_inf (bSet.B_ext_compl hinjects) (independentValue_ext relation)))
  exact ⟨independent, hi.trans inf_le_left, hi.trans (inf_le_right.trans inf_le_left),
    hi.trans (inf_le_right.trans inf_le_right)⟩

theorem uncountable_independent_of_no_blueClique (hB : Flypitch.BA_CCC B) (context : B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (domain ambient relation : bSet B) (n : ℕ)
    (hsubset : context ≤ domain ⊆ᴮ labelDomain label)
    (hambientSubset : context ≤ domain ⊆ᴮ ambient)
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hnoClique : context ≤ (blueCopyValue (V B) (bSet.ofNat n) ambient
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation)ᶜ) :
    ∃ independent : bSet B, context ≤ independent ⊆ᴮ domain ∧
      context ≤ (injectsIntoValue (V B) independent bSet.omega)ᶜ ∧
      context ≤ independentValue independent relation := by
  apply independentSubset_witness context domain relation
  have hcase := uncountable_independent_or_clique_in_ambient hB label hdiscrete ambient relation n context domain
    hsubset hambientSubset hlarge hgraph
  apply lattice.context_or_elim' hcase
  · intro part _ hindependent
    exact hindependent
  · intro part hcontext hclique
    have hcopy := (le_inf hcontext hclique).trans
      (cliqueMap_to_blueCopy context ambient domain relation n hambientSubset hgraph)
    exact ((le_inf hcopy (hcontext.trans hnoClique)).trans_eq inf_compl_eq_bot).trans bot_le

end Erdos597Object.BooleanCliqueCopies
