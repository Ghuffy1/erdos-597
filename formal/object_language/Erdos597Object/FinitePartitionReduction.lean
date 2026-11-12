import Erdos597Object.BooleanFiniteGraphs
import Erdos597Object.PartitionSemantics

set_option backward.isDefEq.respectTransparency false

/-! Reduce the full finite-graph quantifier to the canonical finite graph names. -/

namespace Erdos597Object.FinitePartitionReduction

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanFiniteGraphs

variable {B : Type} [CompleteBooleanAlgebra B]

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

theorem blueCopy_vertices_ext (host edges blue : bSet B) :
    bSet.B_ext (fun vertices => blueCopyValue (V B) vertices host edges blue) := by
  intro x y
  have h := boolean_realize_bounded_formula_congr_head (S := V B) x y (host :: edges :: blue :: [])
    (blueCopy (var0 : Term 4) var1 var2 var3)
  simpa only [realize_blueCopy, boolean_realize_bounded_term_var0,
    boolean_realize_bounded_term_var1, boolean_realize_bounded_term_var2,
    boolean_realize_bounded_term_var3, V_eq] using! h

theorem blueCopy_edges_ext (vertices host blue : bSet B) :
    bSet.B_ext (fun edges => blueCopyValue (V B) vertices host edges blue) := by
  intro x y
  have h := boolean_realize_bounded_formula_congr_head (S := V B) x y (vertices :: host :: blue :: [])
    (blueCopy (var1 : Term 4) var2 var0 var3)
  simpa only [realize_blueCopy, boolean_realize_bounded_term_var0,
    boolean_realize_bounded_term_var1, boolean_realize_bounded_term_var2,
    boolean_realize_bounded_term_var3, V_eq] using! h

noncomputable def partitionForGraphValue (host redDomain hostOrder redOrder vertices edges : bSet B) : B :=
  ⨅ blue : bSet B, (graphValue (V B) host blue)ᶜ ⊔
    (redCopyValue (V B) redDomain host redOrder hostOrder blue ⊔
      blueCopyValue (V B) vertices host edges blue)

theorem partition_vertices_ext (host redDomain hostOrder redOrder edges : bSet B) :
    bSet.B_ext (fun vertices => partitionForGraphValue host redDomain hostOrder redOrder vertices edges) :=
  bSet.B_ext_iInf fun blue => bSet.B_ext_sup (bSet.B_ext_const _)
    (bSet.B_ext_sup (bSet.B_ext_const _) (blueCopy_vertices_ext host edges blue))

theorem partition_edges_ext (host redDomain hostOrder redOrder vertices : bSet B) :
    bSet.B_ext (partitionForGraphValue host redDomain hostOrder redOrder vertices) :=
  bSet.B_ext_iInf fun blue => bSet.B_ext_sup (bSet.B_ext_const _)
    (bSet.B_ext_sup (bSet.B_ext_const _) (blueCopy_edges_ext vertices host blue))

theorem omega_forall (predicate : bSet B → B) (hext : bSet.B_ext predicate) :
    (⨅ x : bSet B, lattice.imp (x ∈ᴮ bSet.omega) (predicate x)) =
      ⨅ n : ℕ, predicate (bSet.ofNat n) := by
  rw [← bSet.bounded_forall bSet.omega predicate hext]
  change (⨅ n : ULift ℕ, lattice.imp ⊤ (predicate (bSet.ofNat n.down))) = _
  simp only [lattice.imp, compl_top, bot_sup_eq]
  apply le_antisymm
  · apply le_iInf
    intro n
    exact iInf_le (fun k : ULift ℕ => predicate (bSet.ofNat k.down)) ⟨n⟩
  · apply le_iInf
    intro n
    exact iInf_le (fun k : ℕ => predicate (bSet.ofNat k)) n.down

theorem finitePartition_of_ground_targets (host redDomain hostOrder redOrder : bSet B)
    (hchecked : ∀ (n : ℕ) (graph : SimpleGraph (Fin n)),
      ⊤ ≤ partitionForGraphValue host redDomain hostOrder redOrder (bSet.ofNat n)
        (graphName naturalLabel graph)) :
    ⊤ ≤ finitePartitionValue (V B) host redDomain hostOrder redOrder := by
  let property : bSet B → B := fun vertices =>
    ⨅ edges : bSet B, lattice.imp (graphValue (V B) vertices edges)
      (partitionForGraphValue host redDomain hostOrder redOrder vertices edges)
  have hext : bSet.B_ext property := bSet.B_ext_iInf fun edges =>
    bSet.B_ext_imp (graph_vertices_ext edges) (partition_vertices_ext host redDomain hostOrder redOrder edges)
  have hforall : ⊤ ≤ ⨅ vertices : bSet B, lattice.imp (vertices ∈ᴮ bSet.omega) (property vertices) := by
    rw [omega_forall property hext]
    apply le_iInf
    intro n
    apply le_iInf
    intro edges
    apply lattice.bv_imp_intro
    exact natural_graph_predicate _ n edges inf_le_right
      (partitionForGraphValue host redDomain hostOrder redOrder (bSet.ofNat n))
      (partition_edges_ext host redDomain hostOrder redOrder (bSet.ofNat n))
      (fun graph => le_top.trans (hchecked n graph))
  unfold finitePartitionValue
  apply le_iInf
  intro vertices
  apply lattice.bv_imp_intro
  have hv := lattice.bv_context_apply
    (inf_le_left.trans (hforall.trans (iInf_le _ vertices))) inf_le_right
  apply le_iInf
  intro edges
  apply lattice.bv_imp_intro
  exact lattice.bv_context_apply ((inf_le_left.trans hv).trans (iInf_le _ edges))
    (inf_le_right.trans inf_le_left)

end Erdos597Object.FinitePartitionReduction
