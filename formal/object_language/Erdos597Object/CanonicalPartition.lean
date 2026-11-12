import Erdos597Object.CanonicalDomains
import Erdos597Object.FinitePartitionReduction
import Erdos597Object.AssertionSemantics

set_option backward.isDefEq.respectTransparency false

/-! The full partition sentence on canonical names in a CCC Boolean-valued model. -/

namespace Erdos597Object.CanonicalPartition

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanFiniteGraphs CanonicalRelations CanonicalDomains

variable {B : Type} [CompleteBooleanAlgebra B]

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

theorem partition_host_ext (redDomain hostOrder redOrder : bSet B) :
    bSet.B_ext (fun host => finitePartitionValue (V B) host redDomain hostOrder redOrder) := by
  intro x y
  have h := boolean_realize_bounded_formula_congr_head (S := V B) x y
    (redDomain :: hostOrder :: redOrder :: []) (finitePartition (var0 : Term 4) var1 var2 var3)
  simpa only [realize_finitePartition, boolean_realize_bounded_term_var0,
    boolean_realize_bounded_term_var1, boolean_realize_bounded_term_var2,
    boolean_realize_bounded_term_var3, V_eq] using! h

theorem partition_redDomain_ext (host hostOrder redOrder : bSet B) :
    bSet.B_ext (fun redDomain => finitePartitionValue (V B) host redDomain hostOrder redOrder) := by
  intro x y
  have h := boolean_realize_bounded_formula_congr_head (S := V B) x y
    (host :: hostOrder :: redOrder :: []) (finitePartition (var1 : Term 4) var0 var2 var3)
  simpa only [realize_finitePartition, boolean_realize_bounded_term_var0,
    boolean_realize_bounded_term_var1, boolean_realize_bounded_term_var2,
    boolean_realize_bounded_term_var3, V_eq] using! h

theorem partition_hostOrder_ext (host redDomain redOrder : bSet B) :
    bSet.B_ext (fun hostOrder => finitePartitionValue (V B) host redDomain hostOrder redOrder) := by
  intro x y
  have h := boolean_realize_bounded_formula_congr_head (S := V B) x y
    (host :: redDomain :: redOrder :: []) (finitePartition (var1 : Term 4) var2 var0 var3)
  simpa only [realize_finitePartition, boolean_realize_bounded_term_var0,
    boolean_realize_bounded_term_var1, boolean_realize_bounded_term_var2,
    boolean_realize_bounded_term_var3, V_eq] using! h

theorem partition_redOrder_ext (host redDomain hostOrder : bSet B) :
    bSet.B_ext (fun redOrder => finitePartitionValue (V B) host redDomain hostOrder redOrder) := by
  intro x y
  have h := boolean_realize_bounded_formula_congr_head (S := V B) x y
    (host :: redDomain :: hostOrder :: []) (finitePartition (var1 : Term 4) var2 var3 var0)
  simpa only [realize_finitePartition, boolean_realize_bounded_term_var0,
    boolean_realize_bounded_term_var1, boolean_realize_bounded_term_var2,
    boolean_realize_bounded_term_var3, V_eq] using! h

theorem assertion_le_canonical_of_omegaOne
    (hOne : (⊤ : B) ≤ omegaOneValue (V B) omegaOneName) :
    finiteAssertionValue (V B) ≤ finitePartitionValue (V B) squareDomain blockDomain squareOrder blockOrder := by
  have hp : (⊤ : B) ≤ omegaOneValue (V B) omegaOneName ⊓
      (cartesianProductValue (V B) omegaOneName omegaOneName squareDomain ⊓
        (cartesianProductValue (V B) bSet.omega omegaOneName blockDomain ⊓
          (lexOrderValue (V B) squareDomain squareOrder ⊓ lexOrderValue (V B) blockDomain blockOrder))) :=
    le_inf hOne
      (le_inf square_product_spec (le_inf block_product_spec (le_inf square_order_spec block_order_spec)))
  exact lattice.bv_context_apply
    ((iInf_le _ (omegaOneName : bSet B)).trans
      ((iInf_le _ (squareDomain : bSet B)).trans
        ((iInf_le _ (blockDomain : bSet B)).trans
          ((iInf_le _ (squareOrder : bSet B)).trans (iInf_le _ (blockOrder : bSet B))))))
    (le_top.trans hp)

theorem canonical_le_assertion_of_omegaOne
    (hUnique : ∀ kappa : bSet B, omegaOneValue (V B) kappa ≤ kappa =ᴮ omegaOneName) :
    finitePartitionValue (V B) squareDomain blockDomain squareOrder blockOrder ≤ finiteAssertionValue (V B) := by
  unfold finiteAssertionValue
  apply le_iInf
  intro kappa
  apply le_iInf
  intro host
  apply le_iInf
  intro redDomain
  apply le_iInf
  intro hostOrder
  apply le_iInf
  intro redOrder
  apply lattice.bv_imp_intro
  let context : B := finitePartitionValue (V B) squareDomain blockDomain squareOrder blockOrder ⊓
    (omegaOneValue (V B) kappa ⊓
      (cartesianProductValue (V B) kappa kappa host ⊓
        (cartesianProductValue (V B) bSet.omega kappa redDomain ⊓
          (lexOrderValue (V B) host hostOrder ⊓ lexOrderValue (V B) redDomain redOrder))))
  change context ≤ finitePartitionValue (V B) host redDomain hostOrder redOrder
  have hk : context ≤ kappa =ᴮ omegaOneName :=
    (inf_le_right.trans inf_le_left).trans (hUnique kappa)
  have hhDef : context ≤ host =ᴮ bSet.prod kappa kappa :=
    (inf_le_right.trans (inf_le_right.trans inf_le_left)).trans_eq (cartesianProduct_eq kappa kappa host)
  have hrDef : context ≤ redDomain =ᴮ bSet.prod bSet.omega kappa :=
    (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))).trans_eq
      (cartesianProduct_eq bSet.omega kappa redDomain)
  have hh : context ≤ host =ᴮ squareDomain := bSet.bv_trans hhDef
    (bSet.bv_trans (bSet.prod_congr hk hk) (bSet.bv_symm (le_top.trans squareDomain_eq_product)))
  have hr : context ≤ redDomain =ᴮ blockDomain := bSet.bv_trans hrDef
    (bSet.bv_trans (bSet.prod_congr bSet.bv_refl hk) (bSet.bv_symm (le_top.trans blockDomain_eq_product)))
  have hho : context ≤ lexOrderValue (V B) squareDomain hostOrder :=
    (le_inf hh (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans
      (inf_le_right.trans inf_le_left))))).trans (lexOrder_domain_ext hostOrder host squareDomain)
  have hro : context ≤ lexOrderValue (V B) blockDomain redOrder :=
    (le_inf hr (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans
      (inf_le_right.trans inf_le_right))))).trans (lexOrder_domain_ext redOrder redDomain blockDomain)
  have hhOrder : context ≤ hostOrder =ᴮ squareOrder := lexOrder_eq_name squareLabel hostOrder hho
  have hrOrder : context ≤ redOrder =ᴮ blockOrder := lexOrder_eq_name blockLabel redOrder hro
  have h1 : context ≤ finitePartitionValue (V B) host blockDomain squareOrder blockOrder :=
    (le_inf (bSet.bv_symm hh) inf_le_left).trans
      (partition_host_ext blockDomain squareOrder blockOrder squareDomain host)
  have h2 : context ≤ finitePartitionValue (V B) host redDomain squareOrder blockOrder :=
    (le_inf (bSet.bv_symm hr) h1).trans
      (partition_redDomain_ext host squareOrder blockOrder blockDomain redDomain)
  have h3 : context ≤ finitePartitionValue (V B) host redDomain hostOrder blockOrder :=
    (le_inf (bSet.bv_symm hhOrder) h2).trans
      (partition_hostOrder_ext host redDomain blockOrder squareOrder hostOrder)
  exact (le_inf (bSet.bv_symm hrOrder) h3).trans
    (partition_redOrder_ext host redDomain hostOrder blockOrder redOrder)

theorem finiteAssertionValue_eq_of_omegaOne
    (hOne : (⊤ : B) ≤ omegaOneValue (V B) omegaOneName)
    (hUnique : ∀ kappa : bSet B, omegaOneValue (V B) kappa ≤ kappa =ᴮ omegaOneName) :
    finiteAssertionValue (V B) = finitePartitionValue (V B) squareDomain blockDomain squareOrder blockOrder :=
  le_antisymm (assertion_le_canonical_of_omegaOne hOne) (canonical_le_assertion_of_omegaOne hUnique)

theorem finiteAssertionValue_eq (hB : Flypitch.BA_CCC B) :
    finiteAssertionValue (V B) = finitePartitionValue (V B) squareDomain blockDomain squareOrder blockOrder :=
  finiteAssertionValue_eq_of_omegaOne (BooleanOrdinalBridge.omegaOneValue_check hB)
    (fun kappa => BooleanOrdinalBridge.omegaOneValue_unique hB kappa le_rfl)

theorem finiteAssertion_of_ground_targets (hB : Flypitch.BA_CCC B)
    (hchecked : ∀ (n : ℕ) (graph : SimpleGraph (Fin n)),
      (⊤ : B) ≤ FinitePartitionReduction.partitionForGraphValue squareDomain blockDomain squareOrder blockOrder
        (bSet.ofNat n) (graphName naturalLabel graph)) :
    ⊤ ≤ boolean_realize_sentence (V B) finiteAssertion := by
  rw [realize_finiteAssertion, finiteAssertionValue_eq hB]
  exact FinitePartitionReduction.finitePartition_of_ground_targets _ _ _ _ hchecked

end Erdos597Object.CanonicalPartition
