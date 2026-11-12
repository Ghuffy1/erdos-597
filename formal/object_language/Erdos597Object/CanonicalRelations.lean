import Erdos597Object.BooleanFiniteGraphs
import Erdos597Object.BooleanPosetModel

set_option backward.isDefEq.respectTransparency false

/-! Product domains and the canonical lexicographic relation names. -/

namespace Erdos597Object.CanonicalRelations

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanFiniteGraphs BooleanFunctionBridge

variable {B I : Type} [CompleteBooleanAlgebra B]

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

theorem membership_biimp_eq (x y : bSet B) :
    (⨅ z : bSet B, lattice.biimp (z ∈ᴮ x) (z ∈ᴮ y)) = (x =ᴮ y) := by
  apply le_antisymm (bSet.mem_ext_of_biimp le_rfl)
  apply le_iInf
  intro z
  apply le_inf
  · apply lattice.bv_imp_intro
    exact bSet.subst_congr_mem_right' inf_le_left inf_le_right
  · apply lattice.bv_imp_intro
    exact bSet.subst_congr_mem_right' (bSet.bv_symm inf_le_left) inf_le_right

theorem cartesianProduct_eq (left right product : bSet B) :
    cartesianProductValue (V B) left right product = (product =ᴮ bSet.prod left right) := by
  rw [← membership_biimp_eq]
  unfold cartesianProductValue
  apply iInf_congr
  intro entry
  rw [product_membership]
  rfl

theorem relationName_between (label : I → bSet B) (values : I × I → B) :
    ⊤ ≤ relationBetweenValue (V B) (labelDomain label) (labelDomain label) (relationName label values) := by
  rw [relationBetween_eq_subset_prod]
  apply bSet.subset_intro
  intro ij
  apply bSet.prod_mem
  · exact le_top.trans (weight_le_member label (fun _ => ⊤) ij.1)
  · exact le_top.trans (weight_le_member label (fun _ => ⊤) ij.2)

theorem lexLess_left_ext (z : bSet B) : bSet.B_ext (fun x => lexLessValue (V B) x z) := by
  intro x y
  have h := boolean_realize_bounded_formula_congr_head (S := V B) x y (z :: [])
    (lexLess (var0 : Term 2) var1)
  simpa only [realize_lexLess, boolean_realize_bounded_term_var0,
    boolean_realize_bounded_term_var1, V_eq] using! h

theorem lexLess_right_ext (z : bSet B) : bSet.B_ext (lexLessValue (V B) z) := by
  intro x y
  have h := boolean_realize_bounded_formula_congr_head (S := V B) x y (z :: [])
    (lexLess (var1 : Term 2) var0)
  simpa only [realize_lexLess, boolean_realize_bounded_term_var0,
    boolean_realize_bounded_term_var1, V_eq] using! h

theorem lexOrder_domain_ext (order : bSet B) :
    bSet.B_ext (fun domain => lexOrderValue (V B) domain order) := by
  intro x y
  have h := boolean_realize_bounded_formula_congr_head (S := V B) x y (order :: [])
    (lexOrder (var0 : Term 2) var1)
  simpa only [realize_lexOrder, boolean_realize_bounded_term_var0,
    boolean_realize_bounded_term_var1, V_eq] using! h

noncomputable def lexOrderName (label : I → bSet B) : bSet B :=
  relationName label (fun ij => lexLessValue (V B) (label ij.1) (label ij.2))

theorem lexOrderName_edge (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥) (i j : I) :
    edgeValue (V B) (lexOrderName label) (label i) (label j) =
      lexLessValue (V B) (label i) (label j) :=
  relationName_edge label hdiscrete _ i j

theorem lexOrderName_spec (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥) :
    ⊤ ≤ lexOrderValue (V B) (labelDomain label) (lexOrderName label) := by
  apply le_inf (relationName_between label _)
  let body : bSet B → bSet B → B := fun x y =>
    lattice.biimp (edgeValue (V B) (lexOrderName label) x y) (lexLessValue (V B) x y)
  have hleft (y : bSet B) : bSet.B_ext (fun x => body x y) :=
    bSet.B_ext_biimp (edge_left_ext _ y) (lexLess_left_ext y)
  have hright (x : bSet B) : bSet.B_ext (body x) :=
    bSet.B_ext_biimp (edge_right_ext _ x) (lexLess_right_ext x)
  change ⊤ ≤ ⨅ x : bSet B, lattice.imp (x ∈ᴮ weightedSet label (fun _ => ⊤))
    (⨅ y : bSet B, lattice.imp (y ∈ᴮ weightedSet label (fun _ => ⊤)) (body x y))
  rw [BooleanPosetModel.weighted_forall_two label (fun _ => ⊤) body hleft hright]
  apply le_iInf
  intro i
  simp only [lattice.imp, compl_top, bot_sup_eq]
  apply le_iInf
  intro j
  unfold body
  rw [lexOrderName_edge label hdiscrete]
  simp [lattice.biimp, lattice.imp]

theorem lexOrder_at {context : B} (label : I → bSet B) (order : bSet B)
    (horder : context ≤ lexOrderValue (V B) (labelDomain label) order) (i j : I) :
    context ≤ lattice.biimp (edgeValue (V B) order (label i) (label j))
      (lexLessValue (V B) (label i) (label j)) := by
  have hi := lattice.bv_context_apply ((horder.trans inf_le_right).trans (iInf_le _ (label i)))
    (le_top.trans (weight_le_member label (fun _ => ⊤) i))
  exact lattice.bv_context_apply (hi.trans (iInf_le _ (label j)))
    (le_top.trans (weight_le_member label (fun _ => ⊤) j))

theorem lexOrder_eq_name {context : B} (label : I → bSet B) (order : bSet B)
    (horder : context ≤ lexOrderValue (V B) (labelDomain label) order) :
    context ≤ order =ᴮ lexOrderName label := by
  apply bSet.bv_trans (relation_eq_coefficients context label order (horder.trans inf_le_left))
  apply relationName_congr
  intro ij
  have hpoint := lexOrder_at label order horder ij.1 ij.2
  apply le_antisymm
  · exact le_inf inf_le_left
      (lattice.bv_context_apply (inf_le_left.trans (hpoint.trans inf_le_left)) inf_le_right)
  · exact le_inf inf_le_left
      (lattice.bv_context_apply (inf_le_left.trans (hpoint.trans inf_le_right)) inf_le_right)

end Erdos597Object.CanonicalRelations
