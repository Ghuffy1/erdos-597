import Erdos597Object.CanonicalRelations
import Erdos597Object.BooleanSymmetricPairs

set_option backward.isDefEq.respectTransparency false

/-! Subgraphs obtained by symmetric masks on the canonical labels. -/

namespace Erdos597Object.BooleanMaskedGraphs

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanFiniteGraphs BooleanInjections CanonicalRelations

variable {B I : Type} [CompleteBooleanAlgebra B]

open Classical in
attribute [local instance] propDecidable

noncomputable def maskedName (label : I → bSet B) (relation : bSet B)
    (mask : I → I → Prop) : bSet B := by
  classical
  exact relationName label (fun ij =>
    if mask ij.1 ij.2 then edgeValue (V B) relation (label ij.1) (label ij.2) else ⊥)

theorem masked_edge (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (relation : bSet B) (mask : I → I → Prop) (i j : I) :
    edgeValue (V B) (maskedName label relation mask) (label i) (label j) =
      if mask i j then edgeValue (V B) relation (label i) (label j) else ⊥ := by
  classical
  exact relationName_edge label hdiscrete _ i j

theorem masked_subset (label : I → bSet B) (relation : bSet B) (mask : I → I → Prop) :
    (⊤ : B) ≤ maskedName label relation mask ⊆ᴮ relation := by
  classical
  apply bSet.subset_intro
  intro ij
  change (⊤ : B) ⊓ (if mask ij.1 ij.2 then
    edgeValue (V B) relation (label ij.1) (label ij.2) else ⊥) ≤
      edgeValue (V B) relation (label ij.1) (label ij.2)
  split_ifs <;> simp only [top_inf_eq, le_refl, bot_le]

theorem masked_edge_le (label : I → bSet B) (relation : bSet B)
    (mask : I → I → Prop) (context : B) (x y : bSet B) :
    context ⊓ edgeValue (V B) (maskedName label relation mask) x y ≤
      edgeValue (V B) relation x y :=
  bSet.mem_of_mem_subset' (le_top.trans (masked_subset label relation mask)) inf_le_right

theorem masked_graph (context : B) (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (relation : bSet B) (hgraph : context ≤ graphValue (V B) (labelDomain label) relation)
    (mask : I → I → Prop) (hsymmetric : ∀ i j, mask i j ↔ mask j i) :
    context ≤ graphValue (V B) (labelDomain label) (maskedName label relation mask) := by
  classical
  apply le_inf
  · exact le_top.trans (relationName_between label _)
  · apply le_inf
    · have hself : bSet.B_ext (fun x => edgeValue (V B) (maskedName label relation mask) x x) := by
        intro x y
        have hpair : (x =ᴮ y) ⊓ (bSet.pair x x ∈ᴮ maskedName label relation mask) ≤
            bSet.pair x x =ᴮ bSet.pair y y := bSet.pair_congr inf_le_left inf_le_left
        exact bSet.subst_congr_mem_left' hpair inf_le_right
      change context ≤ ⨅ x : bSet B, lattice.imp (x ∈ᴮ weightedSet label (fun _ => ⊤))
        (edgeValue (V B) (maskedName label relation mask) x x)ᶜ
      rw [weighted_bounded_forall label (fun _ => ⊤) _ (bSet.B_ext_compl hself)]
      apply le_iInf
      intro i
      simp only [lattice.imp, compl_top, bot_sup_eq]
      rw [masked_edge label hdiscrete]
      by_cases h : mask i i
      · rw [ite_eq_left h]
        exact graph_loopless context label relation hgraph i
      · simp only [ite_eq_right h, compl_bot, le_top]
    · let symmetry : bSet B → bSet B → B := fun x y =>
        lattice.imp (edgeValue (V B) (maskedName label relation mask) x y)
          (edgeValue (V B) (maskedName label relation mask) y x) ⊓
        lattice.imp (edgeValue (V B) (maskedName label relation mask) y x)
          (edgeValue (V B) (maskedName label relation mask) x y)
      have hleft (y : bSet B) : bSet.B_ext (fun x => symmetry x y) :=
        bSet.B_ext_inf
          (bSet.B_ext_imp (edge_left_ext _ y) (edge_right_ext _ y))
          (bSet.B_ext_imp (edge_right_ext _ y) (edge_left_ext _ y))
      have hright (x : bSet B) : bSet.B_ext (symmetry x) :=
        bSet.B_ext_inf
          (bSet.B_ext_imp (edge_right_ext _ x) (edge_left_ext _ x))
          (bSet.B_ext_imp (edge_left_ext _ x) (edge_right_ext _ x))
      change context ≤ ⨅ x : bSet B, lattice.imp (x ∈ᴮ weightedSet label (fun _ => ⊤))
        (⨅ y : bSet B, lattice.imp (y ∈ᴮ weightedSet label (fun _ => ⊤)) (symmetry x y))
      rw [BooleanPosetModel.weighted_forall_two label (fun _ => ⊤) symmetry hleft hright]
      simp only [lattice.imp, compl_top, bot_sup_eq]
      apply le_iInf
      intro i
      apply le_iInf
      intro j
      unfold symmetry
      rw [masked_edge label hdiscrete, masked_edge label hdiscrete]
      by_cases h : mask i j
      · rw [ite_eq_left h, ite_eq_left ((hsymmetric i j).mp h)]
        exact le_inf
          (lattice.le_imp_iff.mpr (graph_symmetric context label relation hgraph i j))
          (lattice.le_imp_iff.mpr (graph_symmetric context label relation hgraph j i))
      · have hreverse : ¬ mask j i := fun hji => h ((hsymmetric i j).mpr hji)
        simp only [ite_eq_right h, ite_eq_right hreverse, lattice.imp, compl_bot, top_sup_eq,
          inf_top_eq, le_top]

theorem complementary_edges (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (relation : bSet B) (mask : I → I → Prop) (i j : I) :
    edgeValue (V B) (maskedName label relation mask) (label i) (label j) ⊔
      edgeValue (V B) (maskedName label relation (fun i j => ¬ mask i j)) (label i) (label j) =
        edgeValue (V B) relation (label i) (label j) := by
  classical
  rw [masked_edge label hdiscrete, masked_edge label hdiscrete]
  by_cases h : mask i j <;> simp only [h, not_true_eq_false, not_false_eq_true, ↓reduceIte,
    sup_bot_eq, bot_sup_eq]

end Erdos597Object.BooleanMaskedGraphs
