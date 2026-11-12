import Erdos597Object.BooleanRedBlockExclusion
import Erdos597Object.SetInterpretation

set_option backward.isDefEq.respectTransparency false

/-! Finite K4-free graph names satisfy the literal first-order exclusion predicate. -/

namespace Erdos597Object.BooleanFiniteCliqueFree

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanFiniteGraphs

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem fourClique_first_ext (edges b c d : bSet B) :
    bSet.B_ext (fun a => fourCliqueValue (V B) edges a b c d) := by
  unfold fourCliqueValue
  exact bSet.B_ext_inf (edge_left_ext edges b)
    (bSet.B_ext_inf (edge_left_ext edges c)
      (bSet.B_ext_inf (edge_left_ext edges d) (bSet.B_ext_const _)))

theorem fourClique_second_ext (edges a c d : bSet B) :
    bSet.B_ext (fun b => fourCliqueValue (V B) edges a b c d) := by
  unfold fourCliqueValue
  exact bSet.B_ext_inf (edge_right_ext edges a)
    (bSet.B_ext_inf (bSet.B_ext_const _)
      (bSet.B_ext_inf (bSet.B_ext_const _)
        (bSet.B_ext_inf (edge_left_ext edges c)
          (bSet.B_ext_inf (edge_left_ext edges d) (bSet.B_ext_const _)))))

theorem fourClique_third_ext (edges a b d : bSet B) :
    bSet.B_ext (fun c => fourCliqueValue (V B) edges a b c d) := by
  unfold fourCliqueValue
  exact bSet.B_ext_inf (bSet.B_ext_const _)
    (bSet.B_ext_inf (edge_right_ext edges a)
      (bSet.B_ext_inf (bSet.B_ext_const _)
        (bSet.B_ext_inf (edge_right_ext edges b)
          (bSet.B_ext_inf (bSet.B_ext_const _) (edge_left_ext edges d)))))

theorem fourClique_fourth_ext (edges a b c : bSet B) :
    bSet.B_ext (fourCliqueValue (V B) edges a b c) := by
  unfold fourCliqueValue
  exact bSet.B_ext_inf (bSet.B_ext_const _)
    (bSet.B_ext_inf (bSet.B_ext_const _)
      (bSet.B_ext_inf (edge_right_ext edges a)
        (bSet.B_ext_inf (bSet.B_ext_const _)
          (bSet.B_ext_inf (edge_right_ext edges b) (edge_right_ext edges c)))))

theorem ground_fourClique_eq_bot (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (H : SimpleGraph I) (hH : H.CliqueFree 4) (a b c d : I) :
    fourCliqueValue (V B) (graphName label H) (label a) (label b) (label c) (label d) = ⊥ := by
  classical
  have hnot := (SetInterpretation.cliqueFree_four_iff H).mp hH a b c d
  simp only [not_and_or] at hnot
  unfold fourCliqueValue
  simp only [graphName_edge label hdiscrete]
  rcases hnot with h | h | h | h | h | h <;> simp [graphCoefficient, h]

theorem graphName_cliqueFree (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (H : SimpleGraph I) (hH : H.CliqueFree 4) :
    ⊤ ≤ cliqueFreeFourValue (V B) (labelDomain label) (graphName label H) := by
  let edges := graphName label H
  let body := fun a b c : bSet B => ⨅ d : bSet B,
    lattice.imp (d ∈ᴮ labelDomain label) (fourCliqueValue (V B) edges a b c d)ᶜ
  have hfirst : ∀ b c, bSet.B_ext (fun a => body a b c) := fun b c =>
    bSet.B_ext_iInf fun d => bSet.B_ext_imp (bSet.B_ext_const _)
      (bSet.B_ext_compl (fourClique_first_ext edges b c d))
  have hsecond : ∀ a c, bSet.B_ext (fun b => body a b c) := fun a c =>
    bSet.B_ext_iInf fun d => bSet.B_ext_imp (bSet.B_ext_const _)
      (bSet.B_ext_compl (fourClique_second_ext edges a c d))
  have hthird : ∀ a b, bSet.B_ext (body a b) := fun a b =>
    bSet.B_ext_iInf fun d => bSet.B_ext_imp (bSet.B_ext_const _)
      (bSet.B_ext_compl (fourClique_third_ext edges a b d))
  change ⊤ ≤ ⨅ a : bSet B, lattice.imp (a ∈ᴮ weightedSet label (fun _ => ⊤))
    (⨅ b : bSet B, lattice.imp (b ∈ᴮ weightedSet label (fun _ => ⊤))
      (⨅ c : bSet B, lattice.imp (c ∈ᴮ weightedSet label (fun _ => ⊤)) (body a b c)))
  rw [BooleanPosetModel.weighted_forall_three label (fun _ => ⊤) body hfirst hsecond hthird]
  simp only [lattice.imp, compl_top, bot_sup_eq]
  apply le_iInf
  intro a
  apply le_iInf
  intro b
  apply le_iInf
  intro c
  change ⊤ ≤ ⨅ d : bSet B, lattice.imp (d ∈ᴮ weightedSet label (fun _ => ⊤))
    (fourCliqueValue (V B) edges (label a) (label b) (label c) d)ᶜ
  rw [weighted_bounded_forall label (fun _ => ⊤) _
    (bSet.B_ext_compl (fourClique_fourth_ext edges (label a) (label b) (label c)))]
  apply le_iInf
  intro d
  rw [ground_fourClique_eq_bot label hdiscrete H hH a b c d]
  simp [lattice.imp]

end Erdos597Object.BooleanFiniteCliqueFree
