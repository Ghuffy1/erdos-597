import Erdos597Object.BooleanIndependentFilters

set_option backward.isDefEq.respectTransparency false

/-! The limit row names supplied by directed finite independent conditions. -/

namespace Erdos597Object.BooleanIndependentLimits

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanIndependentConditions BooleanIteration BooleanPosetCoding
open BooleanInjections BooleanRectangles BooleanLocalGraphs BooleanFiniteGraphs CanonicalDomains

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def pointWeight (value : Finset Vertex → B) (v : Vertex) : B :=
  ⨆ points, ⨆ (_ : v ∈ points), value points

noncomputable def limitRow (value : Finset Vertex → B) (row : ℕ) : bSet B :=
  weightedSet blockLabel (fun key => pointWeight value (row, key))

theorem pointWeight_of_member (value : Finset Vertex → B) (points : Finset Vertex)
    (v : Vertex) (hv : v ∈ points) : value points ≤ pointWeight value v :=
  le_iSup_of_le points (le_iSup_of_le hv le_rfl)

theorem limitRow_member (value : Finset Vertex → B) (row : ℕ)
    (key : ℕ × ScheduledIteration.Labels) :
    (blockLabel key ∈ᴮ limitRow value row) = pointWeight value (row, key) :=
  member_weightedSet_discrete blockLabel blockLabel_discrete _ key

theorem pointWeight_row_member (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (value : Finset Vertex → B)
    (hvalid : ∀ p, value p ≤ (forcing base rows relation cut).member p) (v : Vertex) :
    pointWeight value v ≤ blockLabel v.2 ∈ᴮ rows v.1 := by
  apply iSup_le
  intro points
  apply iSup_le
  intro hv
  exact (hvalid points).trans (weight_row_member base rows relation cut points v hv)

theorem limitRow_subset (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (value : Finset Vertex → B)
    (hvalid : ∀ p, value p ≤ (forcing base rows relation cut).member p) (row : ℕ) :
    (⊤ : B) ≤ limitRow value row ⊆ᴮ rows row := by
  apply bSet.subset_intro
  intro key
  exact inf_le_right.trans (pointWeight_row_member base rows relation cut value hvalid (row, key))

theorem condition_cross_independent (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (value : Finset Vertex → B)
    (hvalid : ∀ p, value p ≤ (forcing base rows relation cut).member p)
    (hdir : ∀ p q, value p ⊓ value q ≤ ⨆ s, value s ⊓
      ((forcing base rows relation cut).leValue s p ⊓ (forcing base rows relation cut).leValue s q))
    (left right : Finset Vertex) (x y : Vertex) (hx : x ∈ left) (hy : y ∈ right)
    (hrow : x.1 ≠ y.1) :
    value left ⊓ value right ≤
      (edgeValue (V B) relation (blockLabel x.2) (blockLabel y.2))ᶜ := by
  classical
  apply (hdir left right).trans
  apply iSup_le
  intro points
  by_cases hleft : left ⊆ points
  · by_cases hright : right ⊆ points
    · exact (inf_le_left.trans (hvalid points)).trans
        (weight_independent base rows relation cut points x y (hleft hx) (hright hy) hrow)
    · have hz : (forcing base rows relation cut).leValue points right = ⊥ := by
        simp only [forcing, ite_eq_right hright]
      exact ((inf_le_right.trans inf_le_right).trans_eq hz).trans bot_le
  · have hz : (forcing base rows relation cut).leValue points left = ⊥ := by
      simp only [forcing, ite_eq_right hleft]
    exact ((inf_le_right.trans inf_le_left).trans_eq hz).trans bot_le

theorem pointWeight_independent (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (value : Finset Vertex → B)
    (hvalid : ∀ p, value p ≤ (forcing base rows relation cut).member p)
    (hdir : ∀ p q, value p ⊓ value q ≤ ⨆ s, value s ⊓
      ((forcing base rows relation cut).leValue s p ⊓ (forcing base rows relation cut).leValue s q))
    (x y : Vertex) (hrow : x.1 ≠ y.1) :
    pointWeight value x ⊓ pointWeight value y ≤
      (edgeValue (V B) relation (blockLabel x.2) (blockLabel y.2))ᶜ := by
  change (⨆ p, ⨆ (_ : x ∈ p), value p) ⊓ pointWeight value y ≤ _
  simp only [iSup_inf_eq]
  apply iSup_le
  intro p
  apply iSup_le
  intro hp
  change value p ⊓ (⨆ q, ⨆ (_ : y ∈ q), value q) ≤ _
  simp only [inf_iSup_eq]
  apply iSup_le
  intro q
  apply iSup_le
  intro hq
  exact condition_cross_independent base rows relation cut value hvalid hdir p q x y hp hq hrow

theorem limitRows_empty_rectangle (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (value : Finset Vertex → B)
    (hvalid : ∀ p, value p ≤ (forcing base rows relation cut).member p)
    (hdir : ∀ p q, value p ⊓ value q ≤ ⨆ s, value s ⊓
      ((forcing base rows relation cut).leValue s p ⊓ (forcing base rows relation cut).leValue s q))
    (left right : ℕ) (hne : left ≠ right) :
    (⊤ : B) ≤ emptyRectangle relation (limitRow value left) (limitRow value right) := by
  rw [emptyRectangle_spec]
  change (⊤ : B) ≤ ⨅ x : bSet B, lattice.imp
    (x ∈ᴮ weightedSet blockLabel (fun key => pointWeight value (left, key)))
    (⨅ y : bSet B, lattice.imp
      (y ∈ᴮ weightedSet blockLabel (fun key => pointWeight value (right, key)))
      (edgeValue (V B) relation x y)ᶜ)
  rw [weighted_bounded_forall blockLabel _ _ (bSet.B_ext_iInf fun y =>
    bSet.B_ext_imp (bSet.B_ext_const _) (bSet.B_ext_compl (edge_left_ext relation y)))]
  apply le_iInf
  intro x
  apply lattice.bv_imp_intro
  rw [weighted_bounded_forall blockLabel _ _ (bSet.B_ext_compl (edge_right_ext relation (blockLabel x)))]
  apply le_iInf
  intro y
  apply lattice.bv_imp_intro
  exact (inf_le_inf_right _ inf_le_right).trans
    (pointWeight_independent base rows relation cut value hvalid hdir (left, x) (right, y) hne)

theorem independentValue_mono (context : B) (relation small large : bSet B)
    (hsubset : context ≤ small ⊆ᴮ large) (hlarge : context ≤ independentValue large relation) :
    context ≤ independentValue small relation := by
  apply le_iInf
  intro x
  apply lattice.bv_imp_intro
  apply le_iInf
  intro y
  apply lattice.bv_imp_intro
  have hcontext : (context ⊓ (x ∈ᴮ small)) ⊓ (y ∈ᴮ small) ≤ context :=
    inf_le_left.trans inf_le_left
  have hx : (context ⊓ (x ∈ᴮ small)) ⊓ (y ∈ᴮ small) ≤ x ∈ᴮ large :=
    bSet.mem_of_mem_subset' (hcontext.trans hsubset) (inf_le_left.trans inf_le_right)
  have hy : (context ⊓ (x ∈ᴮ small)) ⊓ (y ∈ᴮ small) ≤ y ∈ᴮ large :=
    bSet.mem_of_mem_subset' (hcontext.trans hsubset) inf_le_right
  have hfirst := lattice.bv_context_apply ((hcontext.trans hlarge).trans (iInf_le _ x)) hx
  exact lattice.bv_context_apply (hfirst.trans (iInf_le _ y)) hy

theorem limitRow_independent (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (value : Finset Vertex → B)
    (hvalid : ∀ p, value p ≤ (forcing base rows relation cut).member p)
    (hindependent : ∀ row, base ≤ independentValue (rows row) relation) (row : ℕ) :
    base ≤ independentValue (limitRow value row) relation :=
  independentValue_mono base relation _ _
    (le_top.trans (limitRow_subset base rows relation cut value hvalid row)) (hindependent row)

end Erdos597Object.BooleanIndependentLimits
