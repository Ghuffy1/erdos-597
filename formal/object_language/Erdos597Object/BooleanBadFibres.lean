import Erdos597Object.BooleanCountableRectangles
import Erdos597Object.BooleanGoodPairs

set_option backward.isDefEq.respectTransparency false

/-! In a bad pair, only countably many vertices have countable forward fibres. -/

namespace Erdos597Object.BooleanBadFibres

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanCountableNames BooleanGraphNeighborhoods
open BooleanUncountableRamsey BooleanRectangles BooleanGoodPairs BooleanCountableRectangles

variable {B : Type} [CompleteBooleanAlgebra B]

theorem neighborhood_congr (domain relation : bSet B) :
    bSet.B_congr (fun name => neighborhood domain relation name) := by
  intro x y
  apply bSet.mem_ext
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    rw [member_neighborhood, member_neighborhood]
    apply le_inf (inf_le_right.trans inf_le_left)
    exact (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans (edge_left_ext relation z x y)
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    rw [member_neighborhood, member_neighborhood]
    apply le_inf (inf_le_right.trans inf_le_left)
    exact (le_inf (bSet.bv_symm inf_le_left) (inf_le_right.trans inf_le_right)).trans
      (edge_left_ext relation z y x)

theorem countable_neighborhood_ext (domain relation : bSet B) :
    bSet.B_ext (fun name => injectsIntoValue (V B) (neighborhood domain relation name) bSet.omega) := by
  simp_rw [BooleanFunctionBridge.injectsInto_eq_injects_into]
  intro x y
  exact (le_inf (inf_le_left.trans (neighborhood_congr domain relation x y)) inf_le_right).trans
    (bSet.B_ext_injects_into_left (neighborhood domain relation x) (neighborhood domain relation y))

noncomputable def smallFibres (relation left right : bSet B) : bSet B :=
  bSet.comprehend (fun name => injectsIntoValue (V B) (neighborhood right relation name) bSet.omega) left

theorem member_smallFibres (relation left right name : bSet B) :
    name ∈ᴮ smallFibres relation left right = (name ∈ᴮ left) ⊓
      injectsIntoValue (V B) (neighborhood right relation name) bSet.omega :=
  member_comprehend _ (countable_neighborhood_ext right relation) left name

theorem smallFibres_subset (relation left right : bSet B) :
    ⊤ ≤ smallFibres relation left right ⊆ᴮ left := bSet.comprehend_subset

theorem predecessors_mono (context : B) (relation small large name : bSet B)
    (hsubset : context ≤ small ⊆ᴮ large) :
    context ≤ predecessors small relation name ⊆ᴮ predecessors large relation name := by
  apply bSet.subset_unfold'.mpr
  apply le_iInf
  intro x
  apply lattice.bv_imp_intro
  rw [member_predecessors, member_predecessors]
  exact le_inf (bSet.mem_of_mem_subset' (inf_le_left.trans hsubset) (inf_le_right.trans inf_le_left))
    (inf_le_right.trans inf_le_right)

theorem countable_smallFibres (hB : Flypitch.BA_CCC B) (context : B)
    (relation left right : bSet B) (leftLabels rightLabels : Erdos597.One → bSet B)
    (hleftDiscrete : ∀ i j, i ≠ j → (leftLabels i =ᴮ leftLabels j) = ⊥)
    (hrightDiscrete : ∀ i j, i ≠ j → (rightLabels i =ᴮ rightLabels j) = ⊥)
    (hleftSubset : context ≤ left ⊆ᴮ weightedSet leftLabels (fun _ => ⊤))
    (hrightSubset : context ≤ right ⊆ᴮ weightedSet rightLabels (fun _ => ⊤))
    (hrightLarge : context ≤ (injectsIntoValue (V B) right bSet.omega)ᶜ)
    (hbad : context ≤ badPair relation left right)
    (hbackward : ∀ y, context ⊓ (y ∈ᴮ right) ≤
      injectsIntoValue (V B) (predecessors left relation y) bSet.omega) :
    context ≤ injectsIntoValue (V B) (smallFibres relation left right) bSet.omega := by
  let small := smallFibres relation left right
  let part := context ⊓ (injectsIntoValue (V B) small bSet.omega)ᶜ
  have hsmallSubset : part ≤ small ⊆ᴮ left := le_top.trans (smallFibres_subset relation left right)
  have hforward (x : bSet B) (hx : part ≤ x ∈ᴮ small) :
      part ≤ injectsIntoValue (V B) (neighborhood right relation x) bSet.omega := by
    rw [member_smallFibres] at hx
    exact hx.trans inf_le_right
  have hbackwardSmall (y : bSet B) (hy : part ≤ y ∈ᴮ right) :
      part ≤ injectsIntoValue (V B) (predecessors small relation y) bSet.omega :=
    subset_countable _ _ (predecessors_mono part relation small left y hsmallSubset)
      ((le_inf inf_le_left hy).trans (hbackward y))
  obtain ⟨smallLeft, smallRight, hsmallLeft, hsmallRight, hempty⟩ :=
    countable_fibres_rectangle hB part relation small right leftLabels rightLabels
      hleftDiscrete hrightDiscrete
      (subset_trans hsmallSubset (inf_le_left.trans hleftSubset)) (inf_le_left.trans hrightSubset)
      inf_le_right (inf_le_left.trans hrightLarge) hforward hbackwardSmall
  have hlargeLeft : part ≤ largeSubset left smallLeft :=
    le_inf (subset_trans (hsmallLeft.trans inf_le_left) hsmallSubset) (hsmallLeft.trans inf_le_right)
  obtain ⟨x, y, hx, hy, hedge⟩ := badPair_edge part relation left right smallLeft smallRight
    (inf_le_left.trans hbad) hlargeLeft hsmallRight
  have hnoEdge := emptyRectangle_no_edge part relation smallLeft smallRight x y hempty hx hy
  have hzero : part ≤ ⊥ := (le_inf hedge hnoEdge).trans_eq inf_compl_eq_bot
  have hdouble : context ≤ ((injectsIntoValue (V B) small bSet.omega)ᶜ)ᶜ :=
    le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr (bot_unique hzero))
  simpa only [compl_compl] using hdouble

end Erdos597Object.BooleanBadFibres
