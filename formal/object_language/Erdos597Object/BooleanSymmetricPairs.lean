import Erdos597Object.BooleanGoodPairs
import Erdos597Object.BooleanCountableRectangles

set_option backward.isDefEq.respectTransparency false

/-! Symmetry transfers for uncountable graph rectangles and countable fibres. -/

namespace Erdos597Object.BooleanSymmetricPairs

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanRectangles BooleanGoodPairs BooleanGraphNeighborhoods
open BooleanCountableRectangles BooleanCountableNames BooleanUncountableRamsey

variable {B : Type} [CompleteBooleanAlgebra B]

theorem rectangleEdge_swap (context : B) (ambient relation left right : bSet B)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hleft : context ≤ left ⊆ᴮ ambient) (hright : context ≤ right ⊆ᴮ ambient) :
    context ⊓ rectangleEdge relation left right ≤ rectangleEdge relation right left := by
  let part := context ⊓ rectangleEdge relation left right
  obtain ⟨x, y, hx, hy, hedge⟩ := rectangleEdge_witness part relation left right inf_le_right
  have hxAmbient : part ≤ x ∈ᴮ ambient := bSet.mem_of_mem_subset' (inf_le_left.trans hleft) hx
  have hyAmbient : part ≤ y ∈ᴮ ambient := bSet.mem_of_mem_subset' (inf_le_left.trans hright) hy
  have hreverse : part ≤ edgeValue (V B) relation y x :=
    (le_inf le_rfl hedge).trans
      (graph_symmetry part ambient relation x y (inf_le_left.trans hgraph) hxAmbient hyAmbient)
  exact le_iSup_of_le y (le_inf hy (le_iSup_of_le x (le_inf hx hreverse)))

theorem emptyRectangle_swap (context : B) (ambient relation left right : bSet B)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hleft : context ≤ left ⊆ᴮ ambient) (hright : context ≤ right ⊆ᴮ ambient) :
    context ⊓ emptyRectangle relation left right ≤ emptyRectangle relation right left := by
  apply le_compl_iff_disjoint_right.mpr
  rw [disjoint_iff]
  apply bot_unique
  have hedge : context ⊓ emptyRectangle relation left right ⊓ rectangleEdge relation right left ≤
      rectangleEdge relation left right :=
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans
      (rectangleEdge_swap context ambient relation right left hgraph hright hleft)
  exact (le_inf hedge (inf_le_left.trans inf_le_right)).trans_eq inf_compl_eq_bot

theorem badPair_swap (context : B) (ambient relation left right : bSet B)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hleft : context ≤ left ⊆ᴮ ambient) (hright : context ≤ right ⊆ᴮ ambient)
    (hbad : context ≤ badPair relation left right) : context ≤ badPair relation right left := by
  apply le_iInf
  intro testRight
  apply lattice.bv_imp_intro
  apply le_iInf
  intro testLeft
  apply lattice.bv_imp_intro
  let part := (context ⊓ largeSubset right testRight) ⊓ largeSubset left testLeft
  have hpart : part ≤ context := inf_le_left.trans inf_le_left
  have hleftLarge : part ≤ largeSubset left testLeft := inf_le_right
  have hrightLarge : part ≤ largeSubset right testRight := inf_le_left.trans inf_le_right
  obtain ⟨x, y, hx, hy, hedge⟩ := badPair_edge part relation left right testLeft testRight
    (hpart.trans hbad) hleftLarge hrightLarge
  have hxAmbient : part ≤ x ∈ᴮ ambient := bSet.mem_of_mem_subset'
    (subset_trans (hleftLarge.trans inf_le_left) (hpart.trans hleft)) hx
  have hyAmbient : part ≤ y ∈ᴮ ambient := bSet.mem_of_mem_subset'
    (subset_trans (hrightLarge.trans inf_le_left) (hpart.trans hright)) hy
  have hreverse : part ≤ edgeValue (V B) relation y x :=
    (le_inf le_rfl hedge).trans
      (graph_symmetry part ambient relation x y (hpart.trans hgraph) hxAmbient hyAmbient)
  exact le_iSup_of_le y (le_inf hy (le_iSup_of_le x (le_inf hx hreverse)))

theorem goodPair_swap (context : B) (ambient relation left right : bSet B)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hleft : context ≤ left ⊆ᴮ ambient) (hright : context ≤ right ⊆ᴮ ambient)
    (hgood : context ≤ goodPair relation left right) : context ≤ goodPair relation right left := by
  apply le_iInf
  intro testRight
  apply lattice.bv_imp_intro
  apply le_iInf
  intro testLeft
  apply lattice.bv_imp_intro
  let part := (context ⊓ largeSubset right testRight) ⊓ largeSubset left testLeft
  have hpart : part ≤ context := inf_le_left.trans inf_le_left
  have hleftLarge : part ≤ largeSubset left testLeft := inf_le_right
  have hrightLarge : part ≤ largeSubset right testRight := inf_le_left.trans inf_le_right
  obtain ⟨smallLeft, smallRight, hsmallLeft, hsmallRight, hempty⟩ :=
    goodPair_refine part relation left right testLeft testRight (hpart.trans hgood) hleftLarge hrightLarge
  have hleftAmbient : part ≤ smallLeft ⊆ᴮ ambient := subset_trans (hsmallLeft.trans inf_le_left)
    (subset_trans (hleftLarge.trans inf_le_left) (hpart.trans hleft))
  have hrightAmbient : part ≤ smallRight ⊆ᴮ ambient := subset_trans (hsmallRight.trans inf_le_left)
    (subset_trans (hrightLarge.trans inf_le_left) (hpart.trans hright))
  have hreverse := (le_inf le_rfl hempty).trans
    (emptyRectangle_swap part ambient relation smallLeft smallRight
      (hpart.trans hgraph) hleftAmbient hrightAmbient)
  exact le_iSup_of_le smallRight (le_inf hsmallRight
    (le_iSup_of_le smallLeft (le_inf hsmallLeft hreverse)))

theorem predecessors_subset_neighborhood (context : B) (ambient relation domain name : bSet B)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hdomain : context ≤ domain ⊆ᴮ ambient) (hname : context ≤ name ∈ᴮ ambient) :
    context ≤ predecessors domain relation name ⊆ᴮ neighborhood domain relation name := by
  apply bSet.subset_unfold'.mpr
  apply le_iInf
  intro other
  apply lattice.bv_imp_intro
  rw [member_predecessors, member_neighborhood]
  let part := context ⊓ ((other ∈ᴮ domain) ⊓ edgeValue (V B) relation other name)
  have hother : part ≤ other ∈ᴮ ambient :=
    bSet.mem_of_mem_subset' (inf_le_left.trans hdomain) (inf_le_right.trans inf_le_left)
  apply le_inf (inf_le_right.trans inf_le_left)
  exact (le_inf le_rfl (inf_le_right.trans inf_le_right)).trans
    (graph_symmetry part ambient relation other name (inf_le_left.trans hgraph)
      hother (inf_le_left.trans hname))

theorem neighborhood_mono (context : B) (relation small large name : bSet B)
    (hsubset : context ≤ small ⊆ᴮ large) :
    context ≤ neighborhood small relation name ⊆ᴮ neighborhood large relation name := by
  apply bSet.subset_unfold'.mpr
  apply le_iInf
  intro other
  apply lattice.bv_imp_intro
  rw [member_neighborhood, member_neighborhood]
  exact le_inf
    (bSet.mem_of_mem_subset' (inf_le_left.trans hsubset) (inf_le_right.trans inf_le_left))
    (inf_le_right.trans inf_le_right)

theorem countable_predecessors_of_neighborhood (context : B)
    (ambient relation domain name : bSet B)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hdomain : context ≤ domain ⊆ᴮ ambient) (hname : context ≤ name ∈ᴮ ambient)
    (hcountable : context ≤ injectsIntoValue (V B) (neighborhood domain relation name) bSet.omega) :
    context ≤ injectsIntoValue (V B) (predecessors domain relation name) bSet.omega :=
  subset_countable _ _
    (predecessors_subset_neighborhood context ambient relation domain name hgraph hdomain hname) hcountable

end Erdos597Object.BooleanSymmetricPairs
