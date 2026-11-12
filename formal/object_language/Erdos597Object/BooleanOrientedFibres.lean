import Erdos597Object.BooleanOrientedGraphs
import Erdos597Object.BooleanBadFibres

set_option backward.isDefEq.respectTransparency false

/-! Countable backward and forward fibres between ordered canonical subsets. -/

namespace Erdos597Object.BooleanOrientedFibres

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanColumns BooleanRowOrder CanonicalDomains
open BooleanFiniteGraphs BooleanInjections
open BooleanOrientedGraphs BooleanGraphNeighborhoods BooleanCountableRectangles
open BooleanCountableNames BooleanUncountableRamsey BooleanBadFibres

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem property_of_label_members (context : B) (label : I → bSet B)
    (domain : bSet B) (predicate : bSet B → B) (hext : bSet.B_ext predicate)
    (hsubset : context ≤ domain ⊆ᴮ labelDomain label)
    (hlabel : ∀ i, context ⊓ (label i ∈ᴮ domain) ≤ predicate (label i)) (name : bSet B) :
    context ⊓ (name ∈ᴮ domain) ≤ predicate name := by
  let body := fun x => lattice.imp (x ∈ᴮ domain) (predicate x)
  have hbody : bSet.B_ext body := bSet.B_ext_imp (bSet.B_ext_mem_left domain) hext
  have hall : context ≤ ⨅ x : bSet B,
      lattice.imp (x ∈ᴮ labelDomain label) (body x) := by
    change context ≤ ⨅ x : bSet B,
      lattice.imp (x ∈ᴮ weightedSet label (fun _ => ⊤)) (body x)
    rw [weighted_bounded_forall label (fun _ => ⊤) body hbody]
    simp only [lattice.imp, compl_top, bot_sup_eq]
    exact le_iInf (fun i => lattice.bv_imp_intro (hlabel i))
  have hmember : context ⊓ (name ∈ᴮ domain) ≤ name ∈ᴮ labelDomain label :=
    bSet.mem_of_mem_subset' (inf_le_left.trans hsubset) inf_le_right
  have hbodyName := lattice.bv_context_apply
    ((inf_le_left.trans hall).trans (iInf_le _ name)) hmember
  exact lattice.bv_context_apply hbodyName inf_le_right

theorem predecessors_congr (domain relation : bSet B) :
    bSet.B_congr (fun name => predecessors domain relation name) := by
  intro x y
  apply bSet.mem_ext
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    rw [member_predecessors, member_predecessors]
    apply le_inf (inf_le_right.trans inf_le_left)
    exact (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans (edge_right_ext relation z x y)
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    rw [member_predecessors, member_predecessors]
    apply le_inf (inf_le_right.trans inf_le_left)
    exact (le_inf (bSet.bv_symm inf_le_left) (inf_le_right.trans inf_le_right)).trans
      (edge_right_ext relation z y x)

theorem countable_predecessors_ext (domain relation : bSet B) :
    bSet.B_ext (fun name => injectsIntoValue (V B) (predecessors domain relation name) bSet.omega) := by
  simp_rw [BooleanFunctionBridge.injectsInto_eq_injects_into]
  intro x y
  exact (le_inf (inf_le_left.trans (predecessors_congr domain relation x y)) inf_le_right).trans
    (bSet.B_ext_injects_into_left (predecessors domain relation x) (predecessors domain relation y))

theorem up_predecessors_label_countable (context : B) (relation left right : bSet B)
    (hleft : context ≤ left ⊆ᴮ blockDomain)
    (hbefore : context ≤ allBefore blockOrder left right)
    (j : ℕ × ScheduledIteration.Labels) (hmember : context ≤ blockLabel j ∈ᴮ right) :
    context ≤ injectsIntoValue (V B) (predecessors left (upPart relation) (blockLabel j))
      bSet.omega := by
  apply countable_of_label_members context _ (column j.2)
  · exact subset_trans (le_top.trans bSet.comprehend_subset) hleft
  · intro i hi
    let part : B := context ⊓ (blockLabel i ∈ᴮ predecessors left (upPart relation) (blockLabel j))
    have hleftMember : part ≤ blockLabel i ∈ᴮ left := by
      dsimp [part]
      rw [member_predecessors]
      exact inf_le_right.trans inf_le_left
    have hedge : part ≤ edgeValue (V B) (upPart relation) (blockLabel i) (blockLabel j) := by
      dsimp [part]
      rw [member_predecessors]
      exact inf_le_right.trans inf_le_right
    have horder : part ≤ edgeValue (V B) blockOrder (blockLabel i) (blockLabel j) :=
      (le_inf inf_le_left (le_inf hleftMember (inf_le_left.trans hmember))).trans
        (allBefore_elim context blockOrder left right hbefore (blockLabel i) (blockLabel j))
    exact (le_inf horder hedge).trans_eq (up_ordered_edge_bot relation i j hi)

theorem down_neighborhood_label_countable (context : B) (relation left right : bSet B)
    (hright : context ≤ right ⊆ᴮ blockDomain)
    (hbefore : context ≤ allBefore blockOrder left right)
    (i : ℕ × ScheduledIteration.Labels) (hmember : context ≤ blockLabel i ∈ᴮ left) :
    context ≤ injectsIntoValue (V B) (neighborhood right (downPart relation) (blockLabel i))
      bSet.omega := by
  apply countable_of_label_members context _ (column i.2)
  · exact subset_trans (le_top.trans (neighborhood_subset right (downPart relation) (blockLabel i))) hright
  · intro j hj
    let part : B := context ⊓ (blockLabel j ∈ᴮ neighborhood right (downPart relation) (blockLabel i))
    have hrightMember : part ≤ blockLabel j ∈ᴮ right := by
      dsimp [part]
      rw [member_neighborhood]
      exact inf_le_right.trans inf_le_left
    have hedge : part ≤ edgeValue (V B) (downPart relation) (blockLabel i) (blockLabel j) := by
      dsimp [part]
      rw [member_neighborhood]
      exact inf_le_right.trans inf_le_right
    have horder : part ≤ edgeValue (V B) blockOrder (blockLabel i) (blockLabel j) :=
      (le_inf inf_le_left (le_inf (inf_le_left.trans hmember) hrightMember)).trans
        (allBefore_elim context blockOrder left right hbefore (blockLabel i) (blockLabel j))
    exact (le_inf horder hedge).trans_eq (down_ordered_edge_bot relation i j hj)

theorem up_predecessors_countable (context : B) (relation left right : bSet B)
    (hleft : context ≤ left ⊆ᴮ blockDomain) (hright : context ≤ right ⊆ᴮ blockDomain)
    (hbefore : context ≤ allBefore blockOrder left right) (name : bSet B) :
    context ⊓ (name ∈ᴮ right) ≤
      injectsIntoValue (V B) (predecessors left (upPart relation) name) bSet.omega := by
  apply property_of_label_members context blockLabel right _
    (countable_predecessors_ext left (upPart relation)) hright _ name
  intro j
  exact up_predecessors_label_countable (context ⊓ (blockLabel j ∈ᴮ right)) relation left right
    (inf_le_left.trans hleft) (inf_le_left.trans hbefore) j inf_le_right

theorem down_neighborhood_countable (context : B) (relation left right : bSet B)
    (hleft : context ≤ left ⊆ᴮ blockDomain) (hright : context ≤ right ⊆ᴮ blockDomain)
    (hbefore : context ≤ allBefore blockOrder left right) (name : bSet B) :
    context ⊓ (name ∈ᴮ left) ≤
      injectsIntoValue (V B) (neighborhood right (downPart relation) name) bSet.omega := by
  apply property_of_label_members context blockLabel left _
    (countable_neighborhood_ext right (downPart relation)) hleft _ name
  intro i
  exact down_neighborhood_label_countable (context ⊓ (blockLabel i ∈ᴮ left)) relation left right
    (inf_le_left.trans hright) (inf_le_left.trans hbefore) i inf_le_right

end Erdos597Object.BooleanOrientedFibres
