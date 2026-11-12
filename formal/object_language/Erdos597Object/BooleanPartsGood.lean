import Erdos597Object.BooleanOrientedFibres

set_option backward.isDefEq.respectTransparency false

/-! Simultaneous goodness for the two graph parts implies goodness for the original graph. -/

namespace Erdos597Object.BooleanPartsGood

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets CanonicalDomains BooleanOrientedGraphs BooleanGoodPairs
open BooleanRectangles BooleanUncountableRamsey
open BooleanFiniteGraphs BooleanInjections

variable {B : Type} [CompleteBooleanAlgebra B]

theorem parts_cover (context : B) (relation x y : bSet B)
    (hx : context ≤ x ∈ᴮ blockDomain) (hy : context ≤ y ∈ᴮ blockDomain) :
    context ⊓ edgeValue (V B) relation x y ≤
      edgeValue (V B) (upPart relation) x y ⊔ edgeValue (V B) (downPart relation) x y := by
  let body := fun x y : bSet B => lattice.imp (edgeValue (V B) relation x y)
    (edgeValue (V B) (upPart relation) x y ⊔ edgeValue (V B) (downPart relation) x y)
  have hleft (y : bSet B) : bSet.B_ext (fun x => body x y) :=
    bSet.B_ext_imp (edge_left_ext relation y)
      (bSet.B_ext_sup (edge_left_ext (upPart relation) y) (edge_left_ext (downPart relation) y))
  have hright (x : bSet B) : bSet.B_ext (body x) :=
    bSet.B_ext_imp (edge_right_ext relation x)
      (bSet.B_ext_sup (edge_right_ext (upPart relation) x) (edge_right_ext (downPart relation) x))
  have hall : (⊤ : B) ≤ ⨅ x : bSet B, lattice.imp (x ∈ᴮ blockDomain)
      (⨅ y : bSet B, lattice.imp (y ∈ᴮ blockDomain) (body x y)) := by
    change (⊤ : B) ≤ ⨅ x : bSet B, lattice.imp (x ∈ᴮ weightedSet blockLabel (fun _ => ⊤))
      (⨅ y : bSet B, lattice.imp (y ∈ᴮ weightedSet blockLabel (fun _ => ⊤)) (body x y))
    rw [BooleanPosetModel.weighted_forall_two blockLabel (fun _ => ⊤) body hleft hright]
    simp only [lattice.imp, compl_top, bot_sup_eq]
    apply le_iInf
    intro i
    apply le_iInf
    intro j
    change (⊤ : B) ≤ lattice.imp _ _
    apply lattice.bv_imp_intro
    rw [parts_cover_labels]
    exact inf_le_right
  have hfirst := lattice.bv_context_apply ((le_top.trans hall).trans (iInf_le _ x)) hx
  have hsecond := lattice.bv_context_apply (hfirst.trans (iInf_le _ y)) hy
  exact lattice.le_imp_iff.mp hsecond

theorem emptyRectangle_of_parts (context : B) (relation left right : bSet B)
    (hleft : context ≤ left ⊆ᴮ blockDomain) (hright : context ≤ right ⊆ᴮ blockDomain)
    (hup : context ≤ emptyRectangle (upPart relation) left right)
    (hdown : context ≤ emptyRectangle (downPart relation) left right) :
    context ≤ emptyRectangle relation left right := by
  rw [emptyRectangle_spec]
  apply le_iInf
  intro x
  apply lattice.bv_imp_intro
  apply le_iInf
  intro y
  apply lattice.bv_imp_intro
  let part : B := (context ⊓ (x ∈ᴮ left)) ⊓ (y ∈ᴮ right)
  have hx : part ≤ x ∈ᴮ left := inf_le_left.trans inf_le_right
  have hy : part ≤ y ∈ᴮ right := inf_le_right
  have hcontext : part ≤ context := inf_le_left.trans inf_le_left
  have hcover := parts_cover part relation x y
    (bSet.mem_of_mem_subset' (hcontext.trans hleft) hx)
    (bSet.mem_of_mem_subset' (hcontext.trans hright) hy)
  have hup' := emptyRectangle_no_edge part (upPart relation) left right x y (hcontext.trans hup) hx hy
  have hdown' := emptyRectangle_no_edge part (downPart relation) left right x y (hcontext.trans hdown) hx hy
  apply le_compl_iff_disjoint_right.mpr
  rw [disjoint_iff]
  apply bot_unique
  have hsmall : part ⊓ edgeValue (V B) relation x y ≤
      (edgeValue (V B) (upPart relation) x y ⊔ edgeValue (V B) (downPart relation) x y) ⊓
        (edgeValue (V B) (upPart relation) x y ⊔ edgeValue (V B) (downPart relation) x y)ᶜ :=
    le_inf hcover (inf_le_left.trans (by
      rw [compl_sup]
      exact le_inf hup' hdown'))
  exact hsmall.trans_eq inf_compl_eq_bot

theorem goodPair_of_parts (context : B) (relation left right : bSet B)
    (hleft : context ≤ left ⊆ᴮ blockDomain) (hright : context ≤ right ⊆ᴮ blockDomain)
    (hup : context ≤ goodPair (upPart relation) left right)
    (hdown : context ≤ goodPair (downPart relation) left right) :
    context ≤ goodPair relation left right := by
  apply le_iInf
  intro testLeft
  apply lattice.bv_imp_intro
  apply le_iInf
  intro testRight
  apply lattice.bv_imp_intro
  let part : B := (context ⊓ largeSubset left testLeft) ⊓ largeSubset right testRight
  have hcontext : part ≤ context := inf_le_left.trans inf_le_left
  have htestLeft : part ≤ largeSubset left testLeft := inf_le_left.trans inf_le_right
  have htestRight : part ≤ largeSubset right testRight := inf_le_right
  obtain ⟨firstLeft, firstRight, hfirstLeft, hfirstRight, hnoUp⟩ :=
    goodPair_refine part (upPart relation) left right testLeft testRight
      (hcontext.trans hup) htestLeft htestRight
  obtain ⟨lastLeft, lastRight, hlastLeft, hlastRight, hnoDown⟩ :=
    goodPair_refine part (downPart relation) left right firstLeft firstRight
      (hcontext.trans hdown) (largeSubset_trans part left testLeft firstLeft htestLeft hfirstLeft)
      (largeSubset_trans part right testRight firstRight htestRight hfirstRight)
  have hlastTestLeft := largeSubset_trans part testLeft firstLeft lastLeft hfirstLeft hlastLeft
  have hlastTestRight := largeSubset_trans part testRight firstRight lastRight hfirstRight hlastRight
  have hlastBlockLeft : part ≤ lastLeft ⊆ᴮ blockDomain :=
    subset_trans (hlastTestLeft.trans inf_le_left)
      (subset_trans (htestLeft.trans inf_le_left) (hcontext.trans hleft))
  have hlastBlockRight : part ≤ lastRight ⊆ᴮ blockDomain :=
    subset_trans (hlastTestRight.trans inf_le_left)
      (subset_trans (htestRight.trans inf_le_left) (hcontext.trans hright))
  apply le_iSup_of_le lastLeft
  apply le_inf hlastTestLeft
  apply le_iSup_of_le lastRight
  apply le_inf hlastTestRight
  exact emptyRectangle_of_parts part relation lastLeft lastRight hlastBlockLeft hlastBlockRight
    ((le_inf le_rfl hnoUp).trans (emptyRectangle_mono part (upPart relation) lastLeft lastRight
      firstLeft firstRight (hlastLeft.trans inf_le_left) (hlastRight.trans inf_le_left))) hnoDown

end Erdos597Object.BooleanPartsGood
