import Erdos597Object.BooleanOrderedSubsets

set_option backward.isDefEq.respectTransparency false

/-! Order reflection, strict block order, and edge avoidance for indexed map names. -/

namespace Erdos597Object.BooleanOrderMaps

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanGraphMaps BooleanBlockOrder BooleanColumns CanonicalDomains

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem map_edge_swap (input output : I → bSet B) (x y : bSet B) :
    edgeValue (V B) (mapName input output) x y =
      edgeValue (V B) (mapName output input) y x := by
  simp only [map_edge, inf_comm]

theorem map_respects (context : B) (input output : I → bSet B) (source target : bSet B)
    (hforward : ∀ i j, context ⊓ edgeValue (V B) source (input i) (input j) ≤
      edgeValue (V B) target (output i) (output j))
    (hreverse : ∀ i j, context ⊓ edgeValue (V B) target (output i) (output j) ≤
      edgeValue (V B) source (input i) (input j)) :
    context ≤ respectsOrderValue (V B) source target (mapName input output) := by
  have hfirst := map_preserves context input output source target hforward
  have hsecond := map_preserves context output input target source hreverse
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  apply le_iInf
  intro a
  apply le_iInf
  intro b
  apply lattice.bv_imp_intro
  have hleft := lattice.bv_context_apply
    ((inf_le_left.trans hfirst).trans ((iInf_le _ x).trans ((iInf_le _ y).trans
      ((iInf_le _ a).trans (iInf_le _ b))))) inf_le_right
  have hinverse : context ⊓ (edgeValue (V B) (mapName input output) x a ⊓
      edgeValue (V B) (mapName input output) y b) ≤
        edgeValue (V B) (mapName output input) a x ⊓
          edgeValue (V B) (mapName output input) b y := by
    simpa only [map_edge_swap input output] using
      (inf_le_right : context ⊓ (edgeValue (V B) (mapName input output) x a ⊓
        edgeValue (V B) (mapName input output) y b) ≤ _)
  have hright := lattice.bv_context_apply
    ((inf_le_left.trans hsecond).trans ((iInf_le _ a).trans ((iInf_le _ b).trans
      ((iInf_le _ x).trans (iInf_le _ y))))) hinverse
  exact le_inf hleft hright

theorem map_avoids (context : B) (input output : I → bSet B) (blue : bSet B)
    (hred : ∀ i j, i ≠ j → context ≤ (edgeValue (V B) blue (output i) (output j))ᶜ) :
    context ≤ avoidsEdgesValue (V B) blue (mapName input output) := by
  classical
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  apply le_iInf
  intro a
  apply le_iInf
  intro b
  apply lattice.bv_imp_intro
  apply map_pair_cases input output _ _ x a y b
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
  intro i j
  let part := ((context ⊓ (edgeValue (V B) (mapName input output) x a ⊓
    edgeValue (V B) (mapName input output) y b)) ⊓ ((x =ᴮ input i) ⊓ (a =ᴮ output i))) ⊓
      ((y =ᴮ input j) ⊓ (b =ᴮ output j))
  have hcontext : part ≤ context := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hx : part ≤ x =ᴮ input i := inf_le_left.trans (inf_le_right.trans inf_le_left)
  have ha : part ≤ a =ᴮ output i := inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hy : part ≤ y =ᴮ input j := inf_le_right.trans inf_le_left
  have hb : part ≤ b =ᴮ output j := inf_le_right.trans inf_le_right
  by_cases hij : i = j
  · subst j
    exact le_sup_of_le_left (bSet.bv_trans hx (bSet.bv_symm hy))
  · apply le_sup_of_le_right
    have hfirst : part ≤ (edgeValue (V B) blue a (output j))ᶜ :=
      (le_inf (bSet.bv_symm ha) (hcontext.trans (hred i j hij))).trans
        (bSet.B_ext_compl (BooleanInjections.edge_left_ext blue (output j)) (output i) a)
    exact (le_inf (bSet.bv_symm hb) hfirst).trans
      (bSet.B_ext_compl (BooleanInjections.edge_right_ext blue a) (output j) b)

theorem blockOrder_no_two_way (context : B) (x y : bSet B)
    (hx : context ≤ x ∈ᴮ blockDomain) (hy : context ≤ y ∈ᴮ blockDomain) :
    (context ⊓ edgeValue (V B) blockOrder x y) ⊓ edgeValue (V B) blockOrder y x = ⊥ := by
  classical
  let part := (context ⊓ edgeValue (V B) blockOrder x y) ⊓ edgeValue (V B) blockOrder y x
  have hpart : part ≤ context := inf_le_left.trans inf_le_left
  have hleft : part ≤ ⨆ i, x =ᴮ blockLabel i := by
    have h := hpart.trans hx
    change part ≤ x ∈ᴮ weightedSet blockLabel (fun _ => ⊤) at h
    simpa only [member_weightedSet, top_inf_eq] using h
  have hright : part ≤ ⨆ i, y =ᴮ blockLabel i := by
    have h := hpart.trans hy
    change part ≤ y ∈ᴮ weightedSet blockLabel (fun _ => ⊤) at h
    simpa only [member_weightedSet, top_inf_eq] using h
  apply bot_unique
  apply (le_inf le_rfl hleft).trans
  apply lattice.bv_cases_right
  intro i
  apply (le_inf le_rfl (inf_le_left.trans hright)).trans
  apply lattice.bv_cases_right
  intro j
  let joint := (part ⊓ (x =ᴮ blockLabel i)) ⊓ (y =ᴮ blockLabel j)
  have hxyOriginal : joint ≤ edgeValue (V B) blockOrder x y :=
    (inf_le_left.trans inf_le_left).trans (inf_le_left.trans inf_le_right)
  have hyxOriginal : joint ≤ edgeValue (V B) blockOrder y x :=
    (inf_le_left.trans inf_le_left).trans inf_le_right
  have hxEqual : joint ≤ x =ᴮ blockLabel i := inf_le_left.trans inf_le_right
  have hyEqual : joint ≤ y =ᴮ blockLabel j := inf_le_right
  have hxy : joint ≤ edgeValue (V B) blockOrder (blockLabel i) (blockLabel j) := by
    change joint ≤ bSet.pair (blockLabel i) (blockLabel j) ∈ᴮ blockOrder
    exact bSet.subst_congr_mem_left' (bSet.pair_congr hxEqual hyEqual) hxyOriginal
  have hyx : joint ≤ edgeValue (V B) blockOrder (blockLabel j) (blockLabel i) := by
    change joint ≤ bSet.pair (blockLabel j) (blockLabel i) ∈ᴮ blockOrder
    exact bSet.subst_congr_mem_left' (bSet.pair_congr hyEqual hxEqual) hyxOriginal
  by_cases hij : keyLess i j
  · exact hyx.trans_eq (by simp only [blockOrder_edge, ite_eq_right (keyLess_asymm hij)])
  · exact hxy.trans_eq (by simp only [blockOrder_edge, ite_eq_right hij])

theorem blockOrder_reverse_false (context : B) (x y : bSet B)
    (hx : context ≤ x ∈ᴮ blockDomain) (hy : context ≤ y ∈ᴮ blockDomain)
    (hxy : context ≤ edgeValue (V B) blockOrder x y) :
    context ≤ (edgeValue (V B) blockOrder y x)ᶜ := by
  apply (le_compl_iff_disjoint_right).mpr
  apply disjoint_iff.mpr
  exact bot_unique ((le_inf (le_inf inf_le_left (inf_le_left.trans hxy)) inf_le_right).trans_eq
    (blockOrder_no_two_way context x y hx hy))

theorem blockOrder_no_loop (context : B) (x : bSet B) (hx : context ≤ x ∈ᴮ blockDomain) :
    context ≤ (edgeValue (V B) blockOrder x x)ᶜ := by
  apply (le_compl_iff_disjoint_right).mpr
  apply disjoint_iff.mpr
  simpa only [inf_assoc, inf_idem] using blockOrder_no_two_way context x x hx hx

theorem keyLess_trichotomy (i j : ℕ × ScheduledIteration.Labels) :
    keyLess i j ∨ i = j ∨ keyLess j i := by
  rcases lt_trichotomy i.1 j.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy (column i.2) (column j.2) with hcol | hcol | hcol
    · exact Or.inl (Or.inr ⟨h, hcol⟩)
    · exact Or.inr (Or.inl (Prod.ext h (column_injective hcol)))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, hcol⟩))
  · exact Or.inr (Or.inr (Or.inl h))

end Erdos597Object.BooleanOrderMaps
