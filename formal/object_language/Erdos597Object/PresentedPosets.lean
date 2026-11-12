import Erdos597Object.BooleanInjections
import Erdos597Object.BooleanPosetModel

set_option backward.isDefEq.respectTransparency false

/-! Presenting a small poset name by Boolean coefficients below a given context. -/

namespace Erdos597Object.PresentedPosets

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem nonempty_ext : bSet.B_ext (fun x : bSet B => nonemptyValue (V B) x) := by
  change bSet.B_ext (fun x : bSet B => ⨆ y : bSet B, y ∈ᴮ x)
  exact bSet.B_ext_iSup fun y => bSet.B_ext_mem_right y

theorem weighted_nonempty (element : I → bSet B) (weight : I → B) :
    nonemptyValue (V B) (weightedSet element weight) = ⨆ i, weight i := by
  have h := weighted_bounded_exists element weight (fun _ => ⊤) bSet.B_ext_top
  simpa only [inf_top_eq] using! h

theorem reflexive_at {context : B} (domain relation x : bSet B)
    (horder : context ≤ partialOrderValue (V B) domain relation)
    (hx : context ≤ x ∈ᴮ domain) : context ≤ edgeValue (V B) relation x x := by
  have h : context ≤ lattice.imp (x ∈ᴮ domain) (edgeValue (V B) relation x x) :=
    horder.trans (inf_le_right.trans (inf_le_left.trans (iInf_le _ x)))
  exact lattice.bv_context_apply h hx

theorem antisymmetric_at {context : B} (domain relation x y : bSet B)
    (horder : context ≤ partialOrderValue (V B) domain relation)
    (hx : context ≤ x ∈ᴮ domain) (hy : context ≤ y ∈ᴮ domain)
    (hxy : context ≤ edgeValue (V B) relation x y)
    (hyx : context ≤ edgeValue (V B) relation y x) : context ≤ x =ᴮ y := by
  have h : context ≤ lattice.imp (x ∈ᴮ domain)
      (⨅ y : bSet B, lattice.imp (y ∈ᴮ domain)
        (lattice.imp (edgeValue (V B) relation x y ⊓ edgeValue (V B) relation y x) (x =ᴮ y))) := by
    have hpart := horder.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
    simpa only [memberValue_bSet, eqValue_bSet, lattice.imp, sup_assoc] using!
      hpart.trans (iInf_le _ x)
  have hfirst := lattice.bv_context_apply h hx
  have hsecond := lattice.bv_context_apply (hfirst.trans (iInf_le _ y)) hy
  exact lattice.bv_context_apply hsecond (le_inf hxy hyx)

theorem transitive_at {context : B} (domain relation x y z : bSet B)
    (horder : context ≤ partialOrderValue (V B) domain relation)
    (hx : context ≤ x ∈ᴮ domain) (hy : context ≤ y ∈ᴮ domain) (hz : context ≤ z ∈ᴮ domain)
    (hxy : context ≤ edgeValue (V B) relation x y)
    (hyz : context ≤ edgeValue (V B) relation y z) :
    context ≤ edgeValue (V B) relation x z := by
  have h : context ≤ lattice.imp (x ∈ᴮ domain)
      (⨅ y : bSet B, lattice.imp (y ∈ᴮ domain)
        (⨅ z : bSet B, lattice.imp (z ∈ᴮ domain)
          (lattice.imp (edgeValue (V B) relation x y ⊓ edgeValue (V B) relation y z)
            (edgeValue (V B) relation x z)))) := by
    have hpart := horder.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
    simpa only [memberValue_bSet, eqValue_bSet, lattice.imp, sup_assoc] using!
      hpart.trans (iInf_le _ x)
  have hfirst := lattice.bv_context_apply h hx
  have hsecond := lattice.bv_context_apply (hfirst.trans (iInf_le _ y)) hy
  have hthird := lattice.bv_context_apply (hsecond.trans (iInf_le _ z)) hz
  exact lattice.bv_context_apply hthird (le_inf hxy hyz)

def ofNames (context : B) (domain relation : bSet B) (element : I → bSet B) (weight : I → B)
    (hvalid : ∀ i, weight i ≤ context ∧ weight i ≤ element i ∈ᴮ domain)
    (hseparate : ∀ i j, i ≠ j → weight i ⊓ weight j ⊓ (element i =ᴮ element j) = ⊥)
    (horder : context ≤ partialOrderValue (V B) domain relation) : BooleanIteration.BooleanPoset B I where
  member := weight
  leValue i j := weight i ⊓ weight j ⊓ edgeValue (V B) relation (element i) (element j)
  le_members _ _ := inf_le_left
  reflexive i :=
    le_inf (le_inf le_rfl le_rfl)
      (reflexive_at domain relation (element i) ((hvalid i).1.trans horder) (hvalid i).2)
  transitive i j k := by
    let part := (weight i ⊓ weight j ⊓ edgeValue (V B) relation (element i) (element j)) ⊓
      (weight j ⊓ weight k ⊓ edgeValue (V B) relation (element j) (element k))
    have hi : part ≤ weight i := inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hj : part ≤ weight j := inf_le_left.trans (inf_le_left.trans inf_le_right)
    have hk : part ≤ weight k := inf_le_right.trans (inf_le_left.trans inf_le_right)
    have hxy : part ≤ edgeValue (V B) relation (element i) (element j) :=
      inf_le_left.trans inf_le_right
    have hyz : part ≤ edgeValue (V B) relation (element j) (element k) :=
      inf_le_right.trans inf_le_right
    exact le_inf (le_inf hi hk)
      (transitive_at domain relation (element i) (element j) (element k)
        ((hi.trans (hvalid i).1).trans horder) (hi.trans (hvalid i).2)
        (hj.trans (hvalid j).2) (hk.trans (hvalid k).2) hxy hyz)
  antisymmetric i j hij := by
    let part := (weight i ⊓ weight j ⊓ edgeValue (V B) relation (element i) (element j)) ⊓
      (weight j ⊓ weight i ⊓ edgeValue (V B) relation (element j) (element i))
    have hi : part ≤ weight i := inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hj : part ≤ weight j := inf_le_left.trans (inf_le_left.trans inf_le_right)
    have hxy : part ≤ edgeValue (V B) relation (element i) (element j) :=
      inf_le_left.trans inf_le_right
    have hyx : part ≤ edgeValue (V B) relation (element j) (element i) :=
      inf_le_right.trans inf_le_right
    have heq := antisymmetric_at domain relation (element i) (element j)
      ((hi.trans (hvalid i).1).trans horder) (hi.trans (hvalid i).2) (hj.trans (hvalid j).2) hxy hyx
    exact bot_unique ((le_inf (le_inf hi hj) heq).trans_eq (hseparate i j hij))

theorem poset_presentation {context : B} (domain relation : bSet B) (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (hinjects : context ≤ injectsIntoValue (V B) domain (weightedSet label (fun _ => ⊤)))
    (horder : context ≤ partialOrderValue (V B) domain relation)
    (hnonempty : context ≤ nonemptyValue (V B) domain) :
    ∃ (element : I → bSet B) (P : BooleanIteration.BooleanPoset B I),
      (⨆ i, P.member i) = context ∧
      (∀ i, P.member i ≤ context ∧ P.member i ≤ element i ∈ᴮ domain) ∧
      (∀ i j, i ≠ j → P.member i ⊓ P.member j ⊓ (element i =ᴮ element j) = ⊥) ∧
      context ≤ domain =ᴮ weightedSet element P.member ∧
      ∀ i j, P.leValue i j = P.member i ⊓ P.member j ⊓
        edgeValue (V B) relation (element i) (element j) := by
  obtain ⟨element, weight, hvalid, hseparate, heq⟩ :=
    presentation_of_injection domain label hdiscrete hinjects
  let P := ofNames context domain relation element weight hvalid hseparate horder
  refine ⟨element, P, ?_, hvalid, hseparate, heq, fun _ _ => rfl⟩
  apply le_antisymm (iSup_le fun i => (hvalid i).1)
  have h := (le_inf heq hnonempty).trans (nonempty_ext domain (weightedSet element weight))
  change context ≤ nonemptyValue (V B) (weightedSet element weight) at h
  rw [weighted_nonempty] at h
  exact h

end Erdos597Object.PresentedPosets
