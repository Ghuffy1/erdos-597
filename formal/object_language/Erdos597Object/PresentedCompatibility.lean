import Erdos597Object.PresentedPosets

set_option backward.isDefEq.respectTransparency false

/-! Compatibility of conditions in a weighted presentation agrees below its member weights. -/

namespace Erdos597Object.PresentedCompatibility

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanAntichains PresentedPosets

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem context_predicate_congr {context : B} {x y : bSet B}
    (heq : context ≤ x =ᴮ y) (predicate : bSet B → B) (hext : bSet.B_ext predicate) :
    context ⊓ predicate x = context ⊓ predicate y := by
  apply le_antisymm
  · exact le_inf inf_le_left ((le_inf (inf_le_left.trans heq) inf_le_right).trans (hext x y))
  · exact le_inf inf_le_left
      ((le_inf (inf_le_left.trans (bSet.bv_symm heq)) inf_le_right).trans (hext y x))

theorem compatibility_domain_ext (relation x y : bSet B) :
    bSet.B_ext (fun domain => Erdos597Object.compatibleValue (V B) domain relation x y) := by
  change bSet.B_ext (fun domain => ⨆ z : bSet B,
    (z ∈ᴮ domain) ⊓ (edgeValue (V B) relation z x ⊓ edgeValue (V B) relation z y))
  exact bSet.B_ext_iSup fun z => bSet.B_ext_inf (bSet.B_ext_mem_right z) (bSet.B_ext_const _)

theorem weighted_compatibility (element : I → bSet B) (weight : I → B)
    (relation x y : bSet B) :
    Erdos597Object.compatibleValue (V B) (weightedSet element weight) relation x y =
      ⨆ i, weight i ⊓ (edgeValue (V B) relation (element i) x ⊓
        edgeValue (V B) relation (element i) y) := by
  change (⨆ z : bSet B, (z ∈ᴮ weightedSet element weight) ⊓
    (edgeValue (V B) relation z x ⊓ edgeValue (V B) relation z y)) = _
  exact weighted_bounded_exists element weight _ (compatibleWitness_ext relation x y)

theorem ofNames_compatibility (context : B) (domain relation : bSet B)
    (element : I → bSet B) (weight : I → B)
    (hvalid : ∀ i, weight i ≤ context ∧ weight i ≤ element i ∈ᴮ domain)
    (hseparate : ∀ i j, i ≠ j → weight i ⊓ weight j ⊓ (element i =ᴮ element j) = ⊥)
    (horder : context ≤ partialOrderValue (V B) domain relation) (i j : I) :
    BooleanIteration.compatibleValue (ofNames context domain relation element weight hvalid hseparate horder) i j =
      weight i ⊓ weight j ⊓ (⨆ k, weight k ⊓
        (edgeValue (V B) relation (element k) (element i) ⊓
          edgeValue (V B) relation (element k) (element j))) := by
  simp only [BooleanIteration.compatibleValue, ofNames, inf_iSup_eq]
  apply iSup_congr
  intro k
  simp only [inf_assoc, inf_left_comm, inf_comm, inf_left_idem]

theorem compatibility_below_weights (context : B) (domain relation : bSet B)
    (element : I → bSet B) (weight : I → B)
    (hvalid : ∀ i, weight i ≤ context ∧ weight i ≤ element i ∈ᴮ domain)
    (hseparate : ∀ i j, i ≠ j → weight i ⊓ weight j ⊓ (element i =ᴮ element j) = ⊥)
    (horder : context ≤ partialOrderValue (V B) domain relation)
    (heq : context ≤ domain =ᴮ weightedSet element weight) (i j : I) :
    weight i ⊓ weight j ⊓
        Erdos597Object.compatibleValue (V B) domain relation (element i) (element j) =
      BooleanIteration.compatibleValue (ofNames context domain relation element weight hvalid hseparate horder) i j := by
  calc
    _ = weight i ⊓ weight j ⊓ Erdos597Object.compatibleValue (V B)
        (weightedSet element weight) relation (element i) (element j) :=
      context_predicate_congr ((inf_le_left.trans (hvalid i).1).trans heq) _
        (compatibility_domain_ext relation (element i) (element j))
    _ = _ := by
      rw [weighted_compatibility]
      exact (ofNames_compatibility context domain relation element weight hvalid hseparate horder i j).symm

end Erdos597Object.PresentedCompatibility
