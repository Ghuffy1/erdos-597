import Erdos597Object.BooleanPosetCoding

set_option backward.isDefEq.respectTransparency false

/-! A small Boolean-valued set presentation obtained from an injection into fixed labels. -/

namespace Erdos597Object.BooleanInjections

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem edge_left_ext (relation z : bSet B) :
    bSet.B_ext (fun x => edgeValue (V B) relation x z) := by
  change bSet.B_ext (fun x => bSet.pair x z ∈ᴮ relation)
  exact bSet.B_ext_pair_mem_left

theorem edge_right_ext (relation x : bSet B) :
    bSet.B_ext (fun z => edgeValue (V B) relation x z) := by
  change bSet.B_ext (fun z => bSet.pair x z ∈ᴮ relation)
  exact bSet.B_ext_pair_mem_right

theorem totalAt_labels {context : B} (domain relation : bSet B) (label : I → bSet B)
    (hfunction : context ≤ functionFromValue (V B) domain
      (weightedSet label (fun _ => ⊤)) relation) (x : bSet B) :
    context ⊓ (x ∈ᴮ domain) ≤ ⨆ i, edgeValue (V B) relation x (label i) := by
  have htotal : context ≤ totalOnValue (V B) domain (weightedSet label (fun _ => ⊤)) relation :=
    hfunction.trans (inf_le_right.trans inf_le_right)
  have himp := htotal.trans (iInf_le _ x)
  have houtput := lattice.le_imp_iff.mp himp
  change context ⊓ (x ∈ᴮ domain) ≤
    ⨆ y : bSet B, (y ∈ᴮ weightedSet label (fun _ => ⊤)) ⊓ edgeValue (V B) relation x y at houtput
  rw [weighted_bounded_exists label (fun _ => ⊤) _ (edge_right_ext relation x)] at houtput
  simpa only [top_inf_eq] using houtput

theorem injective_outputs {context : B} (relation : bSet B)
    (hinjective : context ≤ injectiveValue (V B) relation) (x y z : bSet B) :
    context ⊓ (edgeValue (V B) relation x z ⊓ edgeValue (V B) relation y z) ≤ x =ᴮ y := by
  have himp : context ≤ lattice.imp
      (edgeValue (V B) relation x z ⊓ edgeValue (V B) relation y z) (x =ᴮ y) :=
    hinjective.trans ((iInf_le _ x).trans ((iInf_le _ y).trans (iInf_le _ z)))
  exact lattice.le_imp_iff.mp himp

theorem singleValued_outputs {context : B} (relation : bSet B)
    (hsingle : context ≤ singleValuedValue (V B) relation) (x y z : bSet B) :
    context ⊓ (edgeValue (V B) relation x y ⊓ edgeValue (V B) relation x z) ≤ y =ᴮ z := by
  have himp : context ≤ lattice.imp
      (edgeValue (V B) relation x y ⊓ edgeValue (V B) relation x z) (y =ᴮ z) :=
    hsingle.trans ((iInf_le _ x).trans ((iInf_le _ y).trans (iInf_le _ z)))
  exact lattice.le_imp_iff.mp himp

noncomputable def fiberWeight (context : B) (domain relation : bSet B)
    (label : I → bSet B) (i : I) : B :=
  context ⊓ ⨆ x : bSet B, (x ∈ᴮ domain) ⊓ edgeValue (V B) relation x (label i)

theorem exists_fiberElement (context : B) (domain relation : bSet B)
    (label : I → bSet B) (i : I) :
    ∃ x : bSet B, fiberWeight context domain relation label i ≤
      (x ∈ᴮ domain) ⊓ edgeValue (V B) relation x (label i) :=
  bSet.exists_convert inf_le_right
    (bSet.B_ext_inf (bSet.B_ext_mem_left domain) (edge_left_ext relation (label i)))

noncomputable def fiberElement (context : B) (domain relation : bSet B)
    (label : I → bSet B) (i : I) : bSet B :=
  Classical.choose (exists_fiberElement context domain relation label i)

theorem fiberElement_spec (context : B) (domain relation : bSet B)
    (label : I → bSet B) (i : I) :
    fiberWeight context domain relation label i ≤
      (fiberElement context domain relation label i ∈ᴮ domain) ⊓
        edgeValue (V B) relation (fiberElement context domain relation label i) (label i) :=
  Classical.choose_spec (exists_fiberElement context domain relation label i)

theorem fibers_separated {context : B} (domain relation : bSet B) (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (hsingle : context ≤ singleValuedValue (V B) relation) :
    ∀ i j, i ≠ j → fiberWeight context domain relation label i ⊓
      fiberWeight context domain relation label j ⊓
        (fiberElement context domain relation label i =ᴮ fiberElement context domain relation label j) = ⊥ := by
  intro i j hij
  let part := fiberWeight context domain relation label i ⊓
    fiberWeight context domain relation label j ⊓
      (fiberElement context domain relation label i =ᴮ fiberElement context domain relation label j)
  have hcontext : part ≤ context := (inf_le_left.trans inf_le_left).trans inf_le_left
  have hi := (inf_le_left.trans inf_le_left : part ≤ fiberWeight context domain relation label i).trans
    ((fiberElement_spec context domain relation label i).trans inf_le_right)
  have hj := (inf_le_left.trans inf_le_right : part ≤ fiberWeight context domain relation label j).trans
    ((fiberElement_spec context domain relation label j).trans inf_le_right)
  have htransfer : part ≤ edgeValue (V B) relation
      (fiberElement context domain relation label j) (label i) :=
    (le_inf inf_le_right hi).trans (edge_left_ext relation (label i) _ _)
  have heq := (le_inf hcontext (le_inf htransfer hj)).trans
    (singleValued_outputs relation hsingle _ _ _)
  exact bot_unique (heq.trans_eq (hdiscrete i j hij))

theorem fibers_cover {context : B} (domain relation : bSet B) (label : I → bSet B)
    (hfunction : context ≤ functionFromValue (V B) domain
      (weightedSet label (fun _ => ⊤)) relation)
    (hinjective : context ≤ injectiveValue (V B) relation) (x : bSet B) :
    context ⊓ (x ∈ᴮ domain) ≤ x ∈ᴮ weightedSet
      (fiberElement context domain relation label) (fiberWeight context domain relation label) := by
  let element := fiberElement context domain relation label
  let weight := fiberWeight context domain relation label
  have htotal := totalAt_labels domain relation label hfunction x
  have hpart (i : I) : context ⊓ (x ∈ᴮ domain) ⊓ edgeValue (V B) relation x (label i) ≤
      x ∈ᴮ weightedSet element weight := by
    let part := context ⊓ (x ∈ᴮ domain) ⊓ edgeValue (V B) relation x (label i)
    have hweight : part ≤ weight i :=
      le_inf (inf_le_left.trans inf_le_left)
        (le_iSup_of_le x (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
    have hedge : part ≤ edgeValue (V B) relation (element i) (label i) :=
      hweight.trans ((fiberElement_spec context domain relation label i).trans inf_le_right)
    have heq : part ≤ x =ᴮ element i :=
      (le_inf (inf_le_left.trans inf_le_left) (le_inf inf_le_right hedge)).trans
        (injective_outputs relation hinjective _ _ _)
    exact (le_inf hweight heq).trans (le_iSup (fun i => weight i ⊓ (x =ᴮ element i)) i)
  calc
    context ⊓ (x ∈ᴮ domain) = (context ⊓ (x ∈ᴮ domain)) ⊓
        (⨆ i, edgeValue (V B) relation x (label i)) := (inf_eq_left.mpr htotal).symm
    _ = ⨆ i, context ⊓ (x ∈ᴮ domain) ⊓ edgeValue (V B) relation x (label i) := inf_iSup_eq _ _
    _ ≤ _ := iSup_le hpart

theorem presentation_of_injection {context : B} (domain : bSet B) (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (hinjects : context ≤ injectsIntoValue (V B) domain (weightedSet label (fun _ => ⊤))) :
    ∃ (element : I → bSet B) (weight : I → B),
      (∀ i, weight i ≤ context ∧ weight i ≤ element i ∈ᴮ domain) ∧
      (∀ i j, i ≠ j → weight i ⊓ weight j ⊓ (element i =ᴮ element j) = ⊥) ∧
      context ≤ domain =ᴮ weightedSet element weight := by
  obtain ⟨relation, hfunction, hinjective⟩ := injectsInto_witness domain
    (weightedSet label (fun _ => ⊤)) hinjects
  let element := fiberElement context domain relation label
  let weight := fiberWeight context domain relation label
  have hmember (i : I) : weight i ≤ element i ∈ᴮ domain :=
    (fiberElement_spec context domain relation label i).trans inf_le_left
  refine ⟨element, weight, (fun i => ⟨inf_le_left, hmember i⟩), ?_, ?_⟩
  · exact fibers_separated domain relation label hdiscrete
      (hfunction.trans (inf_le_right.trans inf_le_left))
  · apply bSet.subset_ext
    · apply bSet.subset_unfold'.mpr
      apply le_iInf
      intro x
      exact lattice.le_imp_iff.mpr (fibers_cover domain relation label hfunction hinjective x)
    · apply bSet.subset_intro
      intro i
      exact inf_le_right.trans (hmember i)

end Erdos597Object.BooleanInjections
