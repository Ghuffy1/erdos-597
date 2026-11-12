import Erdos597Object.BooleanUncountability
import Erdos597Object.BooleanPosetModel

set_option backward.isDefEq.respectTransparency false

/-! The countable-neighborhood branch of the Boolean-valued Ramsey argument. -/

namespace Erdos597Object.BooleanLocalGraphs

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanIteration ContextualCCC BooleanInjections

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem countable_of_contextually_injected (hB : Flypitch.BA_CCC B) (context : B)
    (hne : context ≠ ⊥) (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → context ⊓ (label i =ᴮ label j) = ⊥)
    (domain : bSet B) (hmembers : ∀ i, context ≤ label i ∈ᴮ domain)
    (hinjects : context ≤ injectsIntoValue (V B) domain bSet.omega) : Countable I := by
  have hseparate : ∀ i j, i ≠ j → context ⊓ context ⊓ (label i =ᴮ label j) = ⊥ := by
    simpa only [inf_idem] using hdiscrete
  have hcover := cover_of_injected_members label (fun _ => context) domain
    (fun _ => le_rfl) hmembers hseparate hinjects
  have hcount := countable_support_of_cover hB (fun _ : I => context) hcover
  have hall : {i : I | (fun _ : I => context) i ≠ ⊥} = Set.univ :=
    Set.eq_univ_of_forall (fun _ => hne)
  rw [hall] at hcount
  exact Set.countable_univ_iff.mp hcount

noncomputable def neighborName (context : B) (label : I → bSet B) (value : I → I → B)
    (i : I) : bSet B := weightedSet label (fun j => context ⊓ value i j)

noncomputable def possibleGraph (context : B) (value : I → I → B)
    (hsymm : ∀ i j, context ⊓ value i j = context ⊓ value j i) : SimpleGraph I where
  Adj i j := i ≠ j ∧ context ⊓ value i j ≠ ⊥
  symm := ⟨fun i j h => ⟨Ne.symm h.1, fun hz => h.2 ((hsymm i j).trans hz)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem possible_neighbors_countable (hB : Flypitch.BA_CCC B) (context : B)
    (label : I → bSet B) (hdiscrete : ∀ i j, i ≠ j → context ⊓ (label i =ᴮ label j) = ⊥)
    (value : I → I → B) (i : I)
    (hcountable : context ≤ injectsIntoValue (V B) (neighborName context label value i) bSet.omega) :
    {j | context ⊓ value i j ≠ ⊥}.Countable := by
  have hseparate : ∀ j k, j ≠ k →
      (context ⊓ value i j) ⊓ (context ⊓ value i k) ⊓ (label j =ᴮ label k) = ⊥ := by
    intro j k hjk
    exact bot_unique ((le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
      inf_le_right).trans_eq (hdiscrete j k hjk))
  exact countable_support_of_cover hB _
    (cover_of_contextual_injection label (fun j => context ⊓ value i j)
      (fun _ => inf_le_left) hseparate hcountable)

theorem uncountable_independent (hB : Flypitch.BA_CCC B) (context : B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → context ⊓ (label i =ᴮ label j) = ⊥)
    (value : Erdos597.One → Erdos597.One → B)
    (hsymm : ∀ i j, context ⊓ value i j = context ⊓ value j i)
    (hcountable : ∀ i, context ≤ injectsIntoValue (V B) (neighborName context label value i) bSet.omega) :
    ∃ independent : Set Erdos597.One, ¬ independent.Countable ∧
      independent.Pairwise (fun i j => context ⊓ value i j = ⊥) := by
  let graph := possibleGraph context value hsymm
  have hdegree (i : Erdos597.One) : {j | graph.Adj i j}.Countable :=
    (possible_neighbors_countable hB context label hdiscrete value i (hcountable i)).mono
      (fun _ h => h.2)
  obtain ⟨independent, hlarge, hred⟩ := Erdos597.uncountable_independent_of_countable_neighbors graph hdegree
  refine ⟨independent, hlarge, ?_⟩
  intro i hi j hj hij
  by_contra hnonzero
  exact hred hi hj hij ⟨hij, hnonzero⟩

noncomputable def subsetName (context : B) (label : I → bSet B) (indices : Set I) : bSet B :=
  weightedSet (fun i : indices => label i.val) (fun _ => context)

noncomputable def independentValue (domain relation : bSet B) : B :=
  ⨅ x : bSet B, lattice.imp (x ∈ᴮ domain)
    (⨅ y : bSet B, lattice.imp (y ∈ᴮ domain)
      ((x =ᴮ y) ⊔ (edgeValue (V B) relation x y)ᶜ))

theorem subsetName_subset (context : B) (label : I → bSet B) (indices : Set I) :
    context ≤ subsetName context label indices ⊆ᴮ weightedSet label (fun _ => ⊤) := by
  apply bSet.subset_intro
  intro i
  exact le_top.trans (weight_le_member label (fun _ => ⊤) i.val)

theorem subsetName_not_countable (hB : Flypitch.BA_CCC B) (context : B)
    (label : I → bSet B) (hdiscrete : ∀ i j, i ≠ j → context ⊓ (label i =ᴮ label j) = ⊥)
    (indices : Set I) (hlarge : ¬ indices.Countable) :
    context ≤ (injectsIntoValue (V B) (subsetName context label indices) bSet.omega)ᶜ := by
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  by_contra hnonzero
  have hcount : Countable indices := countable_of_contextually_injected hB _ hnonzero
    (fun i : indices => label i.val)
    (fun i j hij => bot_unique ((inf_le_inf_right _ inf_le_left).trans_eq
      (hdiscrete i.val j.val (fun h => hij (Subtype.ext h)))))
    (subsetName context label indices)
    (fun i => inf_le_left.trans (weight_le_member (fun j : indices => label j.val) (fun _ => context) i))
    inf_le_right
  exact hlarge (Set.countable_coe_iff.mp hcount)

theorem subsetName_independent (context : B) (label : I → bSet B) (indices : Set I)
    (relation : bSet B)
    (hnone : indices.Pairwise (fun i j => context ⊓ edgeValue (V B) relation (label i) (label j) = ⊥)) :
    context ≤ independentValue (subsetName context label indices) relation := by
  let body : bSet B → bSet B → B := fun x y => (x =ᴮ y) ⊔ (edgeValue (V B) relation x y)ᶜ
  have hleft (y : bSet B) : bSet.B_ext (fun x => body x y) :=
    bSet.B_ext_sup (bSet.B_ext_eq_left y) (bSet.B_ext_compl (edge_left_ext relation y))
  have hright (x : bSet B) : bSet.B_ext (body x) :=
    bSet.B_ext_sup (bSet.B_ext_eq_right x) (bSet.B_ext_compl (edge_right_ext relation x))
  unfold independentValue subsetName
  rw [BooleanPosetModel.weighted_forall_two _ _ body hleft hright]
  apply le_iInf
  intro i
  apply lattice.bv_imp_intro
  apply le_iInf
  intro j
  apply lattice.bv_imp_intro
  change (context ⊓ context) ⊓ context ≤ (label i.val =ᴮ label j.val) ⊔
    (edgeValue (V B) relation (label i.val) (label j.val))ᶜ
  by_cases hij : i.val = j.val
  · rw [hij]
    exact le_sup_of_le_left bSet.bv_refl
  · have hred : context ≤ (edgeValue (V B) relation (label i.val) (label j.val))ᶜ := by
      rw [le_compl_iff_disjoint_right, disjoint_iff]
      exact hnone i.property j.property hij
    exact ((inf_le_left.trans inf_le_left).trans hred).trans le_sup_right

theorem uncountable_independent_name (hB : Flypitch.BA_CCC B) (context : B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → context ⊓ (label i =ᴮ label j) = ⊥) (relation : bSet B)
    (hsymm : ∀ i j, context ⊓ edgeValue (V B) relation (label i) (label j) =
      context ⊓ edgeValue (V B) relation (label j) (label i))
    (hcountable : ∀ i, context ≤ injectsIntoValue (V B)
      (neighborName context label (fun j k => edgeValue (V B) relation (label j) (label k)) i) bSet.omega) :
    ∃ independent : bSet B,
      context ≤ independent ⊆ᴮ weightedSet label (fun _ => ⊤) ∧
      context ≤ (injectsIntoValue (V B) independent bSet.omega)ᶜ ∧
      context ≤ independentValue independent relation := by
  obtain ⟨indices, hlarge, hnone⟩ := uncountable_independent hB context label hdiscrete
    (fun i j => edgeValue (V B) relation (label i) (label j)) hsymm hcountable
  exact ⟨subsetName context label indices, subsetName_subset context label indices,
    subsetName_not_countable hB context label hdiscrete indices hlarge,
    subsetName_independent context label indices relation hnone⟩

end Erdos597Object.BooleanLocalGraphs
