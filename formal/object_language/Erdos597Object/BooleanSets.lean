import Erdos597Object.BooleanIterationCCC
import Erdos597Object.MartinSemantics

set_option backward.isDefEq.respectTransparency false

/-! Weighted set names and the interpretation of the function predicates. -/

namespace Erdos597Object.BooleanSets

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open scoped Flypitch.bSet

variable {B : Type} [CompleteBooleanAlgebra B]

@[simp] theorem memberValue_bSet (x y : bSet B) :
    memberValue (V B) x y = x ∈ᴮ y := rfl

@[simp] theorem pairValue_bSet (x y : bSet B) :
    pairValue (V B) x y = bSet.pair x y := rfl

@[simp] theorem edgeValue_bSet (relation x y : bSet B) :
    edgeValue (V B) relation x y = bSet.pair x y ∈ᴮ relation := rfl

@[simp] theorem eqValue_bSet (x y : bSet B) : (V B).eq x y = x =ᴮ y := rfl

theorem subsetValue_bSet (x y : bSet B) : subsetValue (V B) x y = x ⊆ᴮ y := by
  change (⨅ z : bSet B, lattice.imp (z ∈ᴮ x) (z ∈ᴮ y)) = x ⊆ᴮ y
  rw [← bSet.bounded_forall x (fun z => z ∈ᴮ y) (bSet.B_ext_mem_left y)]
  exact bSet.subset_unfold.symm

def weightedSet {I : Type} (element : I → bSet B) (weight : I → B) : bSet B :=
  bSet.mk I element weight

theorem member_weightedSet {I : Type} (element : I → bSet B) (weight : I → B)
    (x : bSet B) : x ∈ᴮ weightedSet element weight = ⨆ i, weight i ⊓ x =ᴮ element i := rfl

theorem weight_le_member {I : Type} (element : I → bSet B) (weight : I → B) (i : I) :
    weight i ≤ element i ∈ᴮ weightedSet element weight :=
  bSet.mem.mk element weight i

theorem weighted_bounded_forall {I : Type} (element : I → bSet B) (weight : I → B)
    (predicate : bSet B → B) (hpredicate : bSet.B_ext predicate) :
    (⨅ x : bSet B, lattice.imp (x ∈ᴮ weightedSet element weight) (predicate x)) =
      ⨅ i, lattice.imp (weight i) (predicate (element i)) :=
  (bSet.bounded_forall (weightedSet element weight) predicate hpredicate).symm

theorem weighted_bounded_exists {I : Type} (element : I → bSet B) (weight : I → B)
    (predicate : bSet B → B) (hpredicate : bSet.B_ext predicate) :
    (⨆ x : bSet B, (x ∈ᴮ weightedSet element weight) ⊓ predicate x) =
      ⨆ i, weight i ⊓ predicate (element i) :=
  (bSet.bounded_exists (weightedSet element weight) predicate hpredicate).symm

theorem omega_bounded_exists (predicate : bSet B → B) (hpredicate : bSet.B_ext predicate) :
    (⨆ x : bSet B, (x ∈ᴮ bSet.omega) ⊓ predicate x) =
      ⨆ n : ℕ, predicate (bSet.ofNat n) := by
  rw [← bSet.bounded_exists bSet.omega predicate hpredicate]
  change (⨆ n : ULift ℕ, ⊤ ⊓ predicate (bSet.ofNat n.down)) = _
  simp only [top_inf_eq]
  apply le_antisymm
  · exact iSup_le fun n => le_iSup (fun k => predicate (bSet.ofNat k)) n.down
  · exact iSup_le fun n => le_iSup (fun k : ULift ℕ => predicate (bSet.ofNat k.down)) ⟨n⟩

theorem relationBetween_ext (domain codomain : bSet B) :
    bSet.B_ext (fun relation => relationBetweenValue (V B) domain codomain relation) := by
  unfold relationBetweenValue
  apply bSet.B_ext_iInf
  intro entry
  exact bSet.B_ext_sup (bSet.B_ext_compl (bSet.B_ext_mem_right entry)) (bSet.B_ext_const _)

theorem singleValued_ext : bSet.B_ext (fun relation : bSet B => singleValuedValue (V B) relation) := by
  unfold singleValuedValue
  apply bSet.B_ext_iInf
  intro x
  apply bSet.B_ext_iInf
  intro y
  apply bSet.B_ext_iInf
  intro z
  exact bSet.B_ext_sup (bSet.B_ext_compl (bSet.B_ext_inf
    (bSet.B_ext_mem_right (bSet.pair x y)) (bSet.B_ext_mem_right (bSet.pair x z))))
    (bSet.B_ext_const _)

theorem totalOn_ext (domain codomain : bSet B) :
    bSet.B_ext (fun relation => totalOnValue (V B) domain codomain relation) := by
  unfold totalOnValue
  apply bSet.B_ext_iInf
  intro x
  apply bSet.B_ext_sup (bSet.B_ext_const _)
  apply bSet.B_ext_iSup
  intro y
  exact bSet.B_ext_inf (bSet.B_ext_const _) (bSet.B_ext_mem_right (bSet.pair x y))

theorem functionFrom_ext (domain codomain : bSet B) :
    bSet.B_ext (fun relation => functionFromValue (V B) domain codomain relation) :=
  bSet.B_ext_inf (relationBetween_ext domain codomain)
    (bSet.B_ext_inf singleValued_ext (totalOn_ext domain codomain))

theorem injective_ext : bSet.B_ext (fun relation : bSet B => injectiveValue (V B) relation) := by
  unfold injectiveValue
  apply bSet.B_ext_iInf
  intro x
  apply bSet.B_ext_iInf
  intro y
  apply bSet.B_ext_iInf
  intro z
  exact bSet.B_ext_sup (bSet.B_ext_compl (bSet.B_ext_inf
    (bSet.B_ext_mem_right (bSet.pair x z)) (bSet.B_ext_mem_right (bSet.pair y z))))
    (bSet.B_ext_const _)

theorem injectsInto_witness (domain codomain : bSet B) {context : B}
    (h : context ≤ injectsIntoValue (V B) domain codomain) :
    ∃ relation : bSet B,
      context ≤ functionFromValue (V B) domain codomain relation ∧
        context ≤ injectiveValue (V B) relation := by
  obtain ⟨relation, hrelation⟩ := bSet.exists_convert h
    (bSet.B_ext_inf (functionFrom_ext domain codomain) injective_ext)
  exact ⟨relation, hrelation.trans inf_le_left, hrelation.trans inf_le_right⟩

end Erdos597Object.BooleanSets
