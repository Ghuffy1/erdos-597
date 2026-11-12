import Erdos597Object.BooleanBoundedTransport
import Erdos597Object.BooleanPosetModel

set_option backward.isDefEq.respectTransparency false

/-! Transport of the bounded forcing predicates used by the Martin-axiom construction. -/

namespace Erdos597Object.BooleanForcingTransport

open Flypitch Flypitch.ZFC BooleanNameTransport BooleanBoundedTransport BooleanSets
open BooleanAntichains BooleanPosetModel
open scoped Flypitch.bSet

variable {B C : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

theorem map_bounded_forall_two (f : CompleteLatticeHom B C) (x y : bSet B)
    (φ : bSet B → bSet B → B) (ψ : bSet C → bSet C → C)
    (hφleft : ∀ b, bSet.B_ext (fun a => φ a b)) (hφright : ∀ a, bSet.B_ext (φ a))
    (hψleft : ∀ b, bSet.B_ext (fun a => ψ a b)) (hψright : ∀ a, bSet.B_ext (ψ a))
    (hmap : ∀ a b, f (φ a b) = ψ (nameMap f a) (nameMap f b)) :
    f (⨅ a : bSet B, lattice.imp (a ∈ᴮ x)
      (⨅ b : bSet B, lattice.imp (b ∈ᴮ y) (φ a b))) =
      ⨅ a : bSet C, lattice.imp (a ∈ᴮ nameMap f x)
        (⨅ b : bSet C, lattice.imp (b ∈ᴮ nameMap f y) (ψ a b)) := by
  apply map_bounded_forall
  · exact bSet.B_ext_iInf fun b => bSet.B_ext_imp (bSet.B_ext_const _) (hφleft b)
  · exact bSet.B_ext_iInf fun b => bSet.B_ext_imp (bSet.B_ext_const _) (hψleft b)
  · intro a
    exact map_bounded_forall f y (φ a) (ψ (nameMap f a))
      (hφright a) (hψright _) (hmap a)

theorem map_subsetValue (f : CompleteLatticeHom B C) (x y : bSet B) :
    f (subsetValue (V B) x y) = subsetValue (V C) (nameMap f x) (nameMap f y) := by
  simpa only [subsetValue_bSet] using map_subset f x y

theorem map_bounded_forall_three (f : CompleteLatticeHom B C) (x y z : bSet B)
    (φ : bSet B → bSet B → bSet B → B) (ψ : bSet C → bSet C → bSet C → C)
    (hφfirst : ∀ b c, bSet.B_ext (fun a => φ a b c))
    (hφsecond : ∀ a c, bSet.B_ext (fun b => φ a b c))
    (hφthird : ∀ a b, bSet.B_ext (φ a b))
    (hψfirst : ∀ b c, bSet.B_ext (fun a => ψ a b c))
    (hψsecond : ∀ a c, bSet.B_ext (fun b => ψ a b c))
    (hψthird : ∀ a b, bSet.B_ext (ψ a b))
    (hmap : ∀ a b c, f (φ a b c) = ψ (nameMap f a) (nameMap f b) (nameMap f c)) :
    f (⨅ a : bSet B, lattice.imp (a ∈ᴮ x)
      (⨅ b : bSet B, lattice.imp (b ∈ᴮ y)
        (⨅ c : bSet B, lattice.imp (c ∈ᴮ z) (φ a b c)))) =
      ⨅ a : bSet C, lattice.imp (a ∈ᴮ nameMap f x)
        (⨅ b : bSet C, lattice.imp (b ∈ᴮ nameMap f y)
          (⨅ c : bSet C, lattice.imp (c ∈ᴮ nameMap f z) (ψ a b c))) := by
  apply map_bounded_forall
  · exact bSet.B_ext_iInf fun b => bSet.B_ext_imp (bSet.B_ext_const _)
      (bSet.B_ext_iInf fun c => bSet.B_ext_imp (bSet.B_ext_const _) (hφfirst b c))
  · exact bSet.B_ext_iInf fun b => bSet.B_ext_imp (bSet.B_ext_const _)
      (bSet.B_ext_iInf fun c => bSet.B_ext_imp (bSet.B_ext_const _) (hψfirst b c))
  · intro a
    exact map_bounded_forall_two f y z (φ a) (ψ (nameMap f a))
      (hφsecond a) (hφthird a) (hψsecond _) (hψthird _) (hmap a)

theorem relationWitness_ext (domain codomain : bSet B) :
    bSet.B_ext (fun entry : bSet B =>
      ⨆ x : bSet B, (x ∈ᴮ domain) ⊓
        ⨆ y : bSet B, (y ∈ᴮ codomain) ⊓ (entry =ᴮ bSet.pair x y)) :=
  bSet.B_ext_iSup fun x => bSet.B_ext_inf (bSet.B_ext_const _)
    (bSet.B_ext_iSup fun y => bSet.B_ext_inf (bSet.B_ext_const _)
      (bSet.B_ext_eq_left (bSet.pair x y)))

theorem map_relationWitness (f : CompleteLatticeHom B C) (domain codomain entry : bSet B) :
    f (⨆ x : bSet B, (x ∈ᴮ domain) ⊓
      ⨆ y : bSet B, (y ∈ᴮ codomain) ⊓ (entry =ᴮ bSet.pair x y)) =
      ⨆ x : bSet C, (x ∈ᴮ nameMap f domain) ⊓
        ⨆ y : bSet C, (y ∈ᴮ nameMap f codomain) ⊓ (nameMap f entry =ᴮ bSet.pair x y) := by
  apply map_bounded_exists
  · exact bSet.B_ext_iSup fun y => bSet.B_ext_inf (bSet.B_ext_const _)
      (bSet.B_ext_pair_left (bSet.B_ext_eq_right entry) y)
  · exact bSet.B_ext_iSup fun y => bSet.B_ext_inf (bSet.B_ext_const _)
      (bSet.B_ext_pair_left (bSet.B_ext_eq_right (nameMap f entry)) y)
  · intro x
    apply map_bounded_exists
    · exact bSet.B_ext_pair_right (bSet.B_ext_eq_right entry) x
    · exact bSet.B_ext_pair_right (bSet.B_ext_eq_right (nameMap f entry)) (nameMap f x)
    · intro y
      rw [map_bv_eq, nameMap_pair]

theorem map_relationBetweenValue (f : CompleteLatticeHom B C) (domain codomain relation : bSet B) :
    f (relationBetweenValue (V B) domain codomain relation) =
      relationBetweenValue (V C) (nameMap f domain) (nameMap f codomain) (nameMap f relation) :=
  map_bounded_forall f relation _ _ (relationWitness_ext domain codomain)
    (relationWitness_ext _ _) (map_relationWitness f domain codomain)

theorem map_reflexiveBody (f : CompleteLatticeHom B C) (order x : bSet B) :
    f (reflexiveBody order x) = reflexiveBody (nameMap f order) (nameMap f x) :=
  map_edgeValue f order x x

theorem map_antisymmetricBody (f : CompleteLatticeHom B C) (order x y : bSet B) :
    f (antisymmetricBody order x y) =
      antisymmetricBody (nameMap f order) (nameMap f x) (nameMap f y) := by
  simp only [antisymmetricBody, map_imp, map_inf, map_edgeValue, map_bv_eq]

theorem map_transitiveBody (f : CompleteLatticeHom B C) (order x y z : bSet B) :
    f (transitiveBody order x y z) =
      transitiveBody (nameMap f order) (nameMap f x) (nameMap f y) (nameMap f z) := by
  simp only [transitiveBody, map_imp, map_inf, map_edgeValue]

theorem map_partialOrderValue (f : CompleteLatticeHom B C) (conditions order : bSet B) :
    f (partialOrderValue (V B) conditions order) =
      partialOrderValue (V C) (nameMap f conditions) (nameMap f order) := by
  have hr := map_bounded_forall f conditions (reflexiveBody order)
    (reflexiveBody (nameMap f order)) (reflexiveBody_ext order) (reflexiveBody_ext _)
    (map_reflexiveBody f order)
  have ha := map_bounded_forall_two f conditions conditions (antisymmetricBody order)
    (antisymmetricBody (nameMap f order)) (antisymmetricBody_left_ext order)
    (antisymmetricBody_right_ext order) (antisymmetricBody_left_ext _)
    (antisymmetricBody_right_ext _) (map_antisymmetricBody f order)
  have ht := map_bounded_forall_three f conditions conditions conditions (transitiveBody order)
    (transitiveBody (nameMap f order)) (transitiveBody_first_ext order)
    (transitiveBody_second_ext order) (transitiveBody_third_ext order)
    (transitiveBody_first_ext _) (transitiveBody_second_ext _) (transitiveBody_third_ext _)
    (map_transitiveBody f order)
  have hparts := congrArg₂ (fun a b => a ⊓ b) hr (congrArg₂ (fun a b => a ⊓ b) ha ht)
  simp only [partialOrderValue, map_inf, map_relationBetweenValue]
  apply congrArg (fun a => relationBetweenValue (V C) (nameMap f conditions)
    (nameMap f conditions) (nameMap f order) ⊓ a)
  simpa only [memberValue_bSet, eqValue_bSet, reflexiveBody, antisymmetricBody,
    transitiveBody, lattice.imp, sup_assoc] using! hparts

theorem map_compatibleValue (f : CompleteLatticeHom B C) (conditions order x y : bSet B) :
    f (Erdos597Object.compatibleValue (V B) conditions order x y) =
      Erdos597Object.compatibleValue (V C) (nameMap f conditions) (nameMap f order)
        (nameMap f x) (nameMap f y) := by
  exact map_bounded_exists f conditions
    (fun z => edgeValue (V B) order z x ⊓ edgeValue (V B) order z y)
    (fun z => edgeValue (V C) (nameMap f order) z (nameMap f x) ⊓
      edgeValue (V C) (nameMap f order) z (nameMap f y))
    (compatibleWitness_ext order x y) (compatibleWitness_ext _ _ _)
    (by intro z; simp only [map_inf, map_edgeValue])

theorem map_antichainValue (f : CompleteLatticeHom B C) (conditions order family : bSet B) :
    f (antichainValue (V B) conditions order family) =
      antichainValue (V C) (nameMap f conditions) (nameMap f order) (nameMap f family) := by
  have hbody := map_bounded_forall_two f family family
    (fun x y => (x =ᴮ y) ⊔ (Erdos597Object.compatibleValue (V B) conditions order x y)ᶜ)
    (fun x y => (x =ᴮ y) ⊔ (Erdos597Object.compatibleValue (V C)
      (nameMap f conditions) (nameMap f order) x y)ᶜ)
    (fun y => bSet.B_ext_sup (bSet.B_ext_eq_left y)
      (bSet.B_ext_compl (compatible_left_ext conditions order y)))
    (fun x => bSet.B_ext_sup (bSet.B_ext_eq_right x)
      (bSet.B_ext_compl (compatible_right_ext conditions order x)))
    (fun y => bSet.B_ext_sup (bSet.B_ext_eq_left y)
      (bSet.B_ext_compl (compatible_left_ext _ _ y)))
    (fun x => bSet.B_ext_sup (bSet.B_ext_eq_right x)
      (bSet.B_ext_compl (compatible_right_ext _ _ x)))
    (by intro x y; simp only [map_sup, map_compl', map_bv_eq, map_compatibleValue])
  simp only [antichainValue, map_inf, map_subsetValue]
  apply congrArg (fun a => subsetValue (V C) (nameMap f family) (nameMap f conditions) ⊓ a)
  simpa only [memberValue_bSet, eqValue_bSet, lattice.imp, sup_assoc] using! hbody

theorem map_denseValue (f : CompleteLatticeHom B C) (conditions order denseSet : bSet B) :
    f (denseValue (V B) conditions order denseSet) =
      denseValue (V C) (nameMap f conditions) (nameMap f order) (nameMap f denseSet) := by
  have hbody := map_bounded_forall f conditions
    (fun x => ⨆ y : bSet B, (y ∈ᴮ denseSet) ⊓ edgeValue (V B) order y x)
    (fun x => ⨆ y : bSet C, (y ∈ᴮ nameMap f denseSet) ⊓
      edgeValue (V C) (nameMap f order) y x)
    (bSet.B_ext_iSup fun y => bSet.B_ext_inf (bSet.B_ext_const _) bSet.B_ext_pair_mem_right)
    (bSet.B_ext_iSup fun y => bSet.B_ext_inf (bSet.B_ext_const _) bSet.B_ext_pair_mem_right)
    (by
      intro x
      exact map_bounded_exists f denseSet _ _ bSet.B_ext_pair_mem_left bSet.B_ext_pair_mem_left
        (fun y => map_edgeValue f order y x))
  change f (subsetValue (V B) denseSet conditions ⊓
    (⨅ x : bSet B, lattice.imp (x ∈ᴮ conditions)
      (⨆ y : bSet B, (y ∈ᴮ denseSet) ⊓ edgeValue (V B) order y x))) =
    subsetValue (V C) (nameMap f denseSet) (nameMap f conditions) ⊓
      (⨅ x : bSet C, lattice.imp (x ∈ᴮ nameMap f conditions)
        (⨆ y : bSet C, (y ∈ᴮ nameMap f denseSet) ⊓ edgeValue (V C) (nameMap f order) y x))
  rw [map_inf, map_subsetValue]
  exact congrArg (fun a => subsetValue (V C) (nameMap f denseSet) (nameMap f conditions) ⊓ a) hbody

theorem map_meetsFamilyValue (f : CompleteLatticeHom B C) (filter family : bSet B) :
    f (meetsFamilyValue (V B) filter family) =
      meetsFamilyValue (V C) (nameMap f filter) (nameMap f family) := by
  exact map_bounded_forall f family
    (fun d => ⨆ x : bSet B, (x ∈ᴮ filter) ⊓ (x ∈ᴮ d))
    (fun d => ⨆ x : bSet C, (x ∈ᴮ nameMap f filter) ⊓ (x ∈ᴮ d))
    (bSet.B_ext_iSup fun x => bSet.B_ext_inf (bSet.B_ext_const _) (bSet.B_ext_mem_right x))
    (bSet.B_ext_iSup fun x => bSet.B_ext_inf (bSet.B_ext_const _) (bSet.B_ext_mem_right x))
    (fun d => map_bounded_exists f filter _ _ (bSet.B_ext_mem_left d)
      (bSet.B_ext_mem_left _) (fun x => map_mem f x d))

theorem map_orderFilterValue (f : CompleteLatticeHom B C) (conditions order filter : bSet B) :
    f (orderFilterValue (V B) conditions order filter) =
      orderFilterValue (V C) (nameMap f conditions) (nameMap f order) (nameMap f filter) := by
  have hup := map_bounded_forall_two f filter conditions
    (fun x y => lattice.imp (edgeValue (V B) order x y) (y ∈ᴮ filter))
    (fun x y => lattice.imp (edgeValue (V C) (nameMap f order) x y) (y ∈ᴮ nameMap f filter))
    (fun y => bSet.B_ext_imp bSet.B_ext_pair_mem_left (bSet.B_ext_const _))
    (fun x => bSet.B_ext_imp bSet.B_ext_pair_mem_right (bSet.B_ext_mem_left filter))
    (fun y => bSet.B_ext_imp bSet.B_ext_pair_mem_left (bSet.B_ext_const _))
    (fun x => bSet.B_ext_imp bSet.B_ext_pair_mem_right (bSet.B_ext_mem_left _))
    (by intro x y; simp only [map_imp, map_edgeValue, map_mem])
  have hdir := map_bounded_forall_two f filter filter
    (fun x y => Erdos597Object.compatibleValue (V B) filter order x y)
    (fun x y => Erdos597Object.compatibleValue (V C) (nameMap f filter) (nameMap f order) x y)
    (compatible_left_ext filter order) (compatible_right_ext filter order)
    (compatible_left_ext _ _) (compatible_right_ext _ _)
    (fun x y => map_compatibleValue f filter order x y)
  simp only [orderFilterValue, map_inf, map_subsetValue, map_nonemptyValue]
  apply congrArg (fun a => subsetValue (V C) (nameMap f filter) (nameMap f conditions) ⊓
    (nonemptyValue (V C) (nameMap f filter) ⊓ a))
  have hparts := congrArg₂ (fun a b : C => a ⊓ b) hup hdir
  simpa only [Erdos597Object.compatibleValue, memberValue_bSet, lattice.imp, sup_assoc] using! hparts

end Erdos597Object.BooleanForcingTransport
