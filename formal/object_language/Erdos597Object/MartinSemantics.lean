import Erdos597Object.OrdinalSemantics

set_option backward.isDefEq.respectTransparency false

/-! Boolean-valued interpretations of the Martin-axiom sentence. -/

namespace Erdos597Object

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC

universe u

variable {B : Type u} [CompleteBooleanAlgebra B]
variable (S : bStructure L_ZFC B)

local notation "[]" => dvector.nil

def nonemptyValue (domain : S) : B :=
  ⨆ x : S, memberValue S x domain

theorem realize_nonempty {n : ℕ} (v : dvector S n) (domain : Term n) :
    boolean_realize_bounded_formula v (nonempty domain) [] =
      nonemptyValue S (boolean_realize_bounded_term v domain []) := by
  simp [nonempty, nonemptyValue, existsMember, existsSet, S.eq_refl]

def partialOrderValue (conditions order : S) : B :=
  relationBetweenValue S conditions conditions order ⊓
    ((⨅ x : S, (memberValue S x conditions)ᶜ ⊔ edgeValue S order x x) ⊓
      ((⨅ x : S, (memberValue S x conditions)ᶜ ⊔
          ⨅ y : S, (memberValue S y conditions)ᶜ ⊔
            (edgeValue S order x y ⊓ edgeValue S order y x)ᶜ ⊔ S.eq x y) ⊓
        ⨅ x : S, (memberValue S x conditions)ᶜ ⊔
          ⨅ y : S, (memberValue S y conditions)ᶜ ⊔
            ⨅ z : S, (memberValue S z conditions)ᶜ ⊔
              (edgeValue S order x y ⊓ edgeValue S order y z)ᶜ ⊔
                edgeValue S order x z))

theorem realize_partialOrder {n : ℕ} (v : dvector S n) (conditions order : Term n) :
    boolean_realize_bounded_formula v (partialOrder conditions order) [] =
      partialOrderValue S (boolean_realize_bounded_term v conditions [])
        (boolean_realize_bounded_term v order []) := by
  simp [partialOrder, partialOrderValue, realize_relationBetween, allMember, allSet,
    lattice.imp, sup_assoc]

def compatibleValue (conditions order x y : S) : B :=
  ⨆ z : S, memberValue S z conditions ⊓
    (edgeValue S order z x ⊓ edgeValue S order z y)

theorem realize_compatible {n : ℕ} (v : dvector S n) (conditions order x y : Term n) :
    boolean_realize_bounded_formula v (compatible conditions order x y) [] =
      compatibleValue S (boolean_realize_bounded_term v conditions [])
        (boolean_realize_bounded_term v order [])
        (boolean_realize_bounded_term v x []) (boolean_realize_bounded_term v y []) := by
  simp [compatible, compatibleValue, existsMember, existsSet]

def antichainValue (conditions order family : S) : B :=
  subsetValue S family conditions ⊓
    ⨅ x : S, (memberValue S x family)ᶜ ⊔
      ⨅ y : S, (memberValue S y family)ᶜ ⊔
        S.eq x y ⊔ (compatibleValue S conditions order x y)ᶜ

theorem realize_antichain {n : ℕ} (v : dvector S n) (conditions order family : Term n) :
    boolean_realize_bounded_formula v (antichain conditions order family) [] =
      antichainValue S (boolean_realize_bounded_term v conditions [])
        (boolean_realize_bounded_term v order [])
        (boolean_realize_bounded_term v family []) := by
  simp [antichain, antichainValue, realize_subset, realize_compatible,
    allMember, allSet, lattice.imp, sup_assoc]

def countableChainConditionValue (conditions order : S) : B :=
  ⨅ family : S, (antichainValue S conditions order family)ᶜ ⊔
    injectsIntoValue S family (S.fun_map ZFCFunc.omega [])

theorem realize_countableChainCondition {n : ℕ} (v : dvector S n)
    (conditions order : Term n) :
    boolean_realize_bounded_formula v (countableChainCondition conditions order) [] =
      countableChainConditionValue S (boolean_realize_bounded_term v conditions [])
        (boolean_realize_bounded_term v order []) := by
  simp [countableChainCondition, countableChainConditionValue,
    realize_antichain, realize_injectsInto, allSet, lattice.imp]

def denseValue (conditions order denseSet : S) : B :=
  subsetValue S denseSet conditions ⊓
    ⨅ x : S, (memberValue S x conditions)ᶜ ⊔
      ⨆ y : S, memberValue S y denseSet ⊓ edgeValue S order y x

theorem realize_dense {n : ℕ} (v : dvector S n) (conditions order denseSet : Term n) :
    boolean_realize_bounded_formula v (dense conditions order denseSet) [] =
      denseValue S (boolean_realize_bounded_term v conditions [])
        (boolean_realize_bounded_term v order [])
        (boolean_realize_bounded_term v denseSet []) := by
  simp [dense, denseValue, realize_subset, allMember, allSet, existsMember, existsSet, lattice.imp]

def orderFilterValue (conditions order filter : S) : B :=
  subsetValue S filter conditions ⊓
    (nonemptyValue S filter ⊓
      ((⨅ x : S, (memberValue S x filter)ᶜ ⊔
          ⨅ y : S, (memberValue S y conditions)ᶜ ⊔
            (edgeValue S order x y)ᶜ ⊔ memberValue S y filter) ⊓
        ⨅ x : S, (memberValue S x filter)ᶜ ⊔
          ⨅ y : S, (memberValue S y filter)ᶜ ⊔
            ⨆ z : S, memberValue S z filter ⊓
              (edgeValue S order z x ⊓ edgeValue S order z y)))

theorem realize_orderFilter {n : ℕ} (v : dvector S n) (conditions order filter : Term n) :
    boolean_realize_bounded_formula v (orderFilter conditions order filter) [] =
      orderFilterValue S (boolean_realize_bounded_term v conditions [])
        (boolean_realize_bounded_term v order [])
        (boolean_realize_bounded_term v filter []) := by
  simp [orderFilter, orderFilterValue, realize_subset, realize_nonempty,
    allMember, allSet, existsMember, existsSet, lattice.imp, sup_assoc]

def meetsFamilyValue (filter family : S) : B :=
  ⨅ denseSet : S, (memberValue S denseSet family)ᶜ ⊔
    ⨆ x : S, memberValue S x filter ⊓ memberValue S x denseSet

theorem realize_meetsFamily {n : ℕ} (v : dvector S n) (filter family : Term n) :
    boolean_realize_bounded_formula v (meetsFamily filter family) [] =
      meetsFamilyValue S (boolean_realize_bounded_term v filter [])
        (boolean_realize_bounded_term v family []) := by
  simp [meetsFamily, meetsFamilyValue, allMember, allSet, existsMember, existsSet, lattice.imp]

def martinAxiomAtValue (kappa : S) : B :=
  ⨅ conditions : S, ⨅ order : S, ⨅ family : S,
    (nonemptyValue S conditions ⊓
      (partialOrderValue S conditions order ⊓
        (countableChainConditionValue S conditions order ⊓
          (injectsIntoValue S family kappa ⊓
            ⨅ denseSet : S, (memberValue S denseSet family)ᶜ ⊔
              denseValue S conditions order denseSet))))ᶜ ⊔
      ⨆ filter : S, orderFilterValue S conditions order filter ⊓
        meetsFamilyValue S filter family

theorem realize_martinAxiomAt {n : ℕ} (v : dvector S n) (kappa : Term n) :
    boolean_realize_bounded_formula v (martinAxiomAt kappa) [] =
      martinAxiomAtValue S (boolean_realize_bounded_term v kappa []) := by
  simp [martinAxiomAt, martinAxiomAtValue, realize_nonempty, realize_partialOrder,
    realize_countableChainCondition, realize_injectsInto, realize_dense,
    realize_orderFilter, realize_meetsFamily, allMember, allSet, existsSet, lattice.imp]

def martinAxiomAlephOneValue : B :=
  ⨅ kappa : S, (omegaOneValue S kappa)ᶜ ⊔ martinAxiomAtValue S kappa

theorem realize_martinAxiomAlephOne :
    boolean_realize_sentence S martinAxiomAlephOne = martinAxiomAlephOneValue S := by
  change boolean_realize_bounded_formula (S := S) [] martinAxiomAlephOne [] = _
  simp [martinAxiomAlephOne, martinAxiomAlephOneValue, realize_omegaOne,
    realize_martinAxiomAt, allSet, lattice.imp]

end Erdos597Object
