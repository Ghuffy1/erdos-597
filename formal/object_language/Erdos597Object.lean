import Flypitch.ZFC

/-!
The finite-target assertion as a sentence of the first-order set-theory language.
All graphs, functions, products and orders in this file are set-coded objects.
The relation symbol is membership and the pair symbol denotes an ordered pair.

The carrier of the host is the lexicographic product omega-one times omega-one.
The red target is the lexicographic product omega times omega-one. A blue copy
only preserves graph edges. Its map has no order-preservation requirement.
-/

namespace Erdos597Object

open Flypitch Flypitch.fol
open Flypitch.ZFC

abbrev Term (n : Nat) := bounded_term L_ZFC n
abbrev Formula (n : Nat) := bounded_formula L_ZFC n

def allSet {n : Nat} (body : Term (n + 1) → Formula (n + 1)) : Formula n :=
  bd_all (body var0)

def existsSet {n : Nat} (body : Term (n + 1) → Formula (n + 1)) : Formula n :=
  bd_ex (body var0)

def allMember {n : Nat} (domain : Term n)
    (body : Term (n + 1) → Formula (n + 1)) : Formula n :=
  allSet fun x => bd_imp (mem x domain.lift1) (body x)

def existsMember {n : Nat} (domain : Term n)
    (body : Term (n + 1) → Formula (n + 1)) : Formula n :=
  existsSet fun x => bd_and (mem x domain.lift1) (body x)

def nonempty {n : Nat} (domain : Term n) : Formula n :=
  existsMember domain fun x => bd_equal x x

def edge {n : Nat} (relation x y : Term n) : Formula n :=
  mem (pair x y) relation

def relationBetween {n : Nat} (domain codomain relation : Term n) : Formula n :=
  allMember relation fun entry =>
    existsMember domain.lift1 fun x =>
      existsMember codomain.lift1.lift1 fun y =>
        bd_equal entry.lift1.lift1 (pair x.lift1 y)

def singleValued {n : Nat} (relation : Term n) : Formula n :=
  allSet fun x => allSet fun y => allSet fun z =>
    bd_imp
      (bd_and (edge relation.lift1.lift1.lift1 x.lift1.lift1 y.lift1)
        (edge relation.lift1.lift1.lift1 x.lift1.lift1 z))
      (bd_equal y.lift1 z)

def totalOn {n : Nat} (domain codomain relation : Term n) : Formula n :=
  allMember domain fun x => existsMember codomain.lift1 fun y =>
    edge relation.lift1.lift1 x.lift1 y

def functionFrom {n : Nat} (domain codomain relation : Term n) : Formula n :=
  bd_and (relationBetween domain codomain relation)
    (bd_and (singleValued relation) (totalOn domain codomain relation))

def injective {n : Nat} (relation : Term n) : Formula n :=
  allSet fun x => allSet fun y => allSet fun z =>
    bd_imp
      (bd_and (edge relation.lift1.lift1.lift1 x.lift1.lift1 z)
        (edge relation.lift1.lift1.lift1 y.lift1 z))
      (bd_equal x.lift1.lift1 y.lift1)

def injectsInto {n : Nat} (domain codomain : Term n) : Formula n :=
  existsSet fun relation =>
    bd_and (functionFrom domain.lift1 codomain.lift1 relation) (injective relation)

def graph {n : Nat} (vertices edges : Term n) : Formula n :=
  bd_and (relationBetween vertices vertices edges)
    (bd_and
      (allMember vertices fun x => bd_not (edge edges.lift1 x x))
      (allMember vertices fun x => allMember vertices.lift1 fun y =>
        bd_biimp (edge edges.lift1.lift1 x.lift1 y)
          (edge edges.lift1.lift1 y x.lift1)))

def fourClique {n : Nat} (edges a b c d : Term n) : Formula n :=
  bd_and (edge edges a b)
    (bd_and (edge edges a c)
      (bd_and (edge edges a d)
        (bd_and (edge edges b c)
          (bd_and (edge edges b d) (edge edges c d)))))

def cliqueFreeFour {n : Nat} (vertices edges : Term n) : Formula n :=
  allMember vertices fun a => allMember vertices.lift1 fun b =>
    allMember vertices.lift1.lift1 fun c => allMember vertices.lift1.lift1.lift1 fun d =>
      bd_not (fourClique edges.lift1.lift1.lift1.lift1
        a.lift1.lift1.lift1 b.lift1.lift1 c.lift1 d)

def cartesianProduct {n : Nat} (left right product : Term n) : Formula n :=
  allSet fun entry =>
    bd_biimp (mem entry product.lift1)
      (existsMember left.lift1 fun x => existsMember right.lift1.lift1 fun y =>
        bd_equal entry.lift1.lift1 (pair x.lift1 y))

def lexLess {n : Nat} (x y : Term n) : Formula n :=
  existsSet fun a => existsSet fun b => existsSet fun c => existsSet fun d =>
    bd_and (bd_equal x.lift1.lift1.lift1.lift1 (pair a.lift1.lift1.lift1 b.lift1.lift1))
      (bd_and (bd_equal y.lift1.lift1.lift1.lift1 (pair c.lift1 d))
        (bd_or (mem a.lift1.lift1.lift1 c.lift1)
          (bd_and (bd_equal a.lift1.lift1.lift1 c.lift1) (mem b.lift1.lift1 d))))

def lexOrder {n : Nat} (domain order : Term n) : Formula n :=
  bd_and (relationBetween domain domain order)
    (allMember domain fun x => allMember domain.lift1 fun y =>
      bd_biimp (edge order.lift1.lift1 x.lift1 y) (lexLess x.lift1 y))

def preservesRelation {n : Nat} (source target mapping : Term n) : Formula n :=
  allSet fun x => allSet fun y => allSet fun u => allSet fun v =>
    bd_imp
      (bd_and (edge mapping.lift1.lift1.lift1.lift1 x.lift1.lift1.lift1 u.lift1)
        (edge mapping.lift1.lift1.lift1.lift1 y.lift1.lift1 v))
      (bd_imp (edge source.lift1.lift1.lift1.lift1 x.lift1.lift1.lift1 y.lift1.lift1)
        (edge target.lift1.lift1.lift1.lift1 u.lift1 v))

def respectsOrder {n : Nat} (source target mapping : Term n) : Formula n :=
  allSet fun x => allSet fun y => allSet fun u => allSet fun v =>
    bd_imp
      (bd_and (edge mapping.lift1.lift1.lift1.lift1 x.lift1.lift1.lift1 u.lift1)
        (edge mapping.lift1.lift1.lift1.lift1 y.lift1.lift1 v))
      (bd_biimp (edge source.lift1.lift1.lift1.lift1 x.lift1.lift1.lift1 y.lift1.lift1)
        (edge target.lift1.lift1.lift1.lift1 u.lift1 v))

def avoidsEdges {n : Nat} (blue mapping : Term n) : Formula n :=
  allSet fun x => allSet fun y => allSet fun u => allSet fun v =>
    bd_imp
      (bd_and (edge mapping.lift1.lift1.lift1.lift1 x.lift1.lift1.lift1 u.lift1)
        (edge mapping.lift1.lift1.lift1.lift1 y.lift1.lift1 v))
      (bd_imp (bd_not (bd_equal x.lift1.lift1.lift1 y.lift1.lift1))
        (bd_not (edge blue.lift1.lift1.lift1.lift1 u.lift1 v)))

def blueCopy {n : Nat} (vertices host edges blue : Term n) : Formula n :=
  existsSet fun mapping =>
    bd_and (functionFrom vertices.lift1 host.lift1 mapping)
      (bd_and (injective mapping) (preservesRelation edges.lift1 blue.lift1 mapping))

def redCopy {n : Nat} (redDomain host redOrder hostOrder blue : Term n) : Formula n :=
  existsSet fun mapping =>
    bd_and (functionFrom redDomain.lift1 host.lift1 mapping)
      (bd_and (injective mapping)
        (bd_and (respectsOrder redOrder.lift1 hostOrder.lift1 mapping)
          (avoidsEdges blue.lift1 mapping)))

def isOrdinal {n : Nat} (x : Term n) : Formula n :=
  subst_bounded_formula_open (OrdF.cast (by omega : 1 ≤ n + 1)) x

def omegaOne {n : Nat} (kappa : Term n) : Formula n :=
  bd_and (isOrdinal kappa)
    (bd_and (bd_not (injectsInto kappa omega))
      (allMember kappa fun alpha => injectsInto alpha omega))

def finitePartition {n : Nat} (host redDomain hostOrder redOrder : Term n) : Formula n :=
  allMember omega fun vertices => allSet fun edges =>
    bd_imp (bd_and (graph vertices.lift1 edges) (cliqueFreeFour vertices.lift1 edges))
      (allSet fun blue => bd_imp (graph host.lift1.lift1.lift1 blue)
        (bd_or
          (redCopy redDomain.lift1.lift1.lift1 host.lift1.lift1.lift1
            redOrder.lift1.lift1.lift1 hostOrder.lift1.lift1.lift1 blue)
          (blueCopy vertices.lift1.lift1 host.lift1.lift1.lift1 edges.lift1 blue)))

/-- Every standard set-coded presentation of the ordinal products satisfies the finite assertion. -/
def finiteAssertion : sentence L_ZFC :=
  allSet fun kappa => allSet fun host => allSet fun redDomain =>
    allSet fun hostOrder => allSet fun redOrder =>
      bd_imp
        (bd_and (omegaOne kappa.lift1.lift1.lift1.lift1)
          (bd_and (cartesianProduct kappa.lift1.lift1.lift1.lift1
              kappa.lift1.lift1.lift1.lift1 host.lift1.lift1.lift1)
            (bd_and (cartesianProduct omega kappa.lift1.lift1.lift1.lift1 redDomain.lift1.lift1)
              (bd_and (lexOrder host.lift1.lift1.lift1 hostOrder.lift1)
                (lexOrder redDomain.lift1.lift1 redOrder)))))
        (finitePartition host.lift1.lift1.lift1 redDomain.lift1.lift1 hostOrder.lift1 redOrder)

def partialOrder {n : Nat} (conditions order : Term n) : Formula n :=
  bd_and (relationBetween conditions conditions order)
    (bd_and
      (allMember conditions fun x => edge order.lift1 x x)
      (bd_and
        (allMember conditions fun x => allMember conditions.lift1 fun y =>
          bd_imp
            (bd_and (edge order.lift1.lift1 x.lift1 y)
              (edge order.lift1.lift1 y x.lift1))
            (bd_equal x.lift1 y))
        (allMember conditions fun x => allMember conditions.lift1 fun y =>
          allMember conditions.lift1.lift1 fun z =>
            bd_imp
              (bd_and (edge order.lift1.lift1.lift1 x.lift1.lift1 y.lift1)
                (edge order.lift1.lift1.lift1 y.lift1 z))
              (edge order.lift1.lift1.lift1 x.lift1.lift1 z))))

def compatible {n : Nat} (conditions order x y : Term n) : Formula n :=
  existsMember conditions fun z =>
    bd_and (edge order.lift1 z x.lift1) (edge order.lift1 z y.lift1)

def antichain {n : Nat} (conditions order family : Term n) : Formula n :=
  bd_and (subsetF family conditions)
    (allMember family fun x => allMember family.lift1 fun y =>
      bd_imp (bd_not (bd_equal x.lift1 y))
        (bd_not (compatible conditions.lift1.lift1 order.lift1.lift1 x.lift1 y)))

def countableChainCondition {n : Nat} (conditions order : Term n) : Formula n :=
  allSet fun family =>
    bd_imp (antichain conditions.lift1 order.lift1 family) (injectsInto family omega)

def dense {n : Nat} (conditions order denseSet : Term n) : Formula n :=
  bd_and (subsetF denseSet conditions)
    (allMember conditions fun x => existsMember denseSet.lift1 fun y =>
      edge order.lift1.lift1 y x.lift1)

def orderFilter {n : Nat} (conditions order filter : Term n) : Formula n :=
  bd_and (subsetF filter conditions)
    (bd_and
      (nonempty filter)
      (bd_and
        (allMember filter fun x => allMember conditions.lift1 fun y =>
          bd_imp (edge order.lift1.lift1 x.lift1 y) (mem y filter.lift1.lift1))
        (allMember filter fun x => allMember filter.lift1 fun y =>
          existsMember filter.lift1.lift1 fun z =>
            bd_and (edge order.lift1.lift1.lift1 z x.lift1.lift1)
              (edge order.lift1.lift1.lift1 z y.lift1))))

def meetsFamily {n : Nat} (filter family : Term n) : Formula n :=
  allMember family fun denseSet => existsMember filter.lift1 fun x => mem x denseSet.lift1

def martinAxiomAt {n : Nat} (kappa : Term n) : Formula n :=
  allSet fun conditions => allSet fun order => allSet fun family =>
    bd_imp
      (bd_and (nonempty conditions.lift1.lift1)
        (bd_and (partialOrder conditions.lift1.lift1 order.lift1)
          (bd_and (countableChainCondition conditions.lift1.lift1 order.lift1)
            (bd_and (injectsInto family kappa.lift1.lift1.lift1)
              (allMember family fun denseSet =>
                dense conditions.lift1.lift1.lift1 order.lift1.lift1 denseSet)))))
      (existsSet fun filter =>
        bd_and (orderFilter conditions.lift1.lift1.lift1 order.lift1.lift1 filter)
          (meetsFamily filter family.lift1))

def martinAxiomAlephOne : sentence L_ZFC :=
  allSet fun kappa => bd_imp (omegaOne kappa) (martinAxiomAt kappa)

/-- The negative conditional sentence, retained for the supplementary derivation route. -/
def negativeConditional : sentence L_ZFC := bd_imp CH_f (bd_not finiteAssertion)

/-- The positive conditional sentence, retained for the supplementary derivation route. -/
def positiveConditional : sentence L_ZFC := bd_imp martinAxiomAlephOne finiteAssertion

/-- The syntactic independence assertion proved in `Erdos597Object.Solution`. -/
def finiteIndependence : Prop :=
  ¬ (Flypitch.ZFC.ZFC ⊢' finiteAssertion) ∧
    ¬ (Flypitch.ZFC.ZFC ⊢' (bd_not finiteAssertion))

def relativeFiniteIndependence : Prop :=
  is_consistent Flypitch.ZFC.ZFC → finiteIndependence

#check finiteAssertion
#print axioms finiteAssertion
#check martinAxiomAlephOne
#check finiteIndependence
#check relativeFiniteIndependence

end Erdos597Object
