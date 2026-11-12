import Erdos597Object

set_option backward.isDefEq.respectTransparency false

/-! Boolean-valued interpretations of the set-coded graph predicates. -/

namespace Erdos597Object

open Flypitch Flypitch.fol Flypitch.fol.bfol
open Flypitch.ZFC

universe u

variable {B : Type u} [CompleteBooleanAlgebra B]
variable (S : bStructure L_ZFC B)

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

def memberValue (x y : S) : B := S.rel_map ZFCRel.epsilon (x :: y :: [])

def pairValue (x y : S) : S := S.fun_map ZFCFunc.pair (x :: y :: [])

def edgeValue (relation x y : S) : B := memberValue S (pairValue S x y) relation

def relationBetweenValue (domain codomain relation : S) : B :=
  ⨅ entry : S, (memberValue S entry relation)ᶜ ⊔
    ⨆ x : S, memberValue S x domain ⊓
      ⨆ y : S, memberValue S y codomain ⊓ S.eq entry (pairValue S x y)

def singleValuedValue (relation : S) : B :=
  ⨅ x : S, ⨅ y : S, ⨅ z : S,
    (edgeValue S relation x y ⊓ edgeValue S relation x z)ᶜ ⊔ S.eq y z

def totalOnValue (domain codomain relation : S) : B :=
  ⨅ x : S, (memberValue S x domain)ᶜ ⊔
    ⨆ y : S, memberValue S y codomain ⊓ edgeValue S relation x y

def functionFromValue (domain codomain relation : S) : B :=
  relationBetweenValue S domain codomain relation ⊓
    (singleValuedValue S relation ⊓ totalOnValue S domain codomain relation)

def injectiveValue (relation : S) : B :=
  ⨅ x : S, ⨅ y : S, ⨅ z : S,
    (edgeValue S relation x z ⊓ edgeValue S relation y z)ᶜ ⊔ S.eq x y

def graphValue (vertices edges : S) : B :=
  relationBetweenValue S vertices vertices edges ⊓
    ((⨅ x : S, (memberValue S x vertices)ᶜ ⊔ (edgeValue S edges x x)ᶜ) ⊓
      ⨅ x : S, (memberValue S x vertices)ᶜ ⊔
        ⨅ y : S, (memberValue S y vertices)ᶜ ⊔
          (((edgeValue S edges x y)ᶜ ⊔ edgeValue S edges y x) ⊓
            ((edgeValue S edges y x)ᶜ ⊔ edgeValue S edges x y)))

def fourCliqueValue (edges a b c d : S) : B :=
  edgeValue S edges a b ⊓
    (edgeValue S edges a c ⊓
      (edgeValue S edges a d ⊓
        (edgeValue S edges b c ⊓
          (edgeValue S edges b d ⊓ edgeValue S edges c d))))

def cliqueFreeFourValue (vertices edges : S) : B :=
  ⨅ a : S, (memberValue S a vertices)ᶜ ⊔
    ⨅ b : S, (memberValue S b vertices)ᶜ ⊔
      ⨅ c : S, (memberValue S c vertices)ᶜ ⊔
        ⨅ d : S, (memberValue S d vertices)ᶜ ⊔ (fourCliqueValue S edges a b c d)ᶜ

def cartesianProductValue (left right product : S) : B :=
  ⨅ entry : S,
    let rhs := ⨆ x : S, memberValue S x left ⊓
      ⨆ y : S, memberValue S y right ⊓ S.eq entry (pairValue S x y)
    ((memberValue S entry product)ᶜ ⊔ rhs) ⊓ (rhsᶜ ⊔ memberValue S entry product)

def lexLessValue (x y : S) : B :=
  ⨆ a : S, ⨆ b : S, ⨆ c : S, ⨆ d : S,
    S.eq x (pairValue S a b) ⊓
      (S.eq y (pairValue S c d) ⊓
        (memberValue S a c ⊔ (S.eq a c ⊓ memberValue S b d)))

def lexOrderValue (domain order : S) : B :=
  relationBetweenValue S domain domain order ⊓
    ⨅ x : S, (memberValue S x domain)ᶜ ⊔
      ⨅ y : S, (memberValue S y domain)ᶜ ⊔
        (((edgeValue S order x y)ᶜ ⊔ lexLessValue S x y) ⊓
          ((lexLessValue S x y)ᶜ ⊔ edgeValue S order x y))

def preservesRelationValue (source target mapping : S) : B :=
  ⨅ x : S, ⨅ y : S, ⨅ a : S, ⨅ b : S,
    (edgeValue S mapping x a ⊓ edgeValue S mapping y b)ᶜ ⊔
      ((edgeValue S source x y)ᶜ ⊔ edgeValue S target a b)

def respectsOrderValue (source target mapping : S) : B :=
  ⨅ x : S, ⨅ y : S, ⨅ a : S, ⨅ b : S,
    (edgeValue S mapping x a ⊓ edgeValue S mapping y b)ᶜ ⊔
      (((edgeValue S source x y)ᶜ ⊔ edgeValue S target a b) ⊓
        ((edgeValue S target a b)ᶜ ⊔ edgeValue S source x y))

def avoidsEdgesValue (blue mapping : S) : B :=
  ⨅ x : S, ⨅ y : S, ⨅ a : S, ⨅ b : S,
    (edgeValue S mapping x a ⊓ edgeValue S mapping y b)ᶜ ⊔
      (S.eq x y ⊔ (edgeValue S blue a b)ᶜ)

def blueCopyValue (vertices host edges blue : S) : B :=
  ⨆ mapping : S, functionFromValue S vertices host mapping ⊓
    (injectiveValue S mapping ⊓ preservesRelationValue S edges blue mapping)

def redCopyValue (redDomain host redOrder hostOrder blue : S) : B :=
  ⨆ mapping : S, functionFromValue S redDomain host mapping ⊓
    (injectiveValue S mapping ⊓
      (respectsOrderValue S redOrder hostOrder mapping ⊓ avoidsEdgesValue S blue mapping))

@[simp] theorem realize_pair {n : Nat} (v : dvector S n) (x y : Term n) :
    boolean_realize_bounded_term v (pair x y) [] =
      pairValue S (boolean_realize_bounded_term v x [])
        (boolean_realize_bounded_term v y []) := by
  simp only [Flypitch.ZFC.pair, Flypitch.fol.bd_apps, Flypitch.fol.bd_app,
    Flypitch.fol.bd_func, Flypitch.fol.bfol.boolean_realize_bounded_term,
    Flypitch.fol.bfol.boolean_realize_bounded_term_mk_fst, pairValue]
  rfl

@[simp] theorem realize_member {n : Nat} (v : dvector S n) (x y : Term n) :
    boolean_realize_bounded_formula v (mem x y) [] =
      memberValue S (boolean_realize_bounded_term v x [])
        (boolean_realize_bounded_term v y []) := by
  simp only [Flypitch.ZFC.mem, Flypitch.fol.bd_apps_rel, Flypitch.fol.bd_apprel,
    Flypitch.fol.bd_rel, Flypitch.fol.bfol.boolean_realize_bounded_formula,
    Flypitch.fol.bfol.boolean_realize_bounded_term_mk_fst, memberValue]
  rfl

@[simp] theorem realize_equal {n : Nat} (v : dvector S n) (x y : Term n) :
    boolean_realize_bounded_formula v (bd_equal x y) [] =
      S.eq (boolean_realize_bounded_term v x [])
        (boolean_realize_bounded_term v y []) := by
  exact Flypitch.fol.bfol.boolean_realize_bounded_formula_equal x y

@[simp] theorem realize_var0 {n : Nat} (v : dvector S n) (x : S) :
    boolean_realize_bounded_term (x :: v) (var0 : Term (n + 1)) [] = x := by
  simp only [Flypitch.ZFC.var0, Flypitch.ZFC.var, Flypitch.fol.bd_var,
    Flypitch.fol.bfol.boolean_realize_bounded_term, dvector.nth]

@[simp] theorem realize_edge {n : Nat} (v : dvector S n) (relation x y : Term n) :
    boolean_realize_bounded_formula v (edge relation x y) [] =
      edgeValue S (boolean_realize_bounded_term v relation [])
        (boolean_realize_bounded_term v x []) (boolean_realize_bounded_term v y []) := by
  simp [edge, edgeValue]

theorem realize_relationBetween {n : Nat} (v : dvector S n)
    (domain codomain relation : Term n) :
    boolean_realize_bounded_formula v (relationBetween domain codomain relation) [] =
      relationBetweenValue S (boolean_realize_bounded_term v domain [])
        (boolean_realize_bounded_term v codomain [])
        (boolean_realize_bounded_term v relation []) := by
  simp [relationBetween, allMember, allSet, existsMember, existsSet,
    relationBetweenValue, lattice.imp]

theorem realize_singleValued {n : Nat} (v : dvector S n) (relation : Term n) :
    boolean_realize_bounded_formula v (singleValued relation) [] =
      singleValuedValue S (boolean_realize_bounded_term v relation []) := by
  simp [singleValued, allSet, singleValuedValue, lattice.imp]

theorem realize_totalOn {n : Nat} (v : dvector S n)
    (domain codomain relation : Term n) :
    boolean_realize_bounded_formula v (totalOn domain codomain relation) [] =
      totalOnValue S (boolean_realize_bounded_term v domain [])
        (boolean_realize_bounded_term v codomain [])
        (boolean_realize_bounded_term v relation []) := by
  simp [totalOn, allMember, allSet, existsMember, existsSet, totalOnValue, lattice.imp]

theorem realize_functionFrom {n : Nat} (v : dvector S n)
    (domain codomain relation : Term n) :
    boolean_realize_bounded_formula v (functionFrom domain codomain relation) [] =
      functionFromValue S (boolean_realize_bounded_term v domain [])
        (boolean_realize_bounded_term v codomain [])
        (boolean_realize_bounded_term v relation []) := by
  simp [functionFrom, functionFromValue, realize_relationBetween,
    realize_singleValued, realize_totalOn]

theorem realize_injective {n : Nat} (v : dvector S n) (relation : Term n) :
    boolean_realize_bounded_formula v (injective relation) [] =
      injectiveValue S (boolean_realize_bounded_term v relation []) := by
  simp [injective, allSet, injectiveValue, lattice.imp]

theorem realize_graph {n : Nat} (v : dvector S n) (vertices edges : Term n) :
    boolean_realize_bounded_formula v (graph vertices edges) [] =
      graphValue S (boolean_realize_bounded_term v vertices [])
        (boolean_realize_bounded_term v edges []) := by
  simp [graph, graphValue, realize_relationBetween, allMember, allSet, bd_biimp, lattice.imp]

theorem realize_fourClique {n : Nat} (v : dvector S n) (edges a b c d : Term n) :
    boolean_realize_bounded_formula v (fourClique edges a b c d) [] =
      fourCliqueValue S (boolean_realize_bounded_term v edges [])
        (boolean_realize_bounded_term v a []) (boolean_realize_bounded_term v b [])
        (boolean_realize_bounded_term v c []) (boolean_realize_bounded_term v d []) := by
  simp [fourClique, fourCliqueValue]

theorem realize_cliqueFreeFour {n : Nat} (v : dvector S n) (vertices edges : Term n) :
    boolean_realize_bounded_formula v (cliqueFreeFour vertices edges) [] =
      cliqueFreeFourValue S (boolean_realize_bounded_term v vertices [])
        (boolean_realize_bounded_term v edges []) := by
  simp [cliqueFreeFour, cliqueFreeFourValue, allMember, allSet, realize_fourClique, lattice.imp]

theorem realize_cartesianProduct {n : Nat} (v : dvector S n) (left right product : Term n) :
    boolean_realize_bounded_formula v (cartesianProduct left right product) [] =
      cartesianProductValue S (boolean_realize_bounded_term v left [])
        (boolean_realize_bounded_term v right []) (boolean_realize_bounded_term v product []) := by
  simp [cartesianProduct, cartesianProductValue, allMember, allSet,
    existsMember, existsSet, bd_biimp, lattice.imp]

theorem realize_lexLess {n : Nat} (v : dvector S n) (x y : Term n) :
    boolean_realize_bounded_formula v (lexLess x y) [] =
      lexLessValue S (boolean_realize_bounded_term v x [])
        (boolean_realize_bounded_term v y []) := by
  simp [lexLess, lexLessValue, existsSet]

theorem realize_lexOrder {n : Nat} (v : dvector S n) (domain order : Term n) :
    boolean_realize_bounded_formula v (lexOrder domain order) [] =
      lexOrderValue S (boolean_realize_bounded_term v domain [])
        (boolean_realize_bounded_term v order []) := by
  simp [lexOrder, lexOrderValue, realize_relationBetween, realize_lexLess,
    allMember, allSet, bd_biimp, lattice.imp]

theorem realize_preservesRelation {n : Nat} (v : dvector S n) (source target mapping : Term n) :
    boolean_realize_bounded_formula v (preservesRelation source target mapping) [] =
      preservesRelationValue S (boolean_realize_bounded_term v source [])
        (boolean_realize_bounded_term v target []) (boolean_realize_bounded_term v mapping []) := by
  simp [preservesRelation, preservesRelationValue, allSet, lattice.imp]

theorem realize_respectsOrder {n : Nat} (v : dvector S n) (source target mapping : Term n) :
    boolean_realize_bounded_formula v (respectsOrder source target mapping) [] =
      respectsOrderValue S (boolean_realize_bounded_term v source [])
        (boolean_realize_bounded_term v target []) (boolean_realize_bounded_term v mapping []) := by
  simp [respectsOrder, respectsOrderValue, allSet, bd_biimp, lattice.imp]

theorem realize_avoidsEdges {n : Nat} (v : dvector S n) (blue mapping : Term n) :
    boolean_realize_bounded_formula v (avoidsEdges blue mapping) [] =
      avoidsEdgesValue S (boolean_realize_bounded_term v blue [])
        (boolean_realize_bounded_term v mapping []) := by
  simp [avoidsEdges, avoidsEdgesValue, allSet, lattice.imp]

theorem realize_blueCopy {n : Nat} (v : dvector S n) (vertices host edges blue : Term n) :
    boolean_realize_bounded_formula v (blueCopy vertices host edges blue) [] =
      blueCopyValue S (boolean_realize_bounded_term v vertices [])
        (boolean_realize_bounded_term v host []) (boolean_realize_bounded_term v edges [])
        (boolean_realize_bounded_term v blue []) := by
  simp [blueCopy, blueCopyValue, existsSet, realize_functionFrom, realize_injective,
    realize_preservesRelation]

theorem realize_redCopy {n : Nat} (v : dvector S n)
    (redDomain host redOrder hostOrder blue : Term n) :
    boolean_realize_bounded_formula v (redCopy redDomain host redOrder hostOrder blue) [] =
      redCopyValue S (boolean_realize_bounded_term v redDomain [])
        (boolean_realize_bounded_term v host []) (boolean_realize_bounded_term v redOrder [])
        (boolean_realize_bounded_term v hostOrder []) (boolean_realize_bounded_term v blue []) := by
  simp [redCopy, redCopyValue, existsSet, realize_functionFrom, realize_injective,
    realize_respectsOrder, realize_avoidsEdges]

end Erdos597Object
