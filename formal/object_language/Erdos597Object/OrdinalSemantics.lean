import Erdos597Object.PartitionSemantics

set_option backward.isDefEq.respectTransparency false

/-! Boolean-valued interpretations of ordinals and the first uncountable ordinal. -/

namespace Erdos597Object

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC

universe u

variable {B : Type u} [CompleteBooleanAlgebra B]
variable (S : bStructure L_ZFC B)

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

local instance : Nonempty S := ⟨S.fun_map ZFCFunc.emptyset []⟩

@[simp] theorem realize_variable {n : ℕ} (v : dvector S n) (i : Fin n) :
    boolean_realize_bounded_term v (var i) [] = v.nth i.val i.isLt := by
  simp only [Flypitch.ZFC.var, bd_var, Flypitch.fol.bfol.boolean_realize_bounded_term]

@[simp] theorem realize_emptyset {n : ℕ} (v : dvector S n) :
    boolean_realize_bounded_term v (emptyset : Term n) [] =
      S.fun_map ZFCFunc.emptyset [] := by
  simp only [Flypitch.ZFC.emptyset, bd_const, bd_func,
    Flypitch.fol.bfol.boolean_realize_bounded_term]

def subsetValue (x y : S) : B :=
  ⨅ z : S, (memberValue S z x)ᶜ ⊔ memberValue S z y

theorem realize_subset {n : ℕ} (v : dvector S n) (x y : Term n) :
    boolean_realize_bounded_formula v (subsetF x y) [] =
      subsetValue S (boolean_realize_bounded_term v x [])
        (boolean_realize_bounded_term v y []) := by
  simp [subsetF, subsetValue, lattice.imp]

def transitiveValue (x : S) : B :=
  ⨅ y : S, (memberValue S y x)ᶜ ⊔ subsetValue S y x

def trichotomyValue (x : S) : B :=
  ⨅ y : S, (memberValue S y x)ᶜ ⊔
    ⨅ z : S, (memberValue S z x)ᶜ ⊔
      ((S.eq y z ⊔ memberValue S y z) ⊔ memberValue S z y)

def wellFoundedValue (x : S) : B :=
  ⨅ y : S, (subsetValue S y x)ᶜ ⊔
    (S.eq y (S.fun_map ZFCFunc.emptyset []) ⊔
      ⨆ z : S, memberValue S z y ⊓
        ⨅ w : S, (memberValue S w y)ᶜ ⊔ (memberValue S w z)ᶜ)

def ordinalValue (x : S) : B :=
  (trichotomyValue S x ⊓ wellFoundedValue S x) ⊓ transitiveValue S x

theorem realize_transitive (x : S) :
    boolean_realize_bounded_formula (S := S) (x :: []) isTransitiveF [] =
      transitiveValue S x := by
  simp [isTransitiveF, transitiveValue, realize_subset, var0, var1, lattice.imp]

theorem realize_trichotomy (x : S) :
    boolean_realize_bounded_formula (S := S) (x :: []) epsilonTrichotomyF [] =
      trichotomyValue S x := by
  simp [epsilonTrichotomyF, trichotomyValue, var0, var1, var2, lattice.imp]

theorem realize_wellFounded (x : S) :
    boolean_realize_bounded_formula (S := S) (x :: []) epsilonWellFoundedF [] =
      wellFoundedValue S x := by
  simp [epsilonWellFoundedF, wellFoundedValue, realize_subset,
    var0, var1, var2, lattice.imp]

theorem realize_ordinal (x : S) :
    boolean_realize_bounded_formula (S := S) (x :: []) OrdF [] = ordinalValue S x := by
  simp [OrdF, ewoF, ordinalValue, realize_trichotomy, realize_wellFounded, realize_transitive]

theorem realize_isOrdinal {n : ℕ} (v : dvector S n) (x : Term n) :
    boolean_realize_bounded_formula v (isOrdinal x) [] =
      ordinalValue S (boolean_realize_bounded_term v x []) := by
  rw [isOrdinal, boolean_realize_bounded_formula_subst_open,
    Flypitch.fol.bfol.boolean_realize_bounded_formula_cast]
  simpa [dvector.take] using realize_ordinal S (boolean_realize_bounded_term v x [])

def injectsIntoValue (x y : S) : B :=
  ⨆ relation : S, functionFromValue S x y relation ⊓ injectiveValue S relation

theorem realize_injectsInto {n : ℕ} (v : dvector S n) (x y : Term n) :
    boolean_realize_bounded_formula v (injectsInto x y) [] =
      injectsIntoValue S (boolean_realize_bounded_term v x [])
        (boolean_realize_bounded_term v y []) := by
  simp [injectsInto, injectsIntoValue, existsSet, realize_functionFrom, realize_injective]

def omegaOneValue (kappa : S) : B :=
  ordinalValue S kappa ⊓
    ((injectsIntoValue S kappa (S.fun_map ZFCFunc.omega []))ᶜ ⊓
      ⨅ alpha : S, (memberValue S alpha kappa)ᶜ ⊔
        injectsIntoValue S alpha (S.fun_map ZFCFunc.omega []))

theorem realize_omegaOne {n : ℕ} (v : dvector S n) (kappa : Term n) :
    boolean_realize_bounded_formula v (omegaOne kappa) [] =
      omegaOneValue S (boolean_realize_bounded_term v kappa []) := by
  simp [omegaOne, omegaOneValue, realize_isOrdinal, realize_injectsInto,
    allMember, allSet, lattice.imp]

end Erdos597Object
