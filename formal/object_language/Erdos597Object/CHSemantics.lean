import Erdos597Object.OrdinalSemantics

set_option backward.isDefEq.respectTransparency false

/-! Interpret the continuum-hypothesis sentence used by the set-theory library. -/

namespace Erdos597Object

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC

universe u

variable {B : Type u} [CompleteBooleanAlgebra B]
variable (S : bStructure L_ZFC B)

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

def powersetValue (x : S) : S := S.fun_map ZFCFunc.powerset (x :: [])

@[simp] theorem realize_powerset {n : ℕ} (v : dvector S n) (x : Term n) :
    boolean_realize_bounded_term v (powerset x) [] =
      powersetValue S (boolean_realize_bounded_term v x []) := by
  simp only [powerset, powersetValue, bd_apps, bd_app, bd_func,
    boolean_realize_bounded_term, boolean_realize_bounded_term_mk_fst]
  rfl

def functionalityValue (relation : S) : B :=
  ⨅ x : S, ⨅ y : S, ⨅ a : S, ⨅ b : S,
    (edgeValue S relation x a ⊓ edgeValue S relation y b)ᶜ ⊔
      ((S.eq x y)ᶜ ⊔ S.eq a b)

@[simp] theorem realize_originalFunction (relation : S) :
    boolean_realize_bounded_formula (S := S) (relation :: []) isFuncF [] =
      functionalityValue S relation := by
  simp [isFuncF, functionalityValue, edgeValue, var0, var1, var2, var3, var4, lattice.imp]

@[simp] theorem realize_originalTotalRev (domain codomain relation : S) :
    boolean_realize_bounded_formula (S := S) (relation :: domain :: codomain :: []) isTotalRevF [] =
      totalOnValue S domain codomain relation := by
  simp [isTotalRevF, totalOnValue, edgeValue, var0, var1, var2, var3, var4, lattice.imp]

@[simp] theorem realize_originalFunction_cast3 (domain codomain relation : S) :
    boolean_realize_bounded_formula (S := S) (relation :: domain :: codomain :: [])
      (isFuncF.cast (by omega : 1 ≤ 3)) [] = functionalityValue S relation := by
  simp [dvector.take]

@[simp] theorem realize_originalFunctionFromRev (domain codomain relation : S) :
    boolean_realize_bounded_formula (S := S) (relation :: domain :: codomain :: []) isFuncPrimeRevF [] =
      functionalityValue S relation ⊓ totalOnValue S domain codomain relation := by
  simp [isFuncPrimeRevF]

@[simp] theorem realize_originalFunctionFromRev_cast4 (extra domain codomain relation : S) :
    boolean_realize_bounded_formula (S := S) (relation :: domain :: codomain :: extra :: [])
      (isFuncPrimeRevF.cast (by omega : 3 ≤ 4)) [] =
      functionalityValue S relation ⊓ totalOnValue S domain codomain relation := by
  simp [dvector.take]

def surjectiveOnValue (domain codomain relation : S) : B :=
  ⨅ y : S, (memberValue S y codomain)ᶜ ⊔
    ⨆ x : S, memberValue S x domain ⊓ edgeValue S relation x y

def surjectsSubsetValue (domain codomain : S) : B :=
  ⨆ subset : S, ⨆ relation : S,
    (subsetValue S subset domain ⊓
      (functionalityValue S relation ⊓ totalOnValue S subset codomain relation)) ⊓
      surjectiveOnValue S subset codomain relation

@[simp] theorem realize_originalAtMost (domain codomain : S) :
    boolean_realize_bounded_formula (S := S) (codomain :: domain :: []) atMostF [] =
      surjectsSubsetValue S domain codomain := by
  simp [atMostF, surjectsSubsetValue, surjectiveOnValue, realize_subset, edgeValue,
    var0, var1, var2, var3, lattice.imp]

@[simp] theorem realize_originalAtMostOmega (x : S) :
    boolean_realize_bounded_formula (S := S) (x :: []) atMostOmegaF [] =
      surjectsSubsetValue S (S.fun_map ZFCFunc.omega []) x := by
  simp [atMostOmegaF, surjectsSubsetValue, surjectiveOnValue, realize_subset, edgeValue,
    var0, var1, var2, var3, lattice.imp]

@[simp] theorem realize_originalFunctionFromPowersetOmega (domain relation x : S) :
    boolean_realize_bounded_formula (S := S) (relation :: domain :: x :: [])
      isFuncPrimePowersetOmegaRevF [] =
      functionalityValue S relation ⊓
        totalOnValue S domain (powersetValue S (S.fun_map ZFCFunc.omega [])) relation := by
  simp [isFuncPrimePowersetOmegaRevF, totalOnValue, edgeValue,
    var0, var1, var2, lattice.imp]

@[simp] theorem realize_originalAtMostPowersetOmega (x : S) :
    boolean_realize_bounded_formula (S := S) (x :: []) atMostPowersetOmegaF [] =
      surjectsSubsetValue S x (powersetValue S (S.fun_map ZFCFunc.omega [])) := by
  simp [atMostPowersetOmegaF, surjectsSubsetValue, surjectiveOnValue, realize_subset, edgeValue,
    var0, var1, var2, var3, lattice.imp]

def continuumHypothesisValue : B :=
  ⨅ x : S, (ordinalValue S x)ᶜ ⊔
    (surjectsSubsetValue S (S.fun_map ZFCFunc.omega []) x ⊔
      surjectsSubsetValue S x (powersetValue S (S.fun_map ZFCFunc.omega [])))

theorem realize_originalCH :
    boolean_realize_sentence S CH_f = continuumHypothesisValue S := by
  change boolean_realize_bounded_formula (S := S) [] CH_f [] = _
  simp [CH_f, continuumHypothesisValue, realize_ordinal, lattice.imp]

end Erdos597Object
