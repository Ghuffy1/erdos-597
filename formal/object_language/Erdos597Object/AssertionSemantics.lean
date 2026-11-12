import Erdos597Object.OrdinalSemantics

set_option backward.isDefEq.respectTransparency false

/-! Boolean-valued interpretation of the complete finite-target sentence. -/

namespace Erdos597Object

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC

universe u

variable {B : Type u} [CompleteBooleanAlgebra B]
variable (S : bStructure L_ZFC B)

local notation "[]" => dvector.nil

def finiteAssertionValue : B :=
  ⨅ kappa : S, ⨅ host : S, ⨅ redDomain : S, ⨅ hostOrder : S, ⨅ redOrder : S,
    (omegaOneValue S kappa ⊓
      (cartesianProductValue S kappa kappa host ⊓
        (cartesianProductValue S (S.fun_map ZFCFunc.omega []) kappa redDomain ⊓
          (lexOrderValue S host hostOrder ⊓ lexOrderValue S redDomain redOrder))))ᶜ ⊔
      finitePartitionValue S host redDomain hostOrder redOrder

theorem realize_finiteAssertion :
    boolean_realize_sentence S finiteAssertion = finiteAssertionValue S := by
  change boolean_realize_bounded_formula (S := S) [] finiteAssertion [] = _
  simp [finiteAssertion, finiteAssertionValue, allSet, realize_omegaOne,
    realize_cartesianProduct, realize_lexOrder, realize_finitePartition, lattice.imp]

end Erdos597Object
