import Erdos597Object.OrdinalPresentation

set_option backward.isDefEq.respectTransparency false

/-! Interpretation of the complete finite-target partition formula. -/

namespace Erdos597Object

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC

universe u

variable {B : Type u} [CompleteBooleanAlgebra B]
variable (S : bStructure L_ZFC B)

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

@[simp] theorem realize_omega {n : ℕ} (v : dvector S n) :
    boolean_realize_bounded_term v (omega : Term n) [] = S.fun_map ZFCFunc.omega [] := by
  simp only [Flypitch.ZFC.omega, bd_const, bd_func,
    Flypitch.fol.bfol.boolean_realize_bounded_term]

def finitePartitionValue (host redDomain hostOrder redOrder : S) : B :=
  ⨅ vertices : S, (memberValue S vertices (S.fun_map ZFCFunc.omega []))ᶜ ⊔
    ⨅ edges : S, (graphValue S vertices edges ⊓ cliqueFreeFourValue S vertices edges)ᶜ ⊔
      ⨅ blue : S, (graphValue S host blue)ᶜ ⊔
        (redCopyValue S redDomain host redOrder hostOrder blue ⊔
          blueCopyValue S vertices host edges blue)

theorem realize_finitePartition {n : ℕ} (v : dvector S n)
    (host redDomain hostOrder redOrder : Term n) :
    boolean_realize_bounded_formula v (finitePartition host redDomain hostOrder redOrder) [] =
      finitePartitionValue S (boolean_realize_bounded_term v host [])
        (boolean_realize_bounded_term v redDomain [])
        (boolean_realize_bounded_term v hostOrder [])
        (boolean_realize_bounded_term v redOrder []) := by
  simp [finitePartition, finitePartitionValue, allMember, allSet, realize_graph,
    realize_cliqueFreeFour, realize_redCopy, realize_blueCopy, lattice.imp]

end Erdos597Object
