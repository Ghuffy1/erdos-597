import Erdos597Object.BooleanPosetCoding

set_option backward.isDefEq.respectTransparency false

/-! Two-step CCC from the literal first-order CCC formula in the set model. -/

namespace Erdos597Object.BooleanCCCBridge

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open Erdos597Object.BooleanIteration Erdos597Object.BooleanPosetCoding

variable {B I : Type} [CompleteBooleanAlgebra B]

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

theorem ccc_formula_value (P : BooleanPoset B I) (element : I → bSet B) :
    boolean_realize_bounded_formula (S := V B)
      (orderName P element :: domainName P element :: [])
      (countableChainCondition var1 var0) [] =
        countableChainConditionValue (V B) (domainName P element) (orderName P element) := by
  rw [realize_countableChainCondition]
  simp [var0, var1]

theorem two_step_ccc_of_formula (hB : Flypitch.BA_CCC B) (P : BooleanPoset B I)
    (element : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (V B).eq (element i) (element j) = ⊥)
    (hccc : ⊤ ≤ boolean_realize_bounded_formula (S := V B)
      (orderName P element :: domainName P element :: [])
      (countableChainCondition var1 var0) []) :
    Erdos597Object.MartinTransport.CountableChainCondition (Condition P) := by
  rw [ccc_formula_value] at hccc
  exact two_step_ccc_of_firstOrder hB P element hdiscrete hccc

theorem two_step_ccc_check_formula (hB : Flypitch.BA_CCC B) (P : BooleanPoset B I)
    (hccc : ⊤ ≤ boolean_realize_bounded_formula (S := V B)
      (orderName P checkLabel :: domainName P checkLabel :: [])
      (countableChainCondition var1 var0) []) :
    Erdos597Object.MartinTransport.CountableChainCondition (Condition P) := by
  rw [ccc_formula_value] at hccc
  exact two_step_ccc_checkLabels hB P hccc

end Erdos597Object.BooleanCCCBridge
