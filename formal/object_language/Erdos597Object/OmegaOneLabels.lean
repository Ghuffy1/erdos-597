import Erdos597Object.BooleanOrdinalBridge
import Erdos597Object.BooleanSetRelabeling
import Erdos597Object.SmallNameMartin

set_option backward.isDefEq.respectTransparency false

/-! Label the checked first uncountable ordinal by the bookkeeping index type. -/

namespace Erdos597Object.OmegaOneLabels

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet Ordinal
open BooleanSets BooleanFunctionBridge BooleanSetRelabeling ScheduledIteration

noncomputable def indexEquiv : Labels ≃ (ω₁ : Ordinal.{0}).toPSet.Type :=
  Classical.choice (Cardinal.eq.mp (by
    rw [labels_card]
    simp))

noncomputable def element {B : Type} [CompleteBooleanAlgebra B] (i : Labels) : bSet B :=
  bSet.check ((ω₁ : Ordinal.{0}).toPSet.Func (indexEquiv i))

variable {B : Type} [CompleteBooleanAlgebra B]

theorem element_discrete (i j : Labels) (hij : i ≠ j) :
    (element (B := B) i =ᴮ element j) = ⊥ :=
  ordinal_elements_discrete _ _ _ (fun h => hij (indexEquiv.injective h))

theorem labelSet_eq_check :
    ⊤ ≤ weightedSet (element (B := B)) (fun _ => ⊤) =ᴮ
      bSet.check (ω₁ : Ordinal.{0}).toPSet := by
  have h := weighted_relabel (B := B) indexEquiv
    (fun i => bSet.check ((ω₁ : Ordinal.{0}).toPSet.Func i)) (fun _ => ⊤)
  simpa only [← check_weighted] using! h

theorem injection_to_labels {context : B} (domain : bSet B)
    (h : context ≤ injectsIntoValue (V B) domain (bSet.check (ω₁ : Ordinal.{0}).toPSet)) :
    context ≤ injectsIntoValue (V B) domain (weightedSet (element (B := B)) (fun _ => ⊤)) := by
  rw [injectsInto_eq_injects_into] at h ⊢
  have heq := bSet.bv_symm (labelSet_eq_check (B := B))
  exact (le_inf (le_top.trans heq) h).trans
    (bSet.B_ext_injects_into_right (y := domain) _ _)

theorem injection_of_omegaOne (hB : Flypitch.BA_CCC B) {context : B}
    (kappa domain : bSet B) (hkappa : context ≤ omegaOneValue (V B) kappa)
    (h : context ≤ injectsIntoValue (V B) domain kappa) :
    context ≤ injectsIntoValue (V B) domain (weightedSet (element (B := B)) (fun _ => ⊤)) := by
  apply injection_to_labels domain
  rw [injectsInto_eq_injects_into] at h ⊢
  exact (le_inf (BooleanOrdinalBridge.omegaOneValue_unique hB kappa hkappa) h).trans
    (bSet.B_ext_injects_into_right (y := domain) _ _)

theorem small_omegaOne_filter_exists (context : ScheduledIteration.finalAlgebra)
    (kappa domain relation family : bSet ScheduledIteration.finalAlgebra)
    (hkappa : context ≤ omegaOneValue (V ScheduledIteration.finalAlgebra) kappa)
    (hdomain : context ≤ injectsIntoValue (V ScheduledIteration.finalAlgebra) domain kappa)
    (hfamily : context ≤ injectsIntoValue (V ScheduledIteration.finalAlgebra) family kappa)
    (hnonempty : context ≤ nonemptyValue (V ScheduledIteration.finalAlgebra) domain)
    (horder : context ≤ partialOrderValue (V ScheduledIteration.finalAlgebra) domain relation)
    (hccc : context ≤ countableChainConditionValue (V ScheduledIteration.finalAlgebra) domain relation)
    (hdense : context ≤ ⨅ subset : bSet ScheduledIteration.finalAlgebra,
      lattice.imp (subset ∈ᴮ family) (denseValue (V ScheduledIteration.finalAlgebra) domain relation subset)) :
    context ≤ ⨆ filter : bSet ScheduledIteration.finalAlgebra,
      orderFilterValue (V ScheduledIteration.finalAlgebra) domain relation filter ⊓
        meetsFamilyValue (V ScheduledIteration.finalAlgebra) filter family :=
  SmallNameMartin.small_names_filter_exists context domain relation family element element_discrete
    (injection_of_omegaOne ScheduledIteration.finalAlgebra.ccc kappa domain hkappa hdomain)
    (injection_of_omegaOne ScheduledIteration.finalAlgebra.ccc kappa family hkappa hfamily)
    hnonempty horder hccc hdense

end Erdos597Object.OmegaOneLabels
