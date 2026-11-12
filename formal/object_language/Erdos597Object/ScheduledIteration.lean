import Erdos597Object.RequirementCodes
import Erdos597Object.GenericFilterModel

set_option backward.isDefEq.respectTransparency false

/-! The scheduled successor selector, with a trivial step when a code is inapplicable. -/

namespace Erdos597Object.ScheduledIteration

open Set Cardinal CanonicalIteration IterationSystems SystemRestrictions TransfiniteSystems
open BooleanIteration IterationNameTransport
open scoped Cardinal

abbrev Labels : Type := (ℵ₁ : Cardinal.{0}).out

theorem labels_card : #Labels = ℵ₁ := Cardinal.mk_out _

def endpoint (j : Index) : Iic j := ⟨j, Set.mem_Iic.mpr (le_refl j)⟩

def trivialPoset (A : Algebra) : BooleanPoset A PUnit where
  member _ := ⊤
  leValue _ _ := ⊤
  le_members _ _ := by simp
  reflexive _ := le_rfl
  transitive _ _ _ := by simp
  antisymmetric i j hij := False.elim (hij (Subsingleton.elim i j))

theorem trivial_boolean_ccc (A : Algebra) : BooleanCountableChainCondition (trivialPoset A) := by
  intro J label weight _ hincompatible
  refine ⟨fun _ => weight, ?_, ?_⟩
  · intro n i j hij
    simpa only [BooleanIteration.compatibleValue, trivialPoset, inf_top_eq, iSup_const] using!
      hincompatible i j hij
  · intro i
    exact le_iSup (fun _ : ℕ => weight i) 0

def trivialStep (A : Algebra) : NextStep A where
  Labels := PUnit
  forcing := trivialPoset A
  ccc := two_step_ccc A.ccc (trivialPoset A) (trivial_boolean_ccc A)
  card_le := Cardinal.mk_le_aleph0.trans (Cardinal.aleph0_le_aleph 1)
  cover := by simp only [trivialPoset, iSup_const]

noncomputable def selectedRequirement (j : Index) (S : Prefix j) :
    Option (BooleanPoset (S.system.obj (endpoint j)) Labels ×
      (Labels → Labels → S.system.obj (endpoint j))) := by
  classical
  exact if h : (BookkeepingSchedule.schedule j).1 ≤ j then
    let earlier : Iic j := ⟨(BookkeepingSchedule.schedule j).1, Set.mem_Iic.mpr h⟩
    let transition := S.system.map earlier (endpoint j) h
    (RequirementCodes.requirementAt (S.system.obj earlier).card_le labels_card.le labels_card.le
      (BookkeepingSchedule.schedule j).2).map
        (fun requirement => (mapPoset transition requirement.1,
          fun d i => transition (requirement.2 d i)))
  else none

noncomputable def guardedStep (A : Algebra)
    (requirement : Option (BooleanPoset A Labels × (Labels → Labels → A))) : NextStep A := by
  classical
  exact match requirement with
  | none => trivialStep A
  | some data =>
    if h : MartinTransport.CountableChainCondition (Condition data.1) ∧
        (⨆ i, data.1.member i) = ⊤ then
      { Labels := Labels
        forcing := data.1
        ccc := h.1
        card_le := labels_card.le
        cover := h.2 }
    else trivialStep A

theorem guardedStep_good (A : Algebra) (P : BooleanPoset A Labels)
    (dense : Labels → Labels → A)
    (hccc : MartinTransport.CountableChainCondition (Condition P))
    (hcover : (⨆ i, P.member i) = ⊤) :
    guardedStep A (some (P, dense)) =
      ({ Labels := Labels, forcing := P, ccc := hccc,
         card_le := labels_card.le, cover := hcover } : NextStep A) := by
  classical
  unfold guardedStep
  dsimp only
  rw [dite_eq_left ⟨hccc, hcover⟩]

theorem guardedStep_none (A : Algebra) : guardedStep A none = trivialStep A := rfl

noncomputable def next (j : Index) (S : Prefix j) : NextStep (S.system.obj (endpoint j)) :=
  guardedStep (S.system.obj (endpoint j)) (selectedRequirement j S)

noncomputable def system : System Index := CanonicalIteration.iteration next

theorem system_continuous : ExtensionContinuity.Continuous system.map :=
  CanonicalIteration.iteration_continuous next

noncomputable def finalAlgebra : Algebra := CanonicalIteration.finalAlgebra next

end Erdos597Object.ScheduledIteration
