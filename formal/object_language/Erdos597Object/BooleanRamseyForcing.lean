import Erdos597Object.BooleanRamseyTree
import Erdos597Object.BooleanCountableForcing
import Erdos597Object.CodedDensity

set_option backward.isDefEq.respectTransparency false

/-! The countable finite-stem forcing used for Ramsey choices in the positive model. -/

namespace Erdos597Object.BooleanRamseyForcing

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanRamseyTree BooleanIteration BooleanPosetCoding BooleanPosetModel

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def forcing (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B) :
    BooleanPoset B (List Choice) := by
  classical
  refine {
    member := weight arity color initial
    leValue := fun left right => if right.IsPrefix left then weight arity color initial left else ⊥
    le_members := ?_
    reflexive := ?_
    transitive := ?_
    antisymmetric := ?_
  }
  · intro left right
    by_cases h : right.IsPrefix left
    · rw [ite_eq_left h]
      apply le_inf le_rfl
      obtain ⟨extra, rfl⟩ := h
      exact weight_append_le arity color initial right extra
    · simp only [h, ↓reduceIte, bot_le]
  · intro history
    simp only [List.prefix_rfl, ↓reduceIte, le_refl]
  · intro left middle right
    by_cases hleft : middle.IsPrefix left
    · by_cases hright : right.IsPrefix middle
      · have hboth : right.IsPrefix left := hright.trans hleft
        simp only [hleft, hright, hboth, ↓reduceIte]
        exact inf_le_left
      · simp only [hleft, hright, ↓reduceIte, inf_bot_eq, bot_le]
    · simp only [hleft, ↓reduceIte, bot_inf_eq, bot_le]
  · intro left right hne
    by_cases hleft : right.IsPrefix left
    · by_cases hright : left.IsPrefix right
      · exact False.elim (hne (List.IsPrefix.eq_of_length_le hright (List.IsPrefix.length_le hleft)))
      · simp only [hleft, hright, ↓reduceIte, inf_bot_eq]
    · simp only [hleft, ↓reduceIte, bot_inf_eq]

theorem forcing_child (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (history : List Choice) (choice : Choice) :
    (forcing arity color initial).leValue (history ++ [choice]) history =
      weight arity color initial (history ++ [choice]) := by
  simp only [forcing, List.prefix_append, ↓reduceIte]

noncomputable def denseWeight (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (bound : ℕ) (history : List Choice) : B :=
  if ∃ n ∈ (state arity color initial history).1, bound ≤ n then
    weight arity color initial history else ⊥

theorem denseWeight_le (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (bound : ℕ) (history : List Choice) :
    denseWeight arity color initial bound history ≤ (forcing arity color initial).member history := by
  unfold denseWeight
  split_ifs <;> simp only [forcing, le_refl, bot_le]

theorem dense_coefficients (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (bound : ℕ) (history : List Choice) :
    (forcing arity color initial).member history ≤ ⨆ next : List Choice,
      denseWeight arity color initial bound next ⊓ (forcing arity color initial).leValue next history := by
  apply (weight_extensions_above arity color initial history bound).trans
  apply iSup_le
  intro point
  apply iSup_le
  intro hpoint
  apply iSup_le
  intro marked
  apply le_iSup_of_le (history ++ [(point, marked)])
  have hmember : point ∈ (state arity color initial (history ++ [(point, marked)])).1 := by
    rw [state_snoc]
    simp only [step, Finset.mem_insert, true_or]
  have hex : ∃ n ∈ (state arity color initial (history ++ [(point, marked)])).1, bound ≤ n :=
    ⟨point, hmember, hpoint⟩
  rw [forcing_child, denseWeight, ite_eq_left hex]
  exact le_inf le_rfl le_rfl

theorem dense_value (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B) (bound : ℕ) :
    ⊤ ≤ denseValue (V B) (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel)
      (weightedSet checkLabel (denseWeight arity color initial bound)) :=
  CodedDensity.denseValue_of_coefficients _ _
    (denseWeight_le arity color initial bound) (dense_coefficients arity color initial bound)

theorem forcing_countable (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B) :
    ⊤ ≤ injectsIntoValue (V B) (domainName (forcing arity color initial) checkLabel) bSet.omega :=
  BooleanCountableNames.weighted_countable checkLabel (fun _ _ h => checkLabel_discrete h) _

theorem forcing_nonempty (context : B) (arity : ℕ) (color : Finset ℕ → B) (initial : ℕ → B)
    (hinfinite : context ≤ BooleanInfiniteSets.infiniteValue initial) :
    context ≤ nonemptyValue (V B) (domainName (forcing arity color initial) checkLabel) := by
  apply le_iSup_of_le (checkLabel (B := B) ([] : List Choice))
  have hweight : context ≤ (forcing arity color initial).member [] := by
    simpa only [forcing, weight, state, List.foldl_nil] using hinfinite
  exact hweight.trans (weight_le_member checkLabel (forcing arity color initial).member [])

theorem filter_exists (context : ScheduledIteration.finalAlgebra) (arity : ℕ)
    (color : Finset ℕ → ScheduledIteration.finalAlgebra) (initial : ℕ → ScheduledIteration.finalAlgebra)
    (hinfinite : context ≤ BooleanInfiniteSets.infiniteValue initial) :
    ∃ filter : bSet ScheduledIteration.finalAlgebra,
      context ≤ orderFilterValue (V ScheduledIteration.finalAlgebra)
        (domainName (forcing arity color initial) checkLabel)
        (orderName (forcing arity color initial) checkLabel) filter ∧
      ∀ bound : ℕ, context ≤ ⨆ history : List Choice,
        denseWeight arity color initial bound history ⊓ (checkLabel history ∈ᴮ filter) := by
  obtain ⟨filter, hfilter, hmeets⟩ := BooleanCountableForcing.countable_family_filter_exists context
    (domainName (forcing arity color initial) checkLabel)
    (orderName (forcing arity color initial) checkLabel)
    (fun bound => weightedSet checkLabel (denseWeight arity color initial bound))
    (forcing_nonempty context arity color initial hinfinite)
    (le_top.trans (partialOrderValue_checkLabels _))
    (le_top.trans (forcing_countable arity color initial))
    (fun bound => le_top.trans (dense_value arity color initial bound))
  refine ⟨filter, hfilter, ?_⟩
  intro bound
  have heq : (⨆ x : bSet ScheduledIteration.finalAlgebra, (x ∈ᴮ filter) ⊓
      (x ∈ᴮ weightedSet checkLabel (denseWeight arity color initial bound))) =
      ⨆ history : List Choice, denseWeight arity color initial bound history ⊓
        (checkLabel history ∈ᴮ filter) := by
    rw [show (⨆ x : bSet ScheduledIteration.finalAlgebra, (x ∈ᴮ filter) ⊓
        (x ∈ᴮ weightedSet checkLabel (denseWeight arity color initial bound))) =
        (⨆ x : bSet ScheduledIteration.finalAlgebra,
          (x ∈ᴮ weightedSet checkLabel (denseWeight arity color initial bound)) ⊓ (x ∈ᴮ filter)) from
      iSup_congr (fun _ => inf_comm _ _)]
    exact weighted_bounded_exists checkLabel (denseWeight arity color initial bound)
      (fun x => x ∈ᴮ filter) (bSet.B_ext_mem_left filter)
  exact (hmeets bound).trans_eq heq

end Erdos597Object.BooleanRamseyForcing
