import Erdos597Object.BooleanIteration
import Flypitch.Forcing

set_option backward.isDefEq.respectTransparency false

/-!
Countable-chain-condition preservation for a Boolean-valued second step.
The countable-cover hypothesis states explicitly the Boolean witness needed
for countability. Its connection to the first-order CCC formula is separate.
-/

namespace Erdos597Object.BooleanIteration

open Set
open Erdos597Object.MartinTransport

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem disjoint_family_support_countable (hB : Flypitch.BA_CCC B)
    {J : Type} (weight : J → B)
    (hdisjoint : ∀ i j, i ≠ j → weight i ⊓ weight j = ⊥) :
    {i | weight i ≠ ⊥}.Countable := by
  let support : Set J := {i | weight i ≠ ⊥}
  have hnonzero : ∀ b ∈ weight '' support, b ≠ ⊥ := by
    rintro b ⟨i, hi, rfl⟩
    exact hi
  have hpair : ∀ a ∈ weight '' support, ∀ b ∈ weight '' support,
      a ≠ b → a ⊓ b = ⊥ := by
    rintro a ⟨i, _, rfl⟩ b ⟨j, _, rfl⟩ hab
    exact hdisjoint i j (fun hij => hab (congrArg weight hij))
  have hcount := hB (weight '' support) hnonzero hpair
  have hinjective : Set.InjOn weight support := by
    intro i hi j _ hij
    by_contra hne
    have hzero := hdisjoint i j hne
    rw [← hij, inf_idem] at hzero
    exact hi hzero
  have hmaps : Set.MapsTo weight support (weight '' support) :=
    fun i hi => ⟨i, hi, rfl⟩
  exact hmaps.countable_of_injOn hinjective hcount

def HasCountableCover {J : Type} (weight : J → B) : Prop :=
  ∃ rows : ℕ → J → B,
    (∀ n i j, i ≠ j → rows n i ⊓ rows n j = ⊥) ∧
      ∀ i, weight i ≤ ⨆ n, rows n i

theorem countable_support_of_cover (hB : Flypitch.BA_CCC B)
    {J : Type} (weight : J → B) (hcover : HasCountableCover weight) :
    {i | weight i ≠ ⊥}.Countable := by
  obtain ⟨rows, hrows, hbound⟩ := hcover
  have hcount : (⋃ n : ℕ, {i | rows n i ≠ ⊥}).Countable :=
    Set.countable_iUnion fun n => disjoint_family_support_countable hB (rows n) (hrows n)
  apply hcount.mono
  intro i hi
  by_contra hnot
  have hzero : ∀ n, rows n i = ⊥ := by
    intro n
    by_contra hne
    exact hnot (Set.mem_iUnion.mpr ⟨n, hne⟩)
  have hle := hbound i
  simp only [hzero, iSup_bot] at hle
  exact hi (bot_unique hle)

def BooleanCountableChainCondition (P : BooleanPoset B I) : Prop :=
  ∀ (J : Type) (label : J → I) (weight : J → B),
    (∀ j, weight j ≤ P.member (label j)) →
    (∀ j k, j ≠ k →
      weight j ⊓ weight k ⊓ compatibleValue P (label j) (label k) = ⊥) →
    HasCountableCover weight

theorem two_step_ccc (hB : Flypitch.BA_CCC B) (P : BooleanPoset B I)
    (hP : BooleanCountableChainCondition P) : CountableChainCondition (Condition P) := by
  intro A hA
  let label : A → I := fun p => p.val.label
  let weight : A → B := fun p => p.val.value
  have hvalid : ∀ p, weight p ≤ P.member (label p) := fun p => p.val.valid
  have hincompatible : ∀ p q : A, p ≠ q →
      weight p ⊓ weight q ⊓ compatibleValue P (label p) (label q) = ⊥ := by
    intro p q hpq
    by_contra hnonzero
    have hne : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
    exact hA p.property q.property hne ((compatible_iff p.val q.val).mpr hnonzero)
  have hcount := countable_support_of_cover hB weight (hP A label weight hvalid hincompatible)
  have hall : {p : A | weight p ≠ ⊥} = Set.univ :=
    Set.eq_univ_of_forall fun p => p.val.nonzero
  rw [hall] at hcount
  haveI : Countable A := Set.countable_univ_iff.mp hcount
  exact Set.to_countable A

end Erdos597Object.BooleanIteration
