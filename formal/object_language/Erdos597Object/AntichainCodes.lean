import Erdos597Object.IterationCardinals

set_option backward.isDefEq.respectTransparency false

/-!
Countable subsets and antichain families admit countable sequence codes.
These bounds control the number of names for small forcing requirements.
-/

namespace Erdos597Object.AntichainCodes

open Cardinal Set
open scoped Cardinal
open Erdos597Object.MartinTransport Erdos597Object.IterationCardinals

def sequenceSupport {P : Type} (s : ℕ → Option P) : Set P :=
  Option.some ⁻¹' Set.range s

theorem sequenceSupport_countable {P : Type} (s : ℕ → Option P) :
    (sequenceSupport s).Countable :=
  (Set.countable_range s).preimage (Option.some_injective P)

theorem exists_sequenceSupport {P : Type} (A : Set P) (hA : A.Countable) :
    ∃ s : ℕ → Option P, sequenceSupport s = A := by
  classical
  by_cases hne : A.Nonempty
  · obtain ⟨f, hf⟩ := hA.exists_eq_range hne
    refine ⟨fun n => some (f n), ?_⟩
    rw [hf]
    ext x
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Option.some.inj hn⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, rfl⟩
  · have hempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨fun _ => none, ?_⟩
    rw [hempty]
    ext x
    simp [sequenceSupport]

def CountableSubsets (P : Type) := {A : Set P // A.Countable}

def decodeSequence {P : Type} (s : ℕ → Option P) : CountableSubsets P :=
  ⟨sequenceSupport s, sequenceSupport_countable s⟩

theorem decodeSequence_surjective (P : Type) :
    Function.Surjective (@decodeSequence P) := by
  rintro ⟨A, hA⟩
  obtain ⟨s, hs⟩ := exists_sequenceSupport A hA
  exact ⟨s, Subtype.ext hs⟩

theorem countableSubsets_card_le {P : Type} (hP : #P ≤ iterationSize) :
    #(CountableSubsets P) ≤ iterationSize := by
  apply (Cardinal.mk_le_of_surjective (decodeSequence_surjective P)).trans
  apply function_card_le (option_card_le hP)
  simpa only [Cardinal.mk_nat] using (Cardinal.aleph0_le_aleph 1)

theorem countable_families_card_le {P I : Type}
    (hP : #P ≤ iterationSize) (hI : #I ≤ ℵ₁) :
    #(I → CountableSubsets P) ≤ iterationSize :=
  function_card_le (countableSubsets_card_le hP) hI

def AntichainFamilies (P I : Type) [PartialOrder P] :=
  {A : I → Set P // ∀ i, (A i).Pairwise (fun p q => ¬ ∃ r : P, r ≤ p ∧ r ≤ q)}

theorem antichain_families_card_le {P I : Type} [PartialOrder P]
    (hccc : CountableChainCondition P) (hP : #P ≤ iterationSize) (hI : #I ≤ ℵ₁) :
    #(AntichainFamilies P I) ≤ iterationSize := by
  let code : AntichainFamilies P I → I → CountableSubsets P :=
    fun A i => ⟨A.val i, hccc (A.val i) (A.property i)⟩
  have hinjective : Function.Injective code := by
    intro A B h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  exact (Cardinal.mk_le_of_injective hinjective).trans (countable_families_card_le hP hI)

end Erdos597Object.AntichainCodes
