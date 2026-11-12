import Erdos597Object.PosetCompletionCCC

set_option backward.isDefEq.respectTransparency false

/-! Cardinal bounds for a Boolean completion with a small dense forcing poset. -/

namespace Erdos597Object.PosetCompletion

open Set Cardinal
open scoped Cardinal
open Erdos597Object.MartinTransport Erdos597Object.IterationCardinals
open Erdos597Object.AntichainCodes

variable {P B : Type} [PartialOrder P] [CompleteBooleanAlgebra B]

def joinOfSubset (image : P → B) (A : Set P) : B := ⨆ p : A, image p.val

theorem countable_join_representation (hP : CountableChainCondition P) (image : P → B)
    (hcompatible : ∀ p q, (∃ r : P, r ≤ p ∧ r ≤ q) ↔ image p ⊓ image q ≠ ⊥)
    (hdense : ∀ b : B, b ≠ ⊥ → ∃ p : P, image p ≤ b) (b : B) :
    ∃ A : Set P, A.Countable ∧ b = joinOfSubset image A := by
  classical
  let families : Set (Set P) :=
    {A | (∀ p ∈ A, image p ≤ b) ∧
      A.Pairwise (fun p q => ¬ ∃ r : P, r ≤ p ∧ r ≤ q)}
  have hchain : ∀ c ⊆ families, IsChain (· ⊆ ·) c →
      ∃ upper ∈ families, ∀ A ∈ c, A ⊆ upper := by
    intro c hc hcc
    refine ⟨⋃₀ c, ?_, fun A hA => Set.subset_sUnion_of_mem hA⟩
    constructor
    · rintro p ⟨A, hA, hp⟩
      exact (hc hA).1 p hp
    · rintro p ⟨A, hA, hp⟩ q ⟨C, hC, hq⟩ hpq
      obtain rfl | hne := eq_or_ne A C
      · exact (hc hA).2 hp hq hpq
      · rcases hcc hA hC hne with hAC | hCA
        · exact (hc hC).2 (hAC hp) hq hpq
        · exact (hc hA).2 hp (hCA hq) hpq
  obtain ⟨A, hA⟩ := zorn_subset families hchain
  have hcountable : A.Countable := hP A hA.prop.2
  have hbelow : joinOfSubset image A ≤ b := by
    apply iSup_le
    intro p
    exact hA.prop.1 p.val p.property
  have habove : b ≤ joinOfSubset image A := by
    by_contra hnot
    have hnonzero : b ⊓ (joinOfSubset image A)ᶜ ≠ ⊥ := by
      intro hzero
      apply hnot
      simpa using le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr hzero)
    obtain ⟨p, hp⟩ := hdense _ hnonzero
    have hincompatible : ∀ q ∈ A, ¬ ∃ r : P, r ≤ p ∧ r ≤ q := by
      intro q hq hcommon
      apply (hcompatible p q).mp hcommon
      apply bot_unique
      calc
        image p ⊓ image q ≤ (joinOfSubset image A)ᶜ ⊓ joinOfSubset image A :=
          inf_le_inf (hp.trans inf_le_right) (le_iSup (fun r : A => image r.val) ⟨q, hq⟩)
        _ = ⊥ := compl_inf_self (joinOfSubset image A)
    have hnew : insert p A ∈ families := by
      constructor
      · rintro q (rfl | hq)
        · exact hp.trans inf_le_left
        · exact hA.prop.1 q hq
      · rintro q (rfl | hq) r (rfl | hr) hqr
        · exact False.elim (hqr rfl)
        · exact hincompatible r hr
        · rintro ⟨s, hsq, hsp⟩
          exact hincompatible q hq ⟨s, hsp, hsq⟩
        · exact hA.prop.2 hq hr hqr
    have hpA : p ∈ A := hA.2 hnew (Set.subset_insert p A) (Set.mem_insert p A)
    exact hincompatible p hpA ⟨p, le_rfl, le_rfl⟩
  exact ⟨A, hcountable, le_antisymm habove hbelow⟩

theorem dense_boolean_algebra_card_le (hP : CountableChainCondition P) (image : P → B)
    (hcompatible : ∀ p q, (∃ r : P, r ≤ p ∧ r ≤ q) ↔ image p ⊓ image q ≠ ⊥)
    (hdense : ∀ b : B, b ≠ ⊥ → ∃ p : P, image p ≤ b)
    (hcard : #P ≤ iterationSize) : #B ≤ iterationSize := by
  let decode : CountableSubsets P → B := fun A => joinOfSubset image A.val
  have hsurjective : Function.Surjective decode := by
    intro b
    obtain ⟨A, hA, hb⟩ := countable_join_representation hP image hcompatible hdense b
    exact ⟨⟨A, hA⟩, hb.symm⟩
  exact (Cardinal.mk_le_of_surjective hsurjective).trans (countableSubsets_card_le hcard)

theorem completion_card_le (hP : CountableChainCondition P) (hcard : #P ≤ iterationSize) :
    #(Completion P) ≤ iterationSize :=
  dense_boolean_algebra_card_le hP principal principal_compatible_iff principal_dense hcard

theorem two_step_card_le {I : Type} (Q : BooleanIteration.BooleanPoset B I)
    (hB : #B ≤ iterationSize) (hI : #I ≤ ℵ₁) :
    #(BooleanIteration.Condition Q) ≤ iterationSize := by
  have hinjective : Function.Injective
      (fun p : BooleanIteration.Condition Q => (p.value, p.label)) := by
    intro p q hpq
    exact BooleanIteration.condition_ext (congrArg Prod.fst hpq) (congrArg Prod.snd hpq)
  calc
    #(BooleanIteration.Condition Q) ≤ #(B × I) := Cardinal.mk_le_of_injective hinjective
    _ = #B * #I := by simp only [Cardinal.mk_prod, Cardinal.lift_id]
    _ ≤ iterationSize * iterationSize := mul_le_mul' hB (hI.trans aleph_one_lt_iterationSize.le)
    _ = iterationSize := Cardinal.mul_eq_self iterationSize_infinite

theorem two_step_completion_card_le {I : Type} (Q : BooleanIteration.BooleanPoset B I)
    (hccc : CountableChainCondition (BooleanIteration.Condition Q))
    (hB : #B ≤ iterationSize) (hI : #I ≤ ℵ₁) :
    #(Completion (BooleanIteration.Condition Q)) ≤ iterationSize :=
  completion_card_le hccc (two_step_card_le Q hB hI)

end Erdos597Object.PosetCompletion
