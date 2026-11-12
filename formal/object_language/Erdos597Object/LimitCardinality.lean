import Erdos597Object.BooleanLimitCCC

set_option backward.isDefEq.respectTransparency false

/-! The size bounds for direct limits and their Boolean completions. -/

namespace Erdos597Object.LimitCardinality

open Cardinal
open scoped Cardinal
open BooleanDirectLimit IterationCardinals MartinTransport

variable {ι : Type} [Preorder ι] [IsDirectedOrder ι]
  {B : ι → Type} [∀ i, CompleteBooleanAlgebra (B i)]
  (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
  [DirectedSystem B (e · · ·)]

theorem rawCondition_card_le (hI : #ι ≤ iterationSize)
    (hB : ∀ i, #(B i) ≤ iterationSize) : #(RawCondition e) ≤ iterationSize := by
  classical
  obtain ⟨indices⟩ : Nonempty (ι ↪ iterationSize.out) :=
    (Cardinal.le_def _ _).mp (by simpa only [Cardinal.mk_out] using hI)
  have hcodes : ∀ i, Nonempty (B i ↪ iterationSize.out) := by
    intro i
    exact (Cardinal.le_def _ _).mp (by simpa only [Cardinal.mk_out] using hB i)
  let codes : ∀ i, B i ↪ iterationSize.out := fun i => Classical.choice (hcodes i)
  let encode : RawCondition e → iterationSize.out × iterationSize.out :=
    fun p => (indices p.index, codes p.index p.value)
  have hinjective : Function.Injective encode := by
    rintro ⟨i, b, hb⟩ ⟨j, c, hc⟩ h
    have hij : i = j := indices.injective (congrArg Prod.fst h)
    subst j
    have hbc : b = c := (codes i).injective (congrArg Prod.snd h)
    subst c
    rfl
  calc
    #(RawCondition e) ≤ #(iterationSize.out × iterationSize.out) :=
      Cardinal.mk_le_of_injective hinjective
    _ = iterationSize * iterationSize := by
      simp only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_out]
    _ = iterationSize := Cardinal.mul_eq_self iterationSize_infinite

theorem condition_card_le (hI : #ι ≤ iterationSize)
    (hB : ∀ i, #(B i) ≤ iterationSize) : #(Condition e) ≤ iterationSize := by
  have hsurjective : Function.Surjective (ofRaw e) := exists_ofRaw e
  exact (Cardinal.mk_le_of_surjective hsurjective).trans (rawCondition_card_le e hI hB)

theorem completion_card_le (hI : #ι ≤ iterationSize)
    (hB : ∀ i, #(B i) ≤ iterationSize) (hccc : CountableChainCondition (Condition e)) :
    #(PosetCompletion.Completion (Condition e)) ≤ iterationSize :=
  PosetCompletion.completion_card_le hccc (condition_card_le e hI hB)

theorem completion_card_le_of_countable_cofinal
    (hinj : ∀ i j h, Function.Injective (e i j h))
    (hI : #ι ≤ iterationSize) (hB : ∀ i, #(B i) ≤ iterationSize)
    (hccc : ∀ i, Flypitch.BA_CCC (B i))
    (stages : ℕ → ι) (hcofinal : ∀ i, ∃ n, i ≤ stages n) :
    #(PosetCompletion.Completion (Condition e)) ≤ iterationSize :=
  completion_card_le e hI hB
    (BooleanLimitCCC.ccc_of_countable_cofinal e hinj hccc stages hcofinal)

end Erdos597Object.LimitCardinality
