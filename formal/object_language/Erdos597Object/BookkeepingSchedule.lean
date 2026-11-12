import Erdos597Object.CanonicalIteration

set_option backward.isDefEq.respectTransparency false

/-! A schedule that revisits every stage and requirement code arbitrarily late. -/

namespace Erdos597Object.BookkeepingSchedule

open Set Cardinal CanonicalIteration IterationCardinals
open scoped Cardinal Ordinal

theorem initial_segment_card_lt (i : Index) : #(Iic i) < iterationSize := by
  have hinitial : Cardinal.ord #Index = typeLT Index := by
    rw [index_card]
    exact (Ordinal.type_toType iterationSize.ord).symm
  have hinfinite : ℵ₀ ≤ #Index := by rw [index_card]; exact iterationSize_infinite
  exact (Cardinal.mk_Iic_lt i hinitial hinfinite).trans_eq index_card

theorem triple_card : #(Index × Index × Index) = iterationSize := by
  simp only [Cardinal.mk_prod, Cardinal.lift_id, index_card]
  rw [Cardinal.mul_eq_self iterationSize_infinite, Cardinal.mul_eq_self iterationSize_infinite]

noncomputable def tripleEquiv : Index ≃ (Index × Index × Index) :=
  Classical.choice (Cardinal.eq.mp (index_card.trans triple_card.symm))

noncomputable def schedule (i : Index) : Index × Index :=
  ((tripleEquiv i).1, (tripleEquiv i).2.1)

theorem schedule_fibre (stage code rank : Index) :
    schedule (tripleEquiv.symm (stage, code, rank)) = (stage, code) := by
  simp only [schedule, Equiv.apply_symm_apply]

theorem cofinally_scheduled (stage code bound : Index) :
    ∃ i, bound < i ∧ schedule i = (stage, code) := by
  classical
  by_contra h
  let fibre : Index → Index := fun rank => tripleEquiv.symm (stage, code, rank)
  have hfibre : Function.Injective fibre := by
    intro i j hij
    have h := congrArg tripleEquiv hij
    simpa only [fibre, Equiv.apply_symm_apply, Prod.mk.injEq, true_and] using h
  have hbound (rank : Index) : fibre rank ≤ bound := by
    apply le_of_not_gt
    intro hlt
    exact h ⟨fibre rank, hlt, schedule_fibre stage code rank⟩
  let into : Index → Iic bound := fun rank => ⟨fibre rank, hbound rank⟩
  have hinj : Function.Injective into := fun i j hij => hfibre (congrArg Subtype.val hij)
  have hcard : iterationSize ≤ #(Iic bound) := by
    simpa only [index_card] using Cardinal.mk_le_of_injective hinj
  exact (initial_segment_card_lt bound).not_ge hcard

theorem scheduled_after_stage (stage code bound : Index) :
    ∃ i, stage < i ∧ bound < i ∧ schedule i = (stage, code) := by
  obtain ⟨i, hi, hs⟩ := cofinally_scheduled stage code (max stage bound)
  exact ⟨i, lt_of_le_of_lt (le_max_left _ _) hi,
    lt_of_le_of_lt (le_max_right _ _) hi, hs⟩

end Erdos597Object.BookkeepingSchedule
