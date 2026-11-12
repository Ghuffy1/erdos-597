import Erdos597Object.BooleanUnboundedRows

set_option backward.isDefEq.respectTransparency false

/-! Increasing ground sequences selected inside a column-unbounded Boolean fiber. -/

namespace Erdos597Object.BooleanUnboundedSequences

open Erdos597 Flypitch
open BooleanUnboundedRows

variable {B : Type} [CompleteBooleanAlgebra B]

theorem select_sequence (hB : has_dense_omega_closed_subset B) (context : B)
    (weight : One → B) (lowerBound : One) (hne : context ≠ ⊥)
    (hunbounded : context ≤ unboundedValue weight) :
    ∃ lower : B, lower ≠ ⊥ ∧ lower ≤ context ∧ ∃ sequence : Nat → One,
      StrictMono sequence ∧ (∀ n, lowerBound < sequence n) ∧
      ∀ n, lower ≤ weight (sequence n) := by
  classical
  obtain ⟨D, hD⟩ := hB
  let State := {s : B × One // s.1 ∈ D ∧ s.1 ≤ context ∧
    s.1 ≤ weight s.2 ∧ lowerBound < s.2}
  have next : ∀ (q : B), q ≠ ⊥ → q ≤ context → ∀ bound : One,
      lowerBound ≤ bound → ∃ s : State, s.val.1 ≤ q ∧ bound < s.val.2 := by
    intro q hq hcontext bound hbound
    have hcover : q ≤ ⨆ i : Set.Ioi bound, weight i.val := by
      apply (hcontext.trans (hunbounded.trans (unbounded_le_tail weight bound))).trans
      apply iSup_le
      intro i
      apply iSup_le
      intro hi
      exact le_iSup_of_le ⟨i, hi⟩ le_rfl
    obtain ⟨i, hi⟩ := BooleanWeightedSupports.exists_nonzero_intersection q
      (fun i : Set.Ioi bound => weight i.val) hq hcover
    obtain ⟨r, hr, hle⟩ := hD.1.2 (q ⊓ weight i.val) (bot_lt_iff_ne_bot.mpr hi)
    exact ⟨⟨(r, i.val), hr, (hle.trans inf_le_left).trans hcontext,
      hle.trans inf_le_right, hbound.trans_lt i.property⟩, hle.trans inf_le_left, i.property⟩
  choose step step_le step_gt using next
  let states : Nat → State := Nat.rec
    (step context hne le_rfl lowerBound le_rfl)
    (fun _ previous => step previous.val.1
      (ne_of_gt (nonzero_of_mem_dense_omega_closed_subset hD previous.property.1))
      previous.property.2.1 previous.val.2 previous.property.2.2.2.le)
  have hchain : ∀ n, (states (n + 1)).val.1 ≤ (states n).val.1 := by
    intro n
    exact step_le (states n).val.1
      (ne_of_gt (nonzero_of_mem_dense_omega_closed_subset hD (states n).property.1))
      (states n).property.2.1 (states n).val.2 (states n).property.2.2.2.le
  have hstrict : StrictMono (fun n => (states n).val.2) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact step_gt (states n).val.1
      (ne_of_gt (nonzero_of_mem_dense_omega_closed_subset hD (states n).property.1))
      (states n).property.2.1 (states n).val.2 (states n).property.2.2.2.le
  let lower := ⨅ n, (states n).val.1
  have hpositive : ⊥ < lower := nonzero_infi_of_mem_dense_omega_closed_subset hD hchain
    (fun n => (states n).property.1)
  refine ⟨lower, ne_of_gt hpositive,
    (iInf_le (fun n => (states n).val.1) 0).trans (states 0).property.2.1,
    fun n => (states n).val.2, hstrict, fun n => (states n).property.2.2.2, ?_⟩
  intro n
  exact (iInf_le (fun n => (states n).val.1) n).trans (states n).property.2.2.1

noncomputable def sequenceCover (weight : One → B) (lowerBound : One) : B :=
  ⨆ sequence : Nat → One, ⨆ (_ : StrictMono sequence ∧ ∀ n, lowerBound < sequence n),
    ⨅ n, weight (sequence n)

theorem increasing_sequences_cover (hB : has_dense_omega_closed_subset B)
    (weight : One → B) (lowerBound : One) :
    unboundedValue weight ≤ sequenceCover weight lowerBound := by
  classical
  by_contra hnot
  let context := unboundedValue weight ⊓ (sequenceCover weight lowerBound)ᶜ
  have hne : context ≠ ⊥ := by
    intro hzero
    apply hnot
    have hle : unboundedValue weight ≤ (sequenceCover weight lowerBound)ᶜᶜ :=
      (le_compl_iff_disjoint_right).mpr (disjoint_iff.mpr hzero)
    simpa only [compl_compl] using hle
  obtain ⟨lower, hlower, hbase, sequence, hstrict, habove, hweights⟩ :=
    select_sequence hB context weight lowerBound hne inf_le_left
  have hin : lower ≤ sequenceCover weight lowerBound :=
    le_iSup_of_le sequence (le_iSup_of_le ⟨hstrict, habove⟩ (le_iInf hweights))
  exact hlower (bot_unique ((le_inf hin (hbase.trans inf_le_right)).trans_eq inf_compl_eq_bot))

end Erdos597Object.BooleanUnboundedSequences
