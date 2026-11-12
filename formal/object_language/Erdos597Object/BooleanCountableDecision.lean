import Erdos597Object.BooleanWeightedSupports
import Flypitch.Collapse

set_option backward.isDefEq.respectTransparency false

/-! Countable simultaneous decisions from a dense omega-closed Boolean basis. -/

namespace Erdos597Object.BooleanCountableDecision

open Flypitch
open scoped Flypitch.bSet

variable {B I : Type} [CompleteBooleanAlgebra B]

/-- A positive condition can decide countably many choices in ground sets. -/
theorem decide_countably (hB : has_dense_omega_closed_subset B)
    (context : B) (weight : Nat → I → B) (hne : context ≠ ⊥)
    (hcover : ∀ n, context ≤ ⨆ i, weight n i) :
    ∃ lower : B, lower ≠ ⊥ ∧ lower ≤ context ∧
      ∃ choice : Nat → I, ∀ n, lower ≤ weight n (choice n) := by
  classical
  obtain ⟨D, hD⟩ := hB
  let State (n : Nat) := {s : B × I //
    s.1 ∈ D ∧ s.1 ≤ context ∧ s.1 ≤ weight n s.2}
  have next : ∀ (n : Nat) (q : B), q ≠ ⊥ → q ≤ context →
      ∃ s : State n, s.val.1 ≤ q := by
    intro n q hq hcontext
    obtain ⟨i, hi⟩ := BooleanWeightedSupports.exists_nonzero_intersection
      q (weight n) hq (hcontext.trans (hcover n))
    obtain ⟨r, hr, hrle⟩ := hD.1.2 (q ⊓ weight n i) (bot_lt_iff_ne_bot.mpr hi)
    exact ⟨⟨(r, i), hr, (hrle.trans inf_le_left).trans hcontext,
      hrle.trans inf_le_right⟩, hrle.trans inf_le_left⟩
  choose step step_le using next
  let sequence : (n : Nat) → State n := Nat.rec
    (step 0 context hne le_rfl)
    (fun n previous => step (n + 1) previous.val.1
      (ne_of_gt (nonzero_of_mem_dense_omega_closed_subset hD previous.property.1))
      previous.property.2.1)
  have hchain : ∀ n, (sequence (n + 1)).val.1 ≤ (sequence n).val.1 := by
    intro n
    exact step_le (n + 1) (sequence n).val.1
      (ne_of_gt (nonzero_of_mem_dense_omega_closed_subset hD (sequence n).property.1))
      (sequence n).property.2.1
  let lower : B := ⨅ n, (sequence n).val.1
  have hpositive : ⊥ < lower := nonzero_infi_of_mem_dense_omega_closed_subset hD
    hchain (fun n => (sequence n).property.1)
  refine ⟨lower, ne_of_gt hpositive,
    (iInf_le (fun n => (sequence n).val.1) 0).trans (sequence 0).property.2.1,
    fun n => (sequence n).val.2, ?_⟩
  intro n
  exact (iInf_le (fun n => (sequence n).val.1) n).trans (sequence n).property.2.2

/-- The decision lemma also applies to any countable family of requests. -/
theorem decide_countable_family {J : Type} [Countable J]
    (hB : has_dense_omega_closed_subset B) (context : B) (weight : J → I → B)
    (hne : context ≠ ⊥) (hcover : ∀ j, context ≤ ⨆ i, weight j i) :
    ∃ lower : B, lower ≠ ⊥ ∧ lower ≤ context ∧
      ∃ choice : J → I, ∀ j, lower ≤ weight j (choice j) := by
  classical
  cases isEmpty_or_nonempty J with
  | inl h =>
    exact ⟨context, hne, le_rfl, fun j => isEmptyElim j, fun j => isEmptyElim j⟩
  | inr h =>
    obtain ⟨encode, hinjective⟩ := Countable.exists_injective_nat J
    let decode : Nat → J := Function.invFun encode
    have hdecode : ∀ j, decode (encode j) = j := Function.leftInverse_invFun hinjective
    obtain ⟨lower, hlower, hbase, choice, hchoice⟩ := decide_countably hB context
      (fun n => weight (decode n)) hne (fun n => hcover (decode n))
    refine ⟨lower, hlower, hbase, fun j => choice (encode j), ?_⟩
    intro j
    simpa only [hdecode] using hchoice (encode j)

/-- Countably many names in a ground-labelled set have simultaneous ground values locally. -/
theorem reflect_members {J : Type} [Countable J]
    (hB : has_dense_omega_closed_subset B) (context : B) (label : I → bSet B)
    (names : J → bSet B) (hne : context ≠ ⊥)
    (hmembers : ∀ j, context ≤ names j ∈ᴮ BooleanSets.weightedSet label (fun _ => ⊤)) :
    ∃ lower : B, lower ≠ ⊥ ∧ lower ≤ context ∧
      ∃ choice : J → I, ∀ j, lower ≤ names j =ᴮ label (choice j) := by
  have hcover : ∀ j, context ≤ ⨆ i, names j =ᴮ label i := by
    intro j
    simpa only [BooleanSets.member_weightedSet, top_inf_eq] using hmembers j
  exact decide_countable_family hB context (fun j i => names j =ᴮ label i) hne hcover

/-- A constant positive family with a countable disjoint cover has countable index set. -/
theorem countable_of_constant_cover (hB : has_dense_omega_closed_subset B)
    (context : B) (hne : context ≠ ⊥)
    (hcover : BooleanIteration.HasCountableCover (fun _ : I => context)) : Countable I := by
  classical
  obtain ⟨rows, hdisjoint, hrows⟩ := hcover
  let weight : Nat → Option I → B := fun n option => match option with
    | none => (⨆ i, rows n i)ᶜ
    | some i => rows n i
  have hfull : ∀ n, context ≤ ⨆ option, weight n option := by
    intro n
    calc
      context ≤ (⨆ i, rows n i) ⊔ (⨆ i, rows n i)ᶜ := by simp
      _ ≤ ⨆ option, weight n option := sup_le
        (iSup_le fun i => le_iSup_of_le (some i) le_rfl)
        (le_iSup_of_le none le_rfl)
  obtain ⟨lower, hlower, hbase, choice, hchoice⟩ :=
    decide_countably hB context weight hne hfull
  have hcovered : ∀ i : I, ∃ n, choice n = some i := by
    intro i
    by_contra hmissing
    have hzero : ∀ n, lower ⊓ rows n i = ⊥ := by
      intro n
      cases hoption : choice n with
      | none =>
        have hnone : lower ≤ (⨆ j, rows n j)ᶜ := by
          simpa only [hoption, weight] using hchoice n
        exact bot_unique ((le_inf (inf_le_left.trans hnone)
          (inf_le_right.trans (le_iSup (rows n) i))).trans_eq compl_inf_eq_bot)
      | some j =>
        have hji : j ≠ i := by
          intro h
          subst j
          exact hmissing ⟨n, hoption⟩
        have hsome : lower ≤ rows n j := by
          simpa only [hoption, weight] using hchoice n
        exact bot_unique ((le_inf (inf_le_left.trans hsome) inf_le_right).trans_eq
          (hdisjoint n j i hji))
    have hle : lower ≤ ⨆ n, lower ⊓ rows n i := by
      rw [← inf_iSup_eq]
      exact le_inf le_rfl (hbase.trans (hrows i))
    exact hlower (bot_unique (by simpa only [hzero, iSup_bot] using hle))
  choose code hcode using hcovered
  apply Function.Injective.countable (f := code)
  intro i j hij
  apply Option.some.inj
  exact (hcode i).symm.trans ((congrArg choice hij).trans (hcode j))

end Erdos597Object.BooleanCountableDecision
