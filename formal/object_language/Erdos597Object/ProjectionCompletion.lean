import Erdos597Object.BooleanProjection

set_option backward.isDefEq.respectTransparency false

/-! Extending a Boolean projection on a forcing poset to its regular-open completion. -/

namespace Erdos597Object.ProjectionCompletion

open Set TopologicalSpace Flypitch
open Topology.WithLowerSet
open PosetCompletion

structure PosetProjection (B P : Type) [CompleteBooleanAlgebra B] [PartialOrder P] where
  value : P → B
  nonzero : ∀ p, value p ≠ ⊥
  monotone : Monotone value
  condition : (b : B) → b ≠ ⊥ → P
  condition_value : ∀ b hb, value (condition b hb) = b
  compatible : ∀ p b hb, (∃ q, q ≤ p ∧ q ≤ condition b hb) ↔ value p ⊓ b ≠ ⊥

variable {B P : Type} [CompleteBooleanAlgebra B] [PartialOrder P]
  (R : PosetProjection B P)

def valueOpen (b : B) : Set (Topology.WithLowerSet P) :=
  {p | R.value (ofLowerSet p) ≤ b}

theorem valueOpen_open (b : B) : IsOpen (valueOpen R b) := by
  apply Topology.IsLowerSet.isOpen_iff_isLowerSet.mpr
  intro p q hpq hq
  exact (R.monotone hpq).trans hq

theorem valueOpen_perp (b : B) : (valueOpen R b)ᵖ = valueOpen R bᶜ := by
  classical
  ext p
  rw [show p = toLowerSet (ofLowerSet p) from rfl, CompletionEmbedding.mem_perp_lower_iff]
  change (∀ q : P, q ≤ ofLowerSet p → ¬ R.value q ≤ b) ↔ R.value (ofLowerSet p) ≤ bᶜ
  constructor
  · intro hp
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff.mpr
    by_contra hnonzero
    let d := R.value (ofLowerSet p) ⊓ b
    have hd : d ≠ ⊥ := hnonzero
    have hcompatible : R.value (ofLowerSet p) ⊓ d ≠ ⊥ := by
      simpa only [d, ← inf_assoc, inf_idem] using hd
    obtain ⟨q, hqp, hqd⟩ := (R.compatible (ofLowerSet p) d hd).mpr hcompatible
    apply hp q hqp
    have hvalue := R.monotone hqd
    rw [R.condition_value] at hvalue
    exact hvalue.trans inf_le_right
  · intro hp q hqp hqb
    apply R.nonzero q
    apply bot_unique
    calc
      R.value q ≤ b ⊓ bᶜ := le_inf hqb ((R.monotone hqp).trans hp)
      _ = ⊥ := inf_compl_self b

theorem valueOpen_regular (b : B) : is_regular (valueOpen R b) := by
  apply regular_iff_p_p.mpr
  rw [valueOpen_perp, valueOpen_perp, compl_compl]

def algebraMap (b : B) : Completion P := ⟨valueOpen R b, valueOpen_regular R b⟩

theorem algebraMap_monotone : Monotone (algebraMap R) := by
  intro b c hbc p hp
  exact hp.trans hbc

theorem algebraMap_compl (b : B) : algebraMap R bᶜ = (algebraMap R b)ᶜ := by
  apply Subtype.ext
  exact (valueOpen_perp R b).symm

theorem algebraMap_sInf (s : Set B) : algebraMap R (sInf s) = sInf (algebraMap R '' s) := by
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨b, hb, rfl⟩
    exact algebraMap_monotone R (sInf_le hb)
  · intro p hp
    change R.value (ofLowerSet p) ≤ sInf s
    apply le_sInf
    intro b hb
    have hbelow : sInf (algebraMap R '' s) ≤ algebraMap R b := sInf_le ⟨b, hb, rfl⟩
    exact hbelow hp

theorem algebraMap_sSup (s : Set B) : algebraMap R (sSup s) = sSup (algebraMap R '' s) := by
  have himages : algebraMap R '' (Compl.compl '' s) = Compl.compl '' (algebraMap R '' s) := by
    ext d
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨algebraMap R b, ⟨b, hb, rfl⟩, (algebraMap_compl R b).symm⟩
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨bᶜ, ⟨b, hb, rfl⟩, algebraMap_compl R b⟩
  apply compl_injective
  rw [← algebraMap_compl, compl_sSup', algebraMap_sInf, compl_sSup', himages]

def completeHom : CompleteLatticeHom B (Completion P) where
  toFun := algebraMap R
  map_sInf' := algebraMap_sInf R
  map_sSup' := algebraMap_sSup R

theorem algebraMap_le_iff (b c : B) : algebraMap R b ≤ algebraMap R c ↔ b ≤ c := by
  constructor
  · intro hbc
    by_contra hnot
    have hd : b ⊓ cᶜ ≠ ⊥ := by
      intro hzero
      apply hnot
      simpa using le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr hzero)
    have hpoint : R.value (R.condition (b ⊓ cᶜ) hd) ≤ b := by
      rw [R.condition_value]
      exact inf_le_left
    have hbound : R.value (R.condition (b ⊓ cᶜ) hd) ≤ c :=
      hbc (a := toLowerSet (R.condition (b ⊓ cᶜ) hd)) hpoint
    rw [R.condition_value] at hbound
    apply hd
    apply bot_unique
    calc
      b ⊓ cᶜ ≤ c ⊓ cᶜ := le_inf hbound inf_le_right
      _ = ⊥ := inf_compl_self c
  · intro hbc
    exact algebraMap_monotone R hbc

theorem completeHom_injective : Function.Injective (completeHom R) := by
  intro b c heq
  exact le_antisymm ((algebraMap_le_iff R b c).mp heq.le)
    ((algebraMap_le_iff R c b).mp heq.ge)

theorem principal_condition_le (b : B) (hb : b ≠ ⊥) :
    principal (R.condition b hb) ≤ algebraMap R b := by
  apply is_regular_stable_subset (valueOpen_regular R b)
  intro q hq
  change R.value (ofLowerSet q) ≤ b
  exact (R.monotone (show ofLowerSet q ≤ R.condition b hb from hq)).trans_eq
    (R.condition_value b hb)

end Erdos597Object.ProjectionCompletion
