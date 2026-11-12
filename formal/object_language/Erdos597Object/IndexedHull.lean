import Erdos597Object.SmallMartin

set_option backward.isDefEq.respectTransparency false

/-! A small index type for closure under one binary operation and an indexed family of unary operations. -/

namespace Erdos597Object.IndexedHull

open Cardinal
open scoped Cardinal

universe u

def Stage (I : Type) : ℕ → Type
  | 0 => PUnit
  | n + 1 => Stage I n ⊕ ((Stage I n × Stage I n) ⊕ (I × Stage I n))

def Labels (I : Type) : Type := Σ n, Stage I n

def evaluateStage {I : Type} {X : Type u} (seed : X) (combine : X → X → X)
    (step : I → X → X) : (n : ℕ) → Stage I n → X
  | 0, _ => seed
  | n + 1, Sum.inl a => evaluateStage seed combine step n a
  | n + 1, Sum.inr (Sum.inl (a, b)) =>
    combine (evaluateStage seed combine step n a) (evaluateStage seed combine step n b)
  | n + 1, Sum.inr (Sum.inr (i, a)) => step i (evaluateStage seed combine step n a)

def evaluate {I : Type} {X : Type u} (seed : X) (combine : X → X → X)
    (step : I → X → X) (label : Labels I) : X :=
  evaluateStage seed combine step label.1 label.2

theorem evaluateStage_property {I : Type} {X : Type u}
    (seed : X) (combine : X → X → X) (step : I → X → X) (property : X → Prop)
    (hseed : property seed) (hcombine : ∀ x y, property x → property y → property (combine x y))
    (hstep : ∀ i x, property x → property (step i x)) :
    ∀ n label, property (evaluateStage seed combine step n label) := by
  intro n
  induction n with
  | zero => exact fun _ => hseed
  | succ n ih =>
    intro label
    rcases label with a | (⟨a, b⟩ | ⟨i, a⟩)
    · exact ih a
    · exact hcombine _ _ (ih a) (ih b)
    · exact hstep i _ (ih a)

theorem evaluateStage_lift {I : Type} {X : Type u}
    (seed : X) (combine : X → X → X) (step : I → X → X)
    {n m : ℕ} (hnm : n ≤ m) (label : Stage I n) :
    ∃ raised : Stage I m, evaluateStage seed combine step m raised = evaluateStage seed combine step n label := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero => exact ⟨label, rfl⟩
  | succ k ih =>
    obtain ⟨raised, hraised⟩ := ih
    exact ⟨Sum.inl raised, hraised⟩

theorem evaluate_seed {I : Type} {X : Type u}
    (seed : X) (combine : X → X → X) (step : I → X → X) :
    ∃ label : Labels I, evaluate seed combine step label = seed :=
  ⟨⟨0, PUnit.unit⟩, rfl⟩

theorem evaluate_combine {I : Type} {X : Type u}
    (seed : X) (combine : X → X → X) (step : I → X → X) (a b : Labels I) :
    ∃ label : Labels I, evaluate seed combine step label =
      combine (evaluate seed combine step a) (evaluate seed combine step b) := by
  obtain ⟨a', ha⟩ := evaluateStage_lift seed combine step (Nat.le_max_left a.1 b.1) a.2
  obtain ⟨b', hb⟩ := evaluateStage_lift seed combine step (Nat.le_max_right a.1 b.1) b.2
  refine ⟨⟨max a.1 b.1 + 1, Sum.inr (Sum.inl (a', b'))⟩, ?_⟩
  change combine (evaluateStage seed combine step _ a') (evaluateStage seed combine step _ b') = _
  rw [ha, hb]
  rfl

theorem evaluate_step {I : Type} {X : Type u}
    (seed : X) (combine : X → X → X) (step : I → X → X) (i : I) (a : Labels I) :
    ∃ label : Labels I, evaluate seed combine step label = step i (evaluate seed combine step a) :=
  ⟨⟨a.1 + 1, Sum.inr (Sum.inr (i, a.2))⟩, rfl⟩

theorem stage_card_le {I : Type} (hI : #I ≤ ℵ₁) : ∀ n, #(Stage I n) ≤ ℵ₁ := by
  intro n
  induction n with
  | zero => simpa [Stage] using one_le_aleph0.trans (aleph0_le_aleph 1)
  | succ n ih =>
    change #(Stage I n ⊕ ((Stage I n × Stage I n) ⊕ (I × Stage I n))) ≤ ℵ₁
    rw [mk_sum, mk_sum, mk_prod, mk_prod]
    simp only [Cardinal.lift_id]
    have hsquare : #(Stage I n) * #(Stage I n) ≤ ℵ₁ :=
      (mul_le_mul' ih ih).trans_eq (mul_eq_self (aleph0_le_aleph 1))
    have hindexed : #I * #(Stage I n) ≤ ℵ₁ :=
      (mul_le_mul' hI ih).trans_eq (mul_eq_self (aleph0_le_aleph 1))
    exact (add_le_add ih ((add_le_add hsquare hindexed).trans_eq
      (add_eq_self (aleph0_le_aleph 1)))).trans_eq (add_eq_self (aleph0_le_aleph 1))

theorem labels_card_le {I : Type} (hI : #I ≤ ℵ₁) : #(Labels I) ≤ ℵ₁ := by
  change #(Σ n, Stage I n) ≤ ℵ₁
  rw [mk_sigma]
  calc
    sum (fun n => #(Stage I n)) ≤ #ℕ * ⨆ n, #(Stage I n) := sum_le_mk_mul_iSup _
    _ ≤ ℵ₁ * ℵ₁ := mul_le_mul' (by simp) (ciSup_le' (stage_card_le hI))
    _ = ℵ₁ := mul_eq_self (aleph0_le_aleph 1)

theorem labels_card_ge (I : Type) : #I ≤ #(Labels I) := by
  let embed : I → Labels I := fun i => ⟨1, Sum.inr (Sum.inr (i, PUnit.unit))⟩
  apply Cardinal.mk_le_of_injective (f := embed)
  intro i j hij
  change (⟨1, Sum.inr (Sum.inr (i, PUnit.unit))⟩ : Labels I) =
    ⟨1, Sum.inr (Sum.inr (j, PUnit.unit))⟩ at hij
  have hparts : (Sum.inr (Sum.inr (i, PUnit.unit)) : Stage I 1) =
      Sum.inr (Sum.inr (j, PUnit.unit)) := eq_of_heq (Sigma.mk.inj hij).2
  exact congrArg Prod.fst (Sum.inr.inj (Sum.inr.inj hparts))

theorem labels_card_eq {I : Type} (hI : #I = ℵ₁) : #(Labels I) = ℵ₁ :=
  le_antisymm (labels_card_le hI.le) (hI.symm.trans_le (labels_card_ge I))

end Erdos597Object.IndexedHull
