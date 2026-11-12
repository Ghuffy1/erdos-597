import Erdos597Object.StageCapture
import Erdos597Object.IterationNameTransport

set_option backward.isDefEq.respectTransparency false

/-! Capturing the coefficients of a small Boolean-valued poset and a family of subsets. -/

namespace Erdos597Object.PosetStageCapture

open Set Cardinal
open scoped Cardinal
open BooleanDirectLimit PosetCompletion LimitEmbeddings

theorem coefficient_index_card_le {I D : Type} (hI : #I ≤ ℵ₁) (hD : #D ≤ ℵ₁) :
    #(I ⊕ ((I × I) ⊕ (D × I))) ≤ ℵ₁ := by
  have hinfinite : ℵ₀ ≤ ℵ₁ := Cardinal.aleph0_le_aleph 1
  have hII : #(I × I) ≤ ℵ₁ := by
    calc
      #(I × I) = #I * #I := by simp only [Cardinal.mk_prod, Cardinal.lift_id]
      _ ≤ ℵ₁ * ℵ₁ := mul_le_mul' hI hI
      _ = ℵ₁ := Cardinal.mul_eq_self hinfinite
  have hDI : #(D × I) ≤ ℵ₁ := by
    calc
      #(D × I) = #D * #I := by simp only [Cardinal.mk_prod, Cardinal.lift_id]
      _ ≤ ℵ₁ * ℵ₁ := mul_le_mul' hD hI
      _ = ℵ₁ := Cardinal.mul_eq_self hinfinite
  calc
    #(I ⊕ ((I × I) ⊕ (D × I))) = #I + (#(I × I) + #(D × I)) := by
      simp only [Cardinal.mk_sum, Cardinal.lift_id]
    _ ≤ ℵ₁ + (ℵ₁ + ℵ₁) := add_le_add hI (add_le_add hII hDI)
    _ = ℵ₁ := by rw [Cardinal.add_eq_self hinfinite, Cardinal.add_eq_self hinfinite]

theorem booleanPoset_ext {A I : Type} [CompleteBooleanAlgebra A]
    {P Q : BooleanIteration.BooleanPoset A I}
    (hm : P.member = Q.member) (ho : P.leValue = Q.leValue) : P = Q := by
  cases P
  cases Q
  cases hm
  cases ho
  rfl

theorem ccc_reflected {A C I : Type} [CompleteBooleanAlgebra A]
    [CompleteBooleanAlgebra C] (f : CompleteLatticeHom A C)
    (hf : Function.Injective f) (P : BooleanIteration.BooleanPoset A I)
    (hccc : MartinTransport.CountableChainCondition
      (BooleanIteration.Condition (IterationNameTransport.mapPoset f P))) :
    MartinTransport.CountableChainCondition (BooleanIteration.Condition P) := by
  intro antichain hanti
  let g := IterationNameTransport.mapCondition f hf P
  have hg : Function.Injective g := IterationNameTransport.mapCondition_injective f hf P
  have himage : (g '' antichain).Pairwise
      (fun p q => ¬ ∃ r, r ≤ p ∧ r ≤ q) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hpq hcompatible
    apply hanti hp hq (fun h => hpq (congrArg g h))
    exact (IterationNameTransport.mapCondition_compatible_iff f hf P p q).mp hcompatible
  have hmaps : Set.MapsTo g antichain (g '' antichain) := fun p hp => ⟨p, hp, rfl⟩
  exact hmaps.countable_of_injOn hg.injOn (hccc _ himage)

variable {J : Type} [LinearOrder J] [Nonempty J]
  {B : J → Type} [∀ j, CompleteBooleanAlgebra (B j)]
  (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
  [DirectedSystem B (e · · ·)]
  (hinj : ∀ i j h, Function.Injective (e i j h))

theorem coefficients_at_stage {I D : Type}
    (hB : ∀ j, Flypitch.BA_CCC (B j)) (hcof : ℵ₁ < Order.cof J)
    (hI : #I ≤ ℵ₁) (hD : #D ≤ ℵ₁)
    (members : I → Completion (Condition e))
    (order : I → I → Completion (Condition e))
    (dense : D → I → Completion (Condition e)) :
    ∃ (j : J) (members' : I → B j) (order' : I → I → B j) (dense' : D → I → B j),
      (∀ i, stageHom e hinj j (members' i) = members i) ∧
      (∀ i k, stageHom e hinj j (order' i k) = order i k) ∧
      (∀ d i, stageHom e hinj j (dense' d i) = dense d i) := by
  let values : I ⊕ ((I × I) ⊕ (D × I)) → Completion (Condition e) :=
    Sum.elim members (Sum.elim (fun ij => order ij.1 ij.2) (fun di => dense di.1 di.2))
  obtain ⟨j, earlier, h⟩ := StageCapture.completion_small_family_at_stage e hinj hB hcof
    (coefficient_index_card_le hI hD) values
  exact ⟨j, (fun i => earlier (Sum.inl i)),
    (fun i k => earlier (Sum.inr (Sum.inl (i, k)))),
    (fun d i => earlier (Sum.inr (Sum.inr (d, i)))),
    (fun i => h (Sum.inl i)), (fun i k => h (Sum.inr (Sum.inl (i, k)))),
    (fun d i => h (Sum.inr (Sum.inr (d, i))))⟩

theorem poset_and_family_at_stage {I D : Type}
    (hB : ∀ j, Flypitch.BA_CCC (B j)) (hcof : ℵ₁ < Order.cof J)
    (hI : #I ≤ ℵ₁) (hD : #D ≤ ℵ₁)
    (P : BooleanIteration.BooleanPoset (Completion (Condition e)) I)
    (dense : D → I → Completion (Condition e)) :
    ∃ (j : J) (earlier : BooleanIteration.BooleanPoset (B j) I) (dense' : D → I → B j),
      IterationNameTransport.mapPoset (stageHom e hinj j) earlier = P ∧
      ∀ d i, stageHom e hinj j (dense' d i) = dense d i := by
  obtain ⟨j, members, order, dense', hm, ho, hd⟩ :=
    coefficients_at_stage e hinj hB hcof hI hD P.member P.leValue dense
  let f := stageHom e hinj j
  have hf : Function.Injective f := stageHom_injective e hinj j
  let earlier : BooleanIteration.BooleanPoset (B j) I := {
    member := members
    leValue := order
    le_members := by
      intro i k
      apply (BooleanNameTransport.map_le_iff f hf _ _).mp
      change stageHom e hinj j (order i k) ≤ stageHom e hinj j (members i ⊓ members k)
      rw [map_inf, ho, hm, hm]
      exact P.le_members i k
    reflexive := by
      intro i
      apply (BooleanNameTransport.map_le_iff f hf _ _).mp
      change stageHom e hinj j (members i) ≤ stageHom e hinj j (order i i)
      rw [hm, ho]
      exact P.reflexive i
    transitive := by
      intro i k l
      apply (BooleanNameTransport.map_le_iff f hf _ _).mp
      change stageHom e hinj j (order i k ⊓ order k l) ≤ stageHom e hinj j (order i l)
      rw [map_inf, ho, ho, ho]
      exact P.transitive i k l
    antisymmetric := by
      intro i k hik
      apply hf
      change stageHom e hinj j (order i k ⊓ order k i) = stageHom e hinj j ⊥
      rw [map_inf, map_bot, ho, ho]
      exact P.antisymmetric i k hik }
  refine ⟨j, earlier, dense', ?_, hd⟩
  apply booleanPoset_ext
  · funext i
    exact hm i
  · funext i k
    exact ho i k

theorem cover_top_reflected {I : Type} {j : J}
    (P : BooleanIteration.BooleanPoset (B j) I)
    (hcover : (⨆ i, (IterationNameTransport.mapPoset (stageHom e hinj j) P).member i) = ⊤) :
    (⨆ i, P.member i) = ⊤ := by
  apply stageHom_injective e hinj j
  rw [map_iSup, map_top]
  exact hcover

theorem ccc_poset_and_family_at_stage {I D : Type}
    (hB : ∀ j, Flypitch.BA_CCC (B j)) (hcof : ℵ₁ < Order.cof J)
    (hI : #I ≤ ℵ₁) (hD : #D ≤ ℵ₁)
    (P : BooleanIteration.BooleanPoset (Completion (Condition e)) I)
    (hP : MartinTransport.CountableChainCondition (BooleanIteration.Condition P))
    (hcover : (⨆ i, P.member i) = ⊤)
    (dense : D → I → Completion (Condition e)) :
    ∃ (j : J) (earlier : BooleanIteration.BooleanPoset (B j) I) (dense' : D → I → B j),
      IterationNameTransport.mapPoset (stageHom e hinj j) earlier = P ∧
      MartinTransport.CountableChainCondition (BooleanIteration.Condition earlier) ∧
      (⨆ i, earlier.member i) = ⊤ ∧
      ∀ d i, stageHom e hinj j (dense' d i) = dense d i := by
  obtain ⟨j, earlier, dense', hposet, hdense⟩ :=
    poset_and_family_at_stage e hinj hB hcof hI hD P dense
  refine ⟨j, earlier, dense', hposet, ?_, ?_, hdense⟩
  · apply ccc_reflected (stageHom e hinj j) (stageHom_injective e hinj j) earlier
    cases hposet
    exact hP
  · apply cover_top_reflected e hinj earlier
    cases hposet
    exact hcover

end Erdos597Object.PosetStageCapture
