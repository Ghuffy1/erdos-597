import Erdos597Object.LimitEmbeddings
import Erdos597Object.CompletionCardinality
import Erdos597Object.BooleanLimitCCC

set_option backward.isDefEq.respectTransparency false

/-! Small families in a high-cofinality Boolean completion come from one earlier stage. -/

namespace Erdos597Object.StageCapture

open Set Cardinal
open scoped Cardinal
open BooleanDirectLimit PosetCompletion LimitEmbeddings

theorem range_bounded_of_card_lt_cof {J A : Type} [LinearOrder J] [Nonempty J]
    (f : A → J) (hA : #A < Order.cof J) : ∃ j, ∀ a, f a ≤ j := by
  have hnot : ¬ IsCofinal (Set.range f) := by
    intro hcofinal
    exact hA.not_ge ((Order.cof_le hcofinal).trans Cardinal.mk_range_le)
  obtain ⟨j, hj⟩ := not_isCofinal_iff.mp hnot
  exact ⟨j, fun a => (hj (f a) ⟨a, rfl⟩).le⟩

variable {J : Type} [LinearOrder J] [Nonempty J]
  {B : J → Type} [∀ j, CompleteBooleanAlgebra (B j)]
  (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
  [DirectedSystem B (e · · ·)]
  (hinj : ∀ i j h, Function.Injective (e i j h))

theorem completion_element_at_stage
    (hccc : MartinTransport.CountableChainCondition (Condition e))
    (hcof : ℵ₀ < Order.cof J) (b : Completion (Condition e)) :
    ∃ (j : J) (a : B j), stageHom e hinj j a = b := by
  classical
  obtain ⟨A, hA, hb⟩ := countable_join_representation hccc principal
    principal_compatible_iff principal_dense b
  let raw : A → RawCondition e := fun p => representative e p.val
  have hcard : #A ≤ ℵ₀ := Cardinal.le_aleph0_iff_set_countable.mpr hA
  obtain ⟨j, hj⟩ := range_bounded_of_card_lt_cof (fun p : A => (raw p).index)
    (hcard.trans_lt hcof)
  refine ⟨j, ⨆ p : A, e (raw p).index j (hj p) (raw p).value, ?_⟩
  rw [map_iSup]
  calc
    (⨆ p : A, stageHom e hinj j (e (raw p).index j (hj p) (raw p).value)) =
        ⨆ p : A, principal p.val := by
      apply iSup_congr
      intro p
      rw [← stageHom_coherent e hinj (hj p)]
      rw [stageHom_principal e hinj (raw p).index (raw p).value (raw p).nonzero]
      change principal (ofRaw e (raw p)) = principal p.val
      rw [show ofRaw e (raw p) = p.val from ofRaw_representative e p.val]
    _ = b := hb.symm

theorem completion_family_at_stage {A : Type}
    (hccc : MartinTransport.CountableChainCondition (Condition e))
    (hcof : ℵ₀ < Order.cof J) (hA : #A < Order.cof J)
    (values : A → Completion (Condition e)) :
    ∃ (j : J) (earlier : A → B j), ∀ a, stageHom e hinj j (earlier a) = values a := by
  classical
  choose index value hvalue using fun a => completion_element_at_stage e hinj hccc hcof (values a)
  obtain ⟨j, hj⟩ := range_bounded_of_card_lt_cof index hA
  refine ⟨j, fun a => e (index a) j (hj a) (value a), ?_⟩
  intro a
  exact (stageHom_coherent e hinj (hj a) (value a)).symm.trans (hvalue a)

theorem completion_small_family_at_stage {A : Type}
    (hB : ∀ j, Flypitch.BA_CCC (B j)) (hcof : ℵ₁ < Order.cof J)
    (hA : #A ≤ ℵ₁) (values : A → Completion (Condition e)) :
    ∃ (j : J) (earlier : A → B j), ∀ a, stageHom e hinj j (earlier a) = values a :=
  completion_family_at_stage e hinj (BooleanLimitCCC.ccc_of_large_cofinality e hinj hB hcof)
    (Cardinal.aleph0_lt_aleph_one.trans hcof) (hA.trans_lt hcof) values

end Erdos597Object.StageCapture
