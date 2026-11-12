import Erdos597Object.BooleanIndependentConditions
import Erdos597Object.ContextualMartinModel

set_option backward.isDefEq.respectTransparency false

/-! Small indexing and filter coefficients for the finite independent-condition forcing. -/

namespace Erdos597Object.BooleanIndependentFilters

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet Cardinal
open BooleanIteration BooleanIndependentConditions BooleanColumns ScheduledIteration PosetRelabeling

theorem vertex_card : #Vertex = ℵ₁ := by
  change #(ℕ × (ℕ × Labels)) = ℵ₁
  rw [Cardinal.mk_prod]
  simp only [Cardinal.lift_id, Cardinal.mk_nat, BooleanOrientedSupport.block_labels_card]
  exact Cardinal.aleph0_mul_aleph 1

theorem conditions_card : #(Finset Vertex) = ℵ₁ := by
  let : Infinite Vertex := Cardinal.infinite_iff.mpr (by
    rw [vertex_card]
    exact Cardinal.aleph0_le_aleph 1)
  rw [Cardinal.mk_finset_of_infinite, vertex_card]

theorem requirements_card : #(ℕ × Erdos597.One) = ℵ₁ := by
  rw [Cardinal.mk_prod]
  simp only [Cardinal.lift_id, Cardinal.mk_nat, Erdos597.one_card]
  exact Cardinal.aleph0_mul_aleph 1

noncomputable def conditionEquiv : Labels ≃ Finset Vertex :=
  Classical.choice (Cardinal.eq.mp (labels_card.trans conditions_card.symm))

noncomputable def requirementEquiv : Labels ≃ ℕ × Erdos597.One :=
  Classical.choice (Cardinal.eq.mp (labels_card.trans requirements_card.symm))

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def denseWeight (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (requirement : ℕ × Erdos597.One) (points : Finset Vertex) : B := by
  classical
  exact if ∃ v ∈ points, v.1 = requirement.1 ∧ requirement.2 < column v.2.2 then
    weight base rows relation cut points else ⊥

theorem denseWeight_le (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (requirement : ℕ × Erdos597.One) (points : Finset Vertex) :
    denseWeight base rows relation cut requirement points ≤ (forcing base rows relation cut).member points := by
  unfold denseWeight
  split_ifs <;> simp only [forcing, le_refl, bot_le]

theorem forcing_cover (base : B) (rows : ℕ → bSet B) (relation : bSet B) (cut : Erdos597.One) :
    (⨆ points, (forcing base rows relation cut).member points) = base := by
  apply le_antisymm (iSup_le fun points => weight_le_base base rows relation cut points)
  apply le_iSup_of_le ∅
  change base ≤ weight base rows relation cut ∅
  rw [weight_empty]

theorem coefficients_of_equivalences {I D : Type}
    (context : finalAlgebra) (P : BooleanPoset finalAlgebra I)
    (index : Labels ≃ I) (requirements : Labels ≃ D)
    (active : D → finalAlgebra) (dense : D → I → finalAlgebra)
    (hP : BooleanCountableChainCondition P) (hcover : (⨆ i, P.member i) = context)
    (hactive : ∀ d, active d ≤ context) (hsubset : ∀ d i, dense d i ≤ P.member i)
    (hdense : ∀ d j, active d ⊓ P.member j ≤ ⨆ i, dense d i ⊓ P.leValue i j) :
    ∃ value : I → finalAlgebra,
      (∀ i, value i ≤ P.member i) ∧ context ≤ (⨆ i, value i) ∧
      (∀ i j, value i ⊓ P.leValue i j ≤ value j) ∧
      (∀ i j, value i ⊓ value j ≤ ⨆ k, value k ⊓ (P.leValue k i ⊓ P.leValue k j)) ∧
      (∀ d, active d ≤ ⨆ i, value i ⊓ dense d i) := by
  let Q := relabel index P
  obtain ⟨value, hvalid, htotal, hup, hdir, hmeets⟩ :=
    ContextualMartinModel.contextual_coefficients context Q (fun d => active (requirements d))
      (fun d i => dense (requirements d) (index i)) (relabel_booleanCCC index P hP)
      ((relabel_members index P).trans hcover) (fun d => hactive (requirements d))
      (fun d i => hsubset (requirements d) (index i)) (by
        intro d j
        exact (hdense (requirements d) (index j)).trans_eq
          (index.surjective.iSup_comp (fun i => dense (requirements d) i ⊓ P.leValue i (index j))).symm)
  refine ⟨fun i => value (index.symm i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [Q, relabel, index.apply_symm_apply] using hvalid (index.symm i)
  · exact htotal.trans_eq (index.symm.surjective.iSup_comp value).symm
  · intro i j
    simpa only [Q, relabel, index.apply_symm_apply] using hup (index.symm i) (index.symm j)
  · intro i j
    have h := hdir (index.symm i) (index.symm j)
    simp only [Q, relabel, index.apply_symm_apply] at h
    have heq : (⨆ k : Labels, value k ⊓ (P.leValue (index k) i ⊓ P.leValue (index k) j)) =
        ⨆ k : I, value (index.symm k) ⊓ (P.leValue k i ⊓ P.leValue k j) := by
      simpa only [index.symm_apply_apply] using index.surjective.iSup_comp
        (fun k => value (index.symm k) ⊓ (P.leValue k i ⊓ P.leValue k j))
    exact h.trans_eq heq
  · intro d
    have h := hmeets (requirements.symm d)
    simp only [requirements.apply_symm_apply] at h
    have heq : (⨆ i : Labels, value i ⊓ dense d (index i)) =
        ⨆ i : I, value (index.symm i) ⊓ dense d i := by
      simpa only [index.symm_apply_apply] using
        index.surjective.iSup_comp (fun i => value (index.symm i) ⊓ dense d i)
    exact h.trans_eq heq

theorem filter_coefficients (base : finalAlgebra) (rows : ℕ → bSet finalAlgebra)
    (relation : bSet finalAlgebra) (cut : Erdos597.One)
    (hccc : BooleanCountableChainCondition (forcing base rows relation cut))
    (hdense : ∀ d p, (forcing base rows relation cut).member p ≤
      ⨆ q, denseWeight base rows relation cut d q ⊓ (forcing base rows relation cut).leValue q p) :
    ∃ value : Finset Vertex → finalAlgebra,
      (∀ p, value p ≤ (forcing base rows relation cut).member p) ∧ base ≤ (⨆ p, value p) ∧
      (∀ p q, value p ⊓ (forcing base rows relation cut).leValue p q ≤ value q) ∧
      (∀ p q, value p ⊓ value q ≤ ⨆ s, value s ⊓
        ((forcing base rows relation cut).leValue s p ⊓ (forcing base rows relation cut).leValue s q)) ∧
      (∀ d, base ≤ ⨆ p, value p ⊓ denseWeight base rows relation cut d p) :=
  coefficients_of_equivalences base (forcing base rows relation cut) conditionEquiv requirementEquiv
    (fun _ => base) (denseWeight base rows relation cut) hccc (forcing_cover base rows relation cut)
    (fun _ => le_rfl) (denseWeight_le base rows relation cut)
    (fun d p => inf_le_right.trans (hdense d p))

end Erdos597Object.BooleanIndependentFilters
