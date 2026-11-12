import Erdos597Object.CompletionGenerators
import Erdos597Object.CompletionEmbedding

set_option backward.isDefEq.respectTransparency false

/-! Boolean coefficients of the generic filter in a two-step forcing completion. -/

namespace Erdos597Object.GenericFilterValues

open Set BooleanIteration PosetCompletion CompletionEmbedding CompletionGenerators

variable {B I : Type} [CompleteBooleanAlgebra B]

noncomputable def labelValue (P : BooleanPoset B I) (i : I) : Completion (Condition P) :=
  ⨆ p : {p : Condition P // p.label = i}, principal p.val

theorem principal_le_labelValue (P : BooleanPoset B I) (p : Condition P) :
    principal p ≤ labelValue P p.label :=
  le_iSup_of_le ⟨p, rfl⟩ le_rfl

theorem labelValue_le_member (P : BooleanPoset B I) (i : I) :
    labelValue P i ≤ baseMap P (P.member i) := by
  apply iSup_le
  intro p
  apply (principal_le_baseMap P p.val _).mpr
  simpa only [p.property] using p.val.valid

theorem labelValue_cover (P : BooleanPoset B I) : (⨆ i, labelValue P i) = ⊤ := by
  apply top_unique
  apply le_of_principal_refinements
  intro p _
  exact ⟨p, le_rfl, le_iSup_of_le p.label (principal_le_labelValue P p)⟩

theorem principal_inf_baseMap (P : BooleanPoset B I) (p : Condition P) (b : B) :
    principal p ⊓ baseMap P b =
      ⨆ q : {q : Condition P // q ≤ p ∧ q.value ≤ b}, principal q.val := by
  apply le_antisymm
  · apply le_of_principal_refinements
    intro r hr
    have hcompatible : principal r ⊓ principal p ≠ ⊥ := by
      rw [inf_eq_left.mpr (hr.trans inf_le_left)]
      exact principal_nonzero r
    obtain ⟨q, hqr, hqp⟩ := (principal_compatible_iff r p).mpr hcompatible
    have hrb : r.value ≤ b := (principal_le_baseMap P r b).mp (hr.trans inf_le_right)
    exact ⟨q, hqr, le_iSup_of_le ⟨q, hqp, hqr.1.trans hrb⟩ le_rfl⟩
  · apply iSup_le
    intro q
    exact le_inf (principal_monotone q.property.1)
      ((principal_le_baseMap P q.val b).mpr q.property.2)

theorem labelValue_upward (P : BooleanPoset B I) (i j : I) :
    labelValue P i ⊓ baseMap P (P.leValue i j) ≤ labelValue P j := by
  classical
  rw [labelValue, iSup_inf_eq]
  apply iSup_le
  intro p
  rw [principal_inf_baseMap]
  apply iSup_le
  intro q
  have hqi : q.val.value ≤ P.leValue q.val.label i := by
    simpa only [p.property] using q.property.1.2
  let r : Condition P :=
    ⟨q.val.value, j, q.val.nonzero,
      (q.property.2.trans (P.le_members i j)).trans inf_le_right⟩
  have hqr : q.val ≤ r :=
    ⟨le_rfl, (le_inf hqi q.property.2).trans (P.transitive q.val.label i j)⟩
  exact (principal_monotone hqr).trans (principal_le_labelValue P r)

theorem labelValue_directed (P : BooleanPoset B I) (i j : I) :
    labelValue P i ⊓ labelValue P j ≤
      ⨆ k, labelValue P k ⊓ baseMap P (P.leValue k i) ⊓ baseMap P (P.leValue k j) := by
  change (⨆ p : {p : Condition P // p.label = i}, principal p.val) ⊓
    (⨆ q : {q : Condition P // q.label = j}, principal q.val) ≤ _
  rw [iSup_inf_eq]
  apply iSup_le
  intro p
  rw [inf_iSup_eq]
  apply iSup_le
  intro q
  rw [principal_inf_principal]
  apply iSup_le
  intro r
  have hri : r.val.value ≤ P.leValue r.val.label i := by
    simpa only [p.property] using r.property.1.2
  have hrj : r.val.value ≤ P.leValue r.val.label j := by
    simpa only [q.property] using r.property.2.2
  apply le_iSup_of_le r.val.label
  exact le_inf (le_inf (principal_le_labelValue P r.val)
    ((principal_le_baseMap P r.val _).mpr hri))
      ((principal_le_baseMap P r.val _).mpr hrj)

theorem labelValue_meets_dense (P : BooleanPoset B I) (dense : I → B)
    (hdense : ∀ j, P.member j ≤ ⨆ i, dense i ⊓ P.leValue i j) :
    (⨆ i, labelValue P i ⊓ baseMap P (dense i)) = ⊤ := by
  classical
  apply top_unique
  apply le_of_principal_refinements
  intro p _
  have hex : ∃ i, p.value ⊓ (dense i ⊓ P.leValue i p.label) ≠ ⊥ := by
    by_contra! hzero
    apply p.nonzero
    calc
      p.value = p.value ⊓ (⨆ i, dense i ⊓ P.leValue i p.label) :=
        (inf_eq_left.mpr (p.valid.trans (hdense p.label))).symm
      _ = ⨆ i, p.value ⊓ (dense i ⊓ P.leValue i p.label) := inf_iSup_eq _ _
      _ = ⊥ := by simp only [hzero, iSup_bot]
  obtain ⟨i, hi⟩ := hex
  let q : Condition P :=
    ⟨p.value ⊓ (dense i ⊓ P.leValue i p.label), i, hi,
      (inf_le_right.trans inf_le_right).trans
        ((P.le_members i p.label).trans inf_le_left)⟩
  have hqp : q ≤ p := ⟨inf_le_left, inf_le_right.trans inf_le_right⟩
  refine ⟨q, hqp, le_iSup_of_le i ?_⟩
  exact le_inf (principal_le_labelValue P q)
    ((principal_le_baseMap P q _).mpr (inf_le_right.trans inf_le_left))

end Erdos597Object.GenericFilterValues
