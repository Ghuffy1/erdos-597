import Erdos597Object.PosetCompletion

set_option backward.isDefEq.respectTransparency false

/-! Refinement arguments for the principal generators of a forcing completion. -/

namespace Erdos597Object.CompletionGenerators

open Set PosetCompletion

variable {P : Type} [PartialOrder P]

theorem le_of_principal_refinements {u v : Completion P}
    (h : ∀ p : P, principal p ≤ u → ∃ q : P, q ≤ p ∧ principal q ≤ v) : u ≤ v := by
  classical
  by_contra hle
  have hnonzero : u ⊓ vᶜ ≠ ⊥ := by
    intro hzero
    apply hle
    simpa only [compl_compl] using
      (le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr hzero))
  obtain ⟨p, hp⟩ := principal_dense (u ⊓ vᶜ) hnonzero
  obtain ⟨q, hqp, hqv⟩ := h p (hp.trans inf_le_left)
  have hqc : principal q ≤ vᶜ := (principal_monotone hqp).trans (hp.trans inf_le_right)
  apply principal_nonzero q
  apply bot_unique
  exact (le_inf hqv hqc).trans_eq (inf_compl_self v)

theorem principal_inf_principal (p q : P) :
    principal p ⊓ principal q =
      ⨆ r : {r : P // r ≤ p ∧ r ≤ q}, principal r.val := by
  apply le_antisymm
  · apply le_of_principal_refinements
    intro r hr
    have hrp : principal r ⊓ principal p ≠ ⊥ := by
      rw [inf_eq_left.mpr (hr.trans inf_le_left)]
      exact principal_nonzero r
    obtain ⟨s, hsr, hsp⟩ := (principal_compatible_iff r p).mpr hrp
    have hsq : principal s ⊓ principal q ≠ ⊥ := by
      rw [inf_eq_left.mpr ((principal_monotone hsr).trans (hr.trans inf_le_right))]
      exact principal_nonzero s
    obtain ⟨t, hts, htq⟩ := (principal_compatible_iff s q).mpr hsq
    exact ⟨t, hts.trans hsr, le_iSup_of_le ⟨t, hts.trans hsp, htq⟩ le_rfl⟩
  · apply iSup_le
    intro r
    exact le_inf (principal_monotone r.property.1) (principal_monotone r.property.2)

end Erdos597Object.CompletionGenerators
