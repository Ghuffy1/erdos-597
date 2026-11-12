import Erdos597Object.BooleanPosetModel
import Mathlib.Topology.Order.UpperLowerSetTopology

set_option backward.isDefEq.respectTransparency false

/-! The regular-open completion of a forcing poset with its lower-set topology. -/

namespace Erdos597Object.PosetCompletion

open Set TopologicalSpace Flypitch
open Topology.WithLowerSet

variable {P : Type} [PartialOrder P]

abbrev Completion (P : Type) [PartialOrder P] :=
  regular_opens (Topology.WithLowerSet P)

def cone (p : P) : Set (Topology.WithLowerSet P) := Iic (toLowerSet p)

theorem cone_open (p : P) : IsOpen (cone p) := by
  apply (Topology.IsLowerSet.isOpen_iff_isLowerSet
    (α := Topology.WithLowerSet P) (s := cone p)).mpr
  exact isLowerSet_Iic (toLowerSet p)

noncomputable def principal (p : P) : Completion P :=
  ⟨(cone p)ᵖᵖ, is_regular_p_p⟩

theorem cone_subset_principal (p : P) : cone p ⊆ (principal p : Set (Topology.WithLowerSet P)) :=
  subset_p_p_of_open (cone_open p)

theorem principal_nonzero (p : P) : principal p ≠ (⊥ : Completion P) := by
  have hp : toLowerSet p ∈ (principal p : Set (Topology.WithLowerSet P)) :=
    cone_subset_principal p le_rfl
  intro h
  rw [h] at hp
  change toLowerSet p ∈ (∅ : Set (Topology.WithLowerSet P)) at hp
  exact hp

theorem principal_monotone : Monotone (principal : P → Completion P) := by
  intro p q hpq
  apply p_p_mono
  intro r hr
  exact hr.trans hpq

theorem principal_compatible_iff (p q : P) :
    (∃ r : P, r ≤ p ∧ r ≤ q) ↔ principal p ⊓ principal q ≠ (⊥ : Completion P) := by
  classical
  constructor
  · rintro ⟨r, hrp, hrq⟩ hzero
    have hr : toLowerSet r ∈
        ((principal p ⊓ principal q : Completion P) : Set (Topology.WithLowerSet P)) :=
      ⟨cone_subset_principal p hrp, cone_subset_principal q hrq⟩
    rw [hzero] at hr
    change toLowerSet r ∈ (∅ : Set (Topology.WithLowerSet P)) at hr
    exact hr
  · intro hnonzero
    by_contra hnone
    have hempty : cone p ∩ cone q = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro r hr
      exact hnone ⟨ofLowerSet r, hr.1, hr.2⟩
    apply hnonzero
    apply Subtype.ext
    change (cone p)ᵖᵖ ∩ (cone q)ᵖᵖ = ∅
    rw [← p_p_inter_eq_inter_p_p (cone_open q), hempty]
    simp

theorem principal_dense (b : Completion P) (hb : b ≠ ⊥) :
    ∃ p : P, principal p ≤ b := by
  have hnonempty : (b : Set (Topology.WithLowerSet P)).Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro hempty
    apply hb
    exact Subtype.ext hempty
  obtain ⟨p, hp⟩ := hnonempty
  refine ⟨ofLowerSet p, ?_⟩
  apply is_regular_stable_subset b.property
  have hlower : IsLowerSet (b : Set (Topology.WithLowerSet P)) :=
    Topology.IsLowerSet.isOpen_iff_isLowerSet.mp (isOpen_of_is_regular b.property)
  intro q hq
  exact hlower hq hp

noncomputable instance completionNontrivial [Nonempty P] : Nontrivial (Completion P) := by
  classical
  obtain ⟨p⟩ := ‹Nonempty P›
  exact ⟨⟨principal p, ⊥, principal_nonzero p⟩⟩

end Erdos597Object.PosetCompletion
