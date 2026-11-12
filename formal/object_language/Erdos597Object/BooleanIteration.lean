import Erdos597Object.AntichainCodes

set_option backward.isDefEq.respectTransparency false

/-!
The conditions in a two-step forcing construction over a Boolean algebra.
The second order is given by Boolean values on a fixed set of labels.
-/

namespace Erdos597Object.BooleanIteration

open Set

structure BooleanPoset (B I : Type) [CompleteBooleanAlgebra B] where
  member : I → B
  leValue : I → I → B
  le_members : ∀ i j, leValue i j ≤ member i ⊓ member j
  reflexive : ∀ i, member i ≤ leValue i i
  transitive : ∀ i j k, leValue i j ⊓ leValue j k ≤ leValue i k
  antisymmetric : ∀ i j, i ≠ j → leValue i j ⊓ leValue j i = ⊥

variable {B I : Type} [CompleteBooleanAlgebra B]

structure Condition (P : BooleanPoset B I) where
  value : B
  label : I
  nonzero : value ≠ ⊥
  valid : value ≤ P.member label

@[ext] theorem condition_ext {P : BooleanPoset B I} {p q : Condition P}
    (hvalue : p.value = q.value) (hlabel : p.label = q.label) : p = q := by
  cases p
  cases q
  cases hvalue
  cases hlabel
  rfl

noncomputable instance (P : BooleanPoset B I) : PartialOrder (Condition P) where
  le p q := p.value ≤ q.value ∧ p.value ≤ P.leValue p.label q.label
  le_refl p := ⟨le_rfl, p.valid.trans (P.reflexive p.label)⟩
  le_trans p q r hpq hqr :=
    ⟨hpq.1.trans hqr.1,
      (le_inf hpq.2 (hpq.1.trans hqr.2)).trans
        (P.transitive p.label q.label r.label)⟩
  le_antisymm p q hpq hqp := by
    apply condition_ext (le_antisymm hpq.1 hqp.1)
    by_contra hne
    have hbound : p.value ≤ P.leValue p.label q.label ⊓ P.leValue q.label p.label :=
      le_inf hpq.2 (hpq.1.trans hqp.2)
    rw [P.antisymmetric p.label q.label hne] at hbound
    exact p.nonzero (bot_unique hbound)

theorem condition_le_iff {P : BooleanPoset B I} (p q : Condition P) :
    p ≤ q ↔ p.value ≤ q.value ∧ p.value ≤ P.leValue p.label q.label := Iff.rfl

def compatibleValue (P : BooleanPoset B I) (i j : I) : B :=
  ⨆ k, P.leValue k i ⊓ P.leValue k j

theorem compatible_iff {P : BooleanPoset B I} (p q : Condition P) :
    (∃ r : Condition P, r ≤ p ∧ r ≤ q) ↔
      p.value ⊓ q.value ⊓ compatibleValue P p.label q.label ≠ ⊥ := by
  classical
  constructor
  · rintro ⟨r, hrp, hrq⟩ heq
    have hrel : r.value ≤ compatibleValue P p.label q.label :=
      le_iSup_of_le r.label (le_inf hrp.2 hrq.2)
    have hbound := le_inf (le_inf hrp.1 hrq.1) hrel
    rw [heq] at hbound
    exact r.nonzero (bot_unique hbound)
  · intro hnonzero
    have hex : ∃ k, p.value ⊓ q.value ⊓
        (P.leValue k p.label ⊓ P.leValue k q.label) ≠ ⊥ := by
      by_contra! h
      apply hnonzero
      simp only [compatibleValue, inf_iSup_eq, h, iSup_bot]
    obtain ⟨k, hk⟩ := hex
    let r : Condition P :=
      ⟨p.value ⊓ q.value ⊓ (P.leValue k p.label ⊓ P.leValue k q.label), k, hk,
        (inf_le_right.trans inf_le_left).trans ((P.le_members k p.label).trans inf_le_left)⟩
    refine ⟨r, ?_, ?_⟩
    · exact ⟨inf_le_left.trans inf_le_left, inf_le_right.trans inf_le_left⟩
    · exact ⟨inf_le_left.trans inf_le_right, inf_le_right.trans inf_le_right⟩

end Erdos597Object.BooleanIteration
