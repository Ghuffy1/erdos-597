import Erdos597Object.BooleanColumns

set_option backward.isDefEq.respectTransparency false

/-! The literal canonical block order agrees with the ground ordinal coordinates. -/

namespace Erdos597Object.BooleanBlockOrder

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanColumns CanonicalDomains CanonicalRelations

variable {B : Type} [CompleteBooleanAlgebra B]

open Classical in
attribute [local instance] propDecidable

theorem lexLess_pair (a b c d : bSet B) :
    lexLessValue (V B) (bSet.pair a b) (bSet.pair c d) =
      (a ∈ᴮ c) ⊔ ((a =ᴮ c) ⊓ (b ∈ᴮ d)) := by
  apply le_antisymm
  · apply iSup_le
    intro a'
    apply iSup_le
    intro b'
    apply iSup_le
    intro c'
    apply iSup_le
    intro d'
    change (bSet.pair a b =ᴮ bSet.pair a' b') ⊓
      ((bSet.pair c d =ᴮ bSet.pair c' d') ⊓
        ((a' ∈ᴮ c') ⊔ ((a' =ᴮ c') ⊓ (b' ∈ᴮ d')))) ≤ _
    let part : B := (bSet.pair a b =ᴮ bSet.pair a' b') ⊓
      ((bSet.pair c d =ᴮ bSet.pair c' d') ⊓
        ((a' ∈ᴮ c') ⊔ ((a' =ᴮ c') ⊓ (b' ∈ᴮ d'))))
    have ha : part ≤ a =ᴮ a' := bSet.eq_of_eq_pair_left' inf_le_left
    have hb : part ≤ b =ᴮ b' := bSet.eq_of_eq_pair_right' inf_le_left
    have hc : part ≤ c =ᴮ c' := bSet.eq_of_eq_pair_left' (inf_le_right.trans inf_le_left)
    have hd : part ≤ d =ᴮ d' := bSet.eq_of_eq_pair_right' (inf_le_right.trans inf_le_left)
    have hcase : part ≤ (a' ∈ᴮ c') ⊔ ((a' =ᴮ c') ⊓ (b' ∈ᴮ d')) :=
      inf_le_right.trans inf_le_right
    apply (le_inf le_rfl hcase).trans
    apply lattice.bv_or_elim_right
    · apply le_sup_of_le_left
      exact bSet.subst_congr_mem_right' (bSet.bv_symm (inf_le_left.trans hc))
        (bSet.subst_congr_mem_left' (bSet.bv_symm (inf_le_left.trans ha)) inf_le_right)
    · apply le_sup_of_le_right
      apply le_inf
      · exact bSet.bv_trans (inf_le_left.trans ha)
          (bSet.bv_trans (inf_le_right.trans inf_le_left)
            (bSet.bv_symm (inf_le_left.trans hc)))
      · exact bSet.subst_congr_mem_right' (bSet.bv_symm (inf_le_left.trans hd))
          (bSet.subst_congr_mem_left' (bSet.bv_symm (inf_le_left.trans hb))
            (inf_le_right.trans inf_le_right))
  · apply le_iSup_of_le a
    apply le_iSup_of_le b
    apply le_iSup_of_le c
    apply le_iSup_of_le d
    exact le_inf bSet.bv_refl (le_inf bSet.bv_refl le_rfl)

theorem natural_member (n m : ℕ) :
    ((bSet.ofNat n : bSet B) ∈ᴮ bSet.ofNat m) = if n < m then ⊤ else ⊥ := by
  by_cases h : n < m
  · rw [ite_eq_left h]
    exact top_unique (bSet.ofNat_mem_of_lt h)
  · rw [ite_eq_right h]
    exact bSet.check_bv_mem_bot_of_not_mem (fun hm => h (pSet.lt_of_of_nat_mem hm))

theorem natural_equal (n m : ℕ) :
    ((bSet.ofNat n : bSet B) =ᴮ bSet.ofNat m) = if n = m then ⊤ else ⊥ := by
  by_cases h : n = m
  · subst m
    simp only [ite_true]
    exact top_unique bSet.bv_refl
  · rw [ite_eq_right h]
    exact bSet.ofNat_inj h

def keyLess (i j : ℕ × ScheduledIteration.Labels) : Prop :=
  i.1 < j.1 ∨ (i.1 = j.1 ∧ column i.2 < column j.2)

theorem keyLess_asymm {i j : ℕ × ScheduledIteration.Labels}
    (hij : keyLess i j) : ¬ keyLess j i := by
  rintro (hji | ⟨hrow, hcol⟩)
  · rcases hij with hij | ⟨hrow, _⟩ <;> omega
  · rcases hij with hij | ⟨_, hcol'⟩
    · omega
    · exact lt_asymm hcol' hcol

theorem blockOrder_edge (i j : ℕ × ScheduledIteration.Labels) :
    edgeValue (V B) blockOrder (blockLabel i) (blockLabel j) =
      if keyLess i j then ⊤ else ⊥ := by
  classical
  rw [show blockOrder = lexOrderName blockLabel from rfl,
    lexOrderName_edge blockLabel blockLabel_discrete]
  change lexLessValue (V B) (bSet.pair (bSet.ofNat i.1) (OmegaOneLabels.element i.2))
    (bSet.pair (bSet.ofNat j.1) (OmegaOneLabels.element j.2)) = _
  rw [lexLess_pair, natural_member, natural_equal, element_member]
  by_cases hrow : i.1 < j.1 <;> by_cases heq : i.1 = j.1 <;>
    by_cases hcol : column i.2 < column j.2 <;> simp [keyLess, hrow, heq, hcol]

end Erdos597Object.BooleanBlockOrder
