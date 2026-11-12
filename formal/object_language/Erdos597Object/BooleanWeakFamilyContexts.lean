import Erdos597Object.BooleanWeakPrefixes

set_option backward.isDefEq.respectTransparency false

/-! Restrict conclusions while keeping the row family's original Boolean context. -/

namespace Erdos597Object.BooleanWeakFamilyContexts

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanWeakFamilies BooleanWeakPrefixes BooleanGoodPairs
open Erdos597.WeakFamilies (Index first last singleton priorIndex erasePrior intervalIndex interval_mem)

variable {B : Type} [CompleteBooleanAlgebra B]

theorem sets_bad_extension_at (context part : B) (hpart : part ≤ context)
    (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ) (s : Index)
    (he : (s.val.erase (last s)).Nonempty)
    (hnotGood : part ≤ (goodPair (relation (first (priorIndex (erasePrior s rfl he))) (last s))
      (sets context domain relation hlarge (priorIndex (erasePrior s rfl he)))
      (sets context domain relation hlarge (singleton (last s))))ᶜ) :
    part ≤ badPair (relation (first (priorIndex (erasePrior s rfl he))) (last s))
      (sets context domain relation hlarge s) (sets context domain relation hlarge (singleton (last s))) := by
  have hstatus := (decision context domain relation hlarge (last s)
    (fun t _ => family context domain relation hlarge t)).status (erasePrior s rfl he)
  have hset : sets context domain relation hlarge s =
      ((decision context domain relation hlarge (last s) (fun t _ => family context domain relation hlarge t)).left
        (erasePrior s rfl he)).name := by
    unfold sets
    rw [family_eq, step_name_nonempty context domain relation hlarge (last s) _ s rfl he]
  rw [sets_singleton] at hnotGood ⊢
  rw [hset]
  apply lattice.context_or_elim' (hpart.trans hstatus)
  · intro smaller hsmaller hgood
    exact ((le_inf hgood (hsmaller.trans hnotGood)).trans_eq inf_compl_eq_bot).trans bot_le
  · intro smaller hsmaller hbad
    exact hbad

theorem sets_to_first (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ) (s : Index) :
    context ≤ sets context domain relation hlarge s ⊆ᴮ
      sets context domain relation hlarge (singleton (first s)) := by
  apply sets_subset_of_prefix
  · intro a ha
    have ha' : a = first s := Finset.mem_singleton.mp ha
    subst a
    exact s.val.min'_mem s.property
  · intro a ha b hb hbt
    have ha' : a = first s := Finset.mem_singleton.mp ha
    subst a
    have hne : b ≠ first s := fun h => hbt (Finset.mem_singleton.mpr h)
    exact lt_of_le_of_ne (s.val.min'_le b hb) hne.symm

theorem sets_interval_prefix (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (f : ℕ → ℕ) (hf : StrictMono f) (i j k : ℕ) (hij : i < j) (hjk : j ≤ k) :
    context ≤ sets context domain relation hlarge (intervalIndex f i k (hij.trans_le hjk)) ⊆ᴮ
      sets context domain relation hlarge (intervalIndex f i j hij) := by
  apply sets_subset_of_prefix
  · intro x hx
    obtain ⟨a, hai, haj, rfl⟩ := (interval_mem f i j hij x).mp hx
    exact (interval_mem f i k _ _).mpr ⟨a, hai, haj.trans_le hjk, rfl⟩
  · intro x hx y hy hynot
    obtain ⟨a, hai, haj, rfl⟩ := (interval_mem f i j hij x).mp hx
    obtain ⟨b, hbi, hbk, rfl⟩ := (interval_mem f i k _ y).mp hy
    have hjb : j ≤ b := by
      by_contra h
      exact hynot ((interval_mem f i j hij _).mpr ⟨b, hbi, lt_of_not_ge h, rfl⟩)
    exact hf (haj.trans_le hjb)

theorem goodPair_forbidden_on_larger (part : B) (relation left smallRight largeRight : bSet B)
    (hsubset : part ≤ smallRight ⊆ᴮ largeRight)
    (hnotGood : part ≤ (goodPair relation left smallRight)ᶜ) :
    part ≤ (goodPair relation left largeRight)ᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  rw [disjoint_iff]
  apply bot_unique
  have hgood : part ⊓ goodPair relation left largeRight ≤ goodPair relation left smallRight :=
    goodPair_restrict (part ⊓ goodPair relation left largeRight) relation left largeRight left smallRight
      bSet.subset_self (inf_le_left.trans hsubset) inf_le_right
  exact (le_inf hgood (inf_le_left.trans hnotGood)).trans_eq inf_compl_eq_bot

end Erdos597Object.BooleanWeakFamilyContexts
