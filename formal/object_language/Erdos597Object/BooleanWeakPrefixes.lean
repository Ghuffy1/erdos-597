import Erdos597Object.BooleanWeakFamilies

set_option backward.isDefEq.respectTransparency false

/-! The Boolean row family is nested along initial segments of a finite chain. -/

namespace Erdos597Object.BooleanWeakPrefixes

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanWeakFamilies BooleanUncountableRamsey
open Erdos597.WeakFamilies (Index last priorIndex erasePrior)

variable {B : Type} [CompleteBooleanAlgebra B]

theorem sets_subset_of_prefix (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (s t : Index) (ht : t.val ⊆ s.val)
    (hbefore : ∀ a ∈ t.val, ∀ b ∈ s.val, b ∉ t.val → a < b) :
    context ≤ sets context domain relation hlarge s ⊆ᴮ sets context domain relation hlarge t := by
  classical
  have aux : ∀ m : ℕ, ∀ s : Index, s.val.card = m → ∀ t : Index,
      t.val ⊆ s.val → (∀ a ∈ t.val, ∀ b ∈ s.val, b ∉ t.val → a < b) →
      context ≤ sets context domain relation hlarge s ⊆ᴮ sets context domain relation hlarge t := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro s hcard t ht hbefore
      by_cases heq : s.val = t.val
      · have hs : s = t := Subtype.ext heq
        rw [hs]
        exact bSet.subset_self
      · have hout : ∃ b ∈ s.val, b ∉ t.val := by
          by_contra hn
          push Not at hn
          exact heq (Finset.Subset.antisymm hn ht)
        obtain ⟨b, hb, hbt⟩ := hout
        have hlast : last s ∉ t.val := by
          intro hlast
          have hlt := hbefore (last s) hlast b hb hbt
          exact (not_lt_of_ge (s.val.le_max' b hb)) hlt
        have herase : (s.val.erase (last s)).Nonempty := by
          obtain ⟨a, ha⟩ := t.property
          exact ⟨a, Finset.mem_erase.mpr ⟨fun h => hlast (h ▸ ha), ht ha⟩⟩
        let p : Index := priorIndex (erasePrior s rfl herase)
        have hpcard : p.val.card < m := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem (s.val.max'_mem s.property)
        have htp : t.val ⊆ p.val := by
          intro a ha
          exact Finset.mem_erase.mpr ⟨fun h => hlast (h ▸ ha), ht ha⟩
        have hbefore' : ∀ a ∈ t.val, ∀ b ∈ p.val, b ∉ t.val → a < b := by
          intro a ha b hb hbt
          exact hbefore a ha b (Finset.mem_of_mem_erase hb) hbt
        exact subset_trans (sets_shrink context domain relation hlarge s herase)
          (ih p.val.card hpcard p rfl t htp hbefore')
  exact aux s.val.card s rfl t ht hbefore

end Erdos597Object.BooleanWeakPrefixes
