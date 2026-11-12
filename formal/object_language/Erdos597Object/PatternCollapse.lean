import Erdos597Object.ScheduledSparseGraph
import Erdos597Object.BooleanFunctionReflection

set_option backward.isDefEq.respectTransparency false

/-! The countably closed collapse that supplies a generic schedule of all ground patterns. -/

namespace Erdos597Object.PatternCollapse

open Erdos597 Flypitch Flypitch.ZFC
open Flypitch.collapse_poset
open scoped Cardinal Ordinal Flypitch.bSet

instance patternNonempty : Nonempty Pattern := by
  classical
  obtain ⟨row, hrow, _⟩ := increasing_sequence_in_uncountable_set
    (S := Set.univ) Set.not_countable_univ zeroOne
  have hcolumns : ∀ n, ∃ column : Nat → One,
      StrictMono column ∧ ∀ m, column m ∈ Set.univ ∧ row n < column m :=
    fun n => increasing_sequence_in_uncountable_set Set.not_countable_univ (row n)
  choose column hcolumn hactive using hcolumns
  exact ⟨⟨row, column, hrow, hcolumn, fun n m => (hactive n m).2⟩⟩

abbrev Algebra := collapse_algebra One Pattern
abbrev Condition := collapse_poset One Pattern (Order.succ Cardinal.aleph0)

theorem closed_basis : has_dense_omega_closed_subset Algebra :=
  collapse_algebra_has_dense_omega_closed_subset

theorem omegaOne_preserved :
    (⊤ : Algebra) ≤ omegaOneValue (V Algebra) CanonicalDomains.omegaOneName :=
  BooleanClosedUncountability.omegaOneValue_check closed_basis

noncomputable def entry (index : One) (pattern : Pattern) : Algebra :=
  inclusion (singleton_collapse_poset index pattern one_lt_succ_aleph0)

theorem mem_entry (schedule : One → Pattern) (index : One) (pattern : Pattern) :
    schedule ∈ (entry index pattern : Set (One → Pattern)) ↔ schedule index = pattern := by
  change schedule ∈ principal_open (singleton_collapse_poset index pattern one_lt_succ_aleph0) ↔ _
  rw [singleton_collapse_poset_principal_open]
  rfl

theorem entry_disjoint (index : One) (left right : Pattern) (hne : left ≠ right) :
    entry index left ⊓ entry index right = ⊥ := by
  apply bot_unique
  change ((entry index left : Set (One → Pattern)) ∩ entry index right) ⊆ ∅
  intro schedule h
  exact (hne ((mem_entry schedule index left).mp h.1 |>.symm.trans
    ((mem_entry schedule index right).mp h.2))).elim

theorem entry_cover (index : One) : (⨆ pattern, entry index pattern) = ⊤ := by
  apply top_unique
  change (Set.univ : Set (One → Pattern)) ⊆ (⨆ pattern, entry index pattern : Algebra)
  intro schedule _
  exact (le_iSup (entry index) (schedule index)) ((mem_entry schedule index (schedule index)).mpr rfl)

noncomputable def prefixCondition (bound : One) (schedule : One → Pattern) : Condition where
  f := fun index => ⟨index < bound, fun _ => schedule index⟩
  Hc := by
    change Cardinal.mk (Set.Iio bound) < Order.succ Cardinal.aleph0
    have : Countable (Set.Iio bound) := BooleanCountableNames.below_countable bound
    exact lt_of_le_of_lt (Cardinal.mk_le_aleph0) (Order.lt_succ Cardinal.aleph0)

noncomputable def prefixValue (bound : One) (schedule : One → Pattern) : Algebra :=
  inclusion (prefixCondition bound schedule)

theorem mem_prefix (bound : One) (schedule value : One → Pattern) :
    value ∈ (prefixValue bound schedule : Set (One → Pattern)) ↔
      ∀ index, index < bound → value index = schedule index := by
  change (∀ index pattern, (∃ _ : index < bound, schedule index = pattern) → value index = pattern) ↔ _
  constructor
  · intro h index hi
    exact h index (schedule index) ⟨hi, rfl⟩
  · rintro h index pattern ⟨hi, rfl⟩
    exact h index hi

theorem prefix_positive (bound : One) (schedule : One → Pattern) : prefixValue bound schedule ≠ ⊥ :=
  inclusion_ne_bot _

theorem prefix_cover (bound : One) : (⨆ schedule, prefixValue bound schedule) = ⊤ := by
  apply top_unique
  change (Set.univ : Set (One → Pattern)) ⊆ (⨆ schedule, prefixValue bound schedule : Algebra)
  intro value _
  exact (le_iSup (prefixValue bound) value) ((mem_prefix bound value value).mpr (fun _ _ => rfl))

theorem prefix_le_entry (bound : One) (schedule : One → Pattern) (index : One)
    (hi : index < bound) : prefixValue bound schedule ≤ entry index (schedule index) := by
  intro value hvalue
  exact (mem_entry value index (schedule index)).mpr ((mem_prefix bound schedule value).mp hvalue index hi)

theorem prefix_mono (small large : One) (hbound : small ≤ large) (schedule : One → Pattern) :
    prefixValue large schedule ≤ prefixValue small schedule := by
  intro value hvalue
  exact (mem_prefix small schedule value).mpr
    (fun index hi => (mem_prefix large schedule value).mp hvalue index (hi.trans_le hbound))

theorem prefix_agreement (bound : One) (left right : One → Pattern)
    (hne : prefixValue bound left ⊓ prefixValue bound right ≠ ⊥) :
    ∀ index, index < bound → left index = right index := by
  intro index hi
  by_contra h
  apply hne
  exact bot_unique ((inf_le_inf (prefix_le_entry bound left index hi)
    (prefix_le_entry bound right index hi)).trans_eq (entry_disjoint index _ _ h))

theorem fresh_index (p : Condition) : ∃ index : One, index ∉ PFun.Dom p.f := by
  classical
  by_contra h
  have hall : ∀ index : One, index ∈ PFun.Dom p.f := by simpa using h
  have hsurjective : Function.Surjective (fun index : PFun.Dom p.f => (index : One)) :=
    fun index => ⟨⟨index, hall index⟩, rfl⟩
  have hle : (Cardinal.aleph 1) ≤ Cardinal.mk (PFun.Dom p.f) := by
    simpa only [Erdos597.one_card] using Cardinal.mk_le_of_surjective hsurjective
  have hlt : (Cardinal.aleph 1) < Cardinal.aleph 1 := by
    simpa only [← Flypitch.pSet.aleph_one_eq_succ_aleph_zero] using hle.trans_lt p.Hc
  exact lt_irrefl _ hlt

theorem union_below (p q : Condition) (hcompatible : collapse_poset.compatible p q) :
    inclusion (union p q) ≤ inclusion p ⊓ inclusion q := by
  change principal_open (union p q) ⊆ principal_open p ∩ principal_open q
  rw [inter_principal_open hcompatible]

theorem entry_onto (pattern : Pattern) : (⨆ index, entry index pattern) = ⊤ := by
  classical
  apply top_unique
  by_contra hnot
  let all : Algebra := ⨆ index, entry index pattern
  have hne : allᶜ ≠ ⊥ := by
    intro hzero
    exact hnot (by simpa only [all, compl_eq_bot] using (compl_eq_bot.mp hzero).ge)
  obtain ⟨p, hp⟩ := collapse_poset_dense (bot_lt_iff_ne_bot.mpr hne)
  obtain ⟨index, hindex⟩ := fresh_index p
  let singleton : Condition := singleton_collapse_poset index pattern one_lt_succ_aleph0
  have hcompatible : collapse_poset.compatible p singleton := by
    intro x hp hq
    have hx : x = index := by
      simpa only [singleton, singleton_collapse_poset, pfun_singleton_dom,
        Set.mem_singleton_iff] using hq
    exact (hindex (hx ▸ hp)).elim
  have hbelow := union_below p singleton hcompatible
  have hin : inclusion (union p singleton) ≤ all :=
    (hbelow.trans inf_le_right).trans (le_iSup (fun index => entry index pattern) index)
  have hout : inclusion (union p singleton) ≤ allᶜ := (hbelow.trans inf_le_left).trans hp
  exact inclusion_ne_bot (union p singleton)
    (bot_unique ((le_inf hin hout).trans_eq inf_compl_eq_bot))

end Erdos597Object.PatternCollapse
