import Erdos597Object.BooleanIndependentDensity

set_option backward.isDefEq.respectTransparency false

/-! Countability and refinement of weighted discrete sets for the finite-condition argument. -/

namespace Erdos597Object.BooleanWeightedSupports

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanCountableNames BooleanCountableAvoidance BooleanGraphNeighborhoods

variable {B I J : Type} [CompleteBooleanAlgebra B]

theorem countable_of_countable_support (context : B) (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥) (weight : I → B)
    (hcount : {i | context ⊓ weight i ≠ ⊥}.Countable) :
    context ≤ injectsIntoValue (V B) (weightedSet label weight) bSet.omega := by
  classical
  let support : Set I := {i | context ⊓ weight i ≠ ⊥}
  let : Countable support := hcount.to_subtype
  let small := weightedSet (fun i : support => label i.val) (fun _ => (⊤ : B))
  have hsmall : (⊤ : B) ≤ injectsIntoValue (V B) small bSet.omega :=
    weighted_countable _ (fun i j hij => hdiscrete i.val j.val (fun h => hij (Subtype.ext h))) _
  apply subset_countable (weightedSet label weight) small ?_ (le_top.trans hsmall)
  apply bSet.subset_intro
  intro i
  change context ⊓ weight i ≤ label i ∈ᴮ small
  by_cases hi : i ∈ support
  · exact le_top.trans (weight_le_member (fun j : support => label j.val) (fun _ => (⊤ : B)) ⟨i, hi⟩)
  · have hzero : context ⊓ weight i = ⊥ := by
      change ¬ (context ⊓ weight i ≠ ⊥) at hi
      exact not_not.mp hi
    rw [hzero]
    exact bot_le

theorem countable_support_of_countable (hB : Flypitch.BA_CCC B) (context : B)
    (label : I → bSet B) (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (weight : I → B)
    (hcount : context ≤ injectsIntoValue (V B) (weightedSet label weight) bSet.omega) :
    {i | context ⊓ weight i ≠ ⊥}.Countable := by
  apply (possible_members_countable hB context label
    (fun i j hij => by rw [hdiscrete i j hij, inf_bot_eq]) (weightedSet label weight) hcount).mono
  intro i hi hzero
  exact hi (bot_unique ((inf_le_inf_left context (weight_le_member label weight i)).trans_eq hzero))

theorem weighted_countable_iff (hB : Flypitch.BA_CCC B) (context : B)
    (label : I → bSet B) (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (weight : I → B) :
    context ≤ injectsIntoValue (V B) (weightedSet label weight) bSet.omega ↔
      {i | context ⊓ weight i ≠ ⊥}.Countable :=
  ⟨countable_support_of_countable hB context label hdiscrete weight,
    countable_of_countable_support context label hdiscrete weight⟩

theorem countability_independent_of_labels (hB : Flypitch.BA_CCC B)
    (left right : I → bSet B)
    (hleft : ∀ i j, i ≠ j → (left i =ᴮ left j) = ⊥)
    (hright : ∀ i j, i ≠ j → (right i =ᴮ right j) = ⊥) (weight : I → B) :
    injectsIntoValue (V B) (weightedSet left weight) bSet.omega =
      injectsIntoValue (V B) (weightedSet right weight) bSet.omega := by
  apply le_antisymm
  · exact countable_of_countable_support _ right hright weight
      (countable_support_of_countable hB _ left hleft weight le_rfl)
  · exact countable_of_countable_support _ left hleft weight
      (countable_support_of_countable hB _ right hright weight le_rfl)

theorem positive_uncountable_part (hB : Flypitch.BA_CCC B) (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥) (weight : I → B)
    (hcount : ¬ {i | weight i ≠ ⊥}.Countable) :
    ∃ context : B, context ≠ ⊥ ∧
      context ≤ (injectsIntoValue (V B) (weightedSet label weight) bSet.omega)ᶜ := by
  let countValue := injectsIntoValue (V B) (weightedSet label weight) bSet.omega
  have hne : countValue ≠ ⊤ := by
    intro htop
    have h := countable_support_of_countable hB ⊤ label hdiscrete weight (by rw [← htop])
    exact hcount (by simpa only [top_inf_eq] using h)
  refine ⟨countValueᶜ, ?_, le_rfl⟩
  intro hzero
  apply hne
  simpa only [compl_compl, compl_bot] using congrArg compl hzero

theorem uncountable_le_outside (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (weight : I → B) (small : Set I) (hsmall : small.Countable) :
    (injectsIntoValue (V B) (weightedSet label weight) bSet.omega)ᶜ ≤
      ⨆ i, ⨆ (_ : i ∉ small), weight i := by
  classical
  let cover : B := ⨆ i, ⨆ (_ : i ∉ small), weight i
  let part := (injectsIntoValue (V B) (weightedSet label weight) bSet.omega)ᶜ ⊓ coverᶜ
  have hsupport : {i | part ⊓ weight i ≠ ⊥}.Countable := by
    apply hsmall.mono
    intro i hi
    by_contra hout
    have hle : weight i ≤ cover := le_iSup_of_le i (le_iSup_of_le hout le_rfl)
    apply hi
    apply bot_unique
    exact (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans hle)).trans_eq
      compl_inf_eq_bot
  have hcount := countable_of_countable_support part label hdiscrete weight hsupport
  have hzero : part = ⊥ := bot_unique
    ((le_inf hcount inf_le_left).trans_eq inf_compl_eq_bot)
  have hdis : (injectsIntoValue (V B) (weightedSet label weight) bSet.omega)ᶜ ≤ coverᶜᶜ :=
    (le_compl_iff_disjoint_right).mpr (disjoint_iff.mpr hzero)
  simpa only [compl_compl] using hdis

theorem restriction_contains (context : B) (label : I → bSet B) (weight : I → B)
    (small : bSet B) (hsmall : context ≤ small ⊆ᴮ weightedSet label weight) :
    context ≤ small ⊆ᴮ weightedSet label (fun i => weight i ⊓ (label i ∈ᴮ small)) := by
  have h : context ≤ small ⊆ᴮ bSet.comprehend (fun x => x ∈ᴮ small) (weightedSet label weight) := by
    apply bSet.subset_intro
    intro i
    rw [member_comprehend _ (bSet.B_ext_mem_left small)]
    have hmember : context ⊓ small.bval i ≤ small.func i ∈ᴮ small :=
      inf_le_right.trans (bSet.mem.mk' small i)
    exact le_inf (bSet.mem_of_mem_subset' (inf_le_left.trans hsmall) hmember) hmember
  change context ≤ small ⊆ᴮ weightedSet label (fun i => (label i ∈ᴮ small) ⊓ weight i) at h
  simpa only [inf_comm] using h

theorem restriction_uncountable (hB : Flypitch.BA_CCC B) (context : B)
    (left right : I → bSet B)
    (hleft : ∀ i j, i ≠ j → (left i =ᴮ left j) = ⊥)
    (hright : ∀ i j, i ≠ j → (right i =ᴮ right j) = ⊥)
    (weight : I → B) (small : bSet B)
    (hsubset : context ≤ small ⊆ᴮ weightedSet left weight)
    (hlarge : context ≤ (injectsIntoValue (V B) small bSet.omega)ᶜ) :
    context ≤ (injectsIntoValue (V B)
      (weightedSet right (fun i => weight i ⊓ (left i ∈ᴮ small))) bSet.omega)ᶜ := by
  have hsub := restriction_contains context left weight small hsubset
  have hcount := subset_countable small (weightedSet left (fun i => weight i ⊓ (left i ∈ᴮ small)))
    (inf_le_left.trans hsub) inf_le_right
  have hzero : context ⊓ injectsIntoValue (V B)
      (weightedSet left (fun i => weight i ⊓ (left i ∈ᴮ small))) bSet.omega = ⊥ :=
    bot_unique ((le_inf (inf_le_left.trans hlarge) hcount).trans_eq compl_inf_eq_bot)
  have hnot : context ≤ (injectsIntoValue (V B)
      (weightedSet left (fun i => weight i ⊓ (left i ∈ᴮ small))) bSet.omega)ᶜ :=
    (le_compl_iff_disjoint_right).mpr (disjoint_iff.mpr hzero)
  rwa [countability_independent_of_labels hB left right hleft hright] at hnot

theorem exists_nonzero_intersection (context : B) (weight : I → B)
    (hcontext : context ≠ ⊥) (hcover : context ≤ ⨆ i, weight i) :
    ∃ i, context ⊓ weight i ≠ ⊥ := by
  classical
  by_contra h
  have hzero : ∀ i, context ⊓ weight i = ⊥ := by
    intro i
    exact not_not.mp (not_exists.mp h i)
  have hbound : context ≤ ⨆ i, context ⊓ weight i := by
    rw [← inf_iSup_eq]
    exact le_inf le_rfl hcover
  exact hcontext (bot_unique (by simpa only [hzero, iSup_bot] using hbound))

theorem exists_distinct_overlap (context : B) (left right : I → B)
    (hcontext : context ≠ ⊥)
    (hleft : context ≤
      (injectsIntoValue (V B) (weightedSet (BooleanPosetCoding.checkLabel (B := B)) left) bSet.omega)ᶜ)
    (hright : context ≤
      (injectsIntoValue (V B) (weightedSet (BooleanPosetCoding.checkLabel (B := B)) right) bSet.omega)ᶜ) :
    ∃ i j, i ≠ j ∧ (context ⊓ left i) ⊓ right j ≠ ⊥ := by
  classical
  have hleftCover : context ≤ ⨆ i, left i := by
    simpa using hleft.trans (uncountable_le_outside (BooleanPosetCoding.checkLabel (B := B))
      (fun _ _ h => BooleanPosetCoding.checkLabel_discrete h) left ∅ Set.countable_empty)
  obtain ⟨i, hi⟩ := exists_nonzero_intersection context left hcontext hleftCover
  have hrightCover : context ≤ ⨆ j : {j : I // j ≠ i}, right j.val := by
    have h := hright.trans (uncountable_le_outside (BooleanPosetCoding.checkLabel (B := B))
      (fun _ _ h => BooleanPosetCoding.checkLabel_discrete h) right {i} (Set.countable_singleton i))
    apply h.trans
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    exact le_iSup_of_le ⟨j, by simpa only [Set.mem_singleton_iff] using hj⟩ le_rfl
  obtain ⟨j, hj⟩ := exists_nonzero_intersection (context ⊓ left i)
    (fun j : {j : I // j ≠ i} => right j.val) hi (inf_le_left.trans hrightCover)
  exact ⟨i, j.val, j.property.symm, hj⟩

end Erdos597Object.BooleanWeightedSupports
