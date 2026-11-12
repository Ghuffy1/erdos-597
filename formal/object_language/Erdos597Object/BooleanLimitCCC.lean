import Erdos597Object.BooleanDirectLimit

set_option backward.isDefEq.respectTransparency false

/-! Countable-cofinality preservation of CCC for the direct-limit forcing. -/

namespace Erdos597Object.BooleanLimitCCC

open Set Cardinal
open scoped Cardinal
open Erdos597Object.MartinTransport Erdos597Object.BooleanDirectLimit

theorem nonzero_ccc {B : Type} [CompleteBooleanAlgebra B] (hB : Flypitch.BA_CCC B) :
    CountableChainCondition {b : B // b ≠ ⊥} := by
  intro A hA
  have hcount : (Subtype.val '' A : Set B).Countable := by
    apply hB
    · rintro _ ⟨b, hb, rfl⟩
      exact b.property
    · rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ hne
      by_contra hnonzero
      apply hA hb hc (fun h => hne (congrArg Subtype.val h))
      exact ⟨⟨b.val ⊓ c.val, hnonzero⟩, inf_le_left, inf_le_right⟩
  exact (Set.mapsTo_image (Subtype.val : {b : B // b ≠ ⊥} → B) A).countable_of_injOn
    Subtype.val_injective.injOn hcount

theorem antichain_inter_range_countable {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (hP : CountableChainCondition P) (f : P ↪o Q) (A : Set Q)
    (hA : A.Pairwise (fun p q => ¬ ∃ r : Q, r ≤ p ∧ r ≤ q)) :
    (A ∩ Set.range f).Countable := by
  have hpre : (f ⁻¹' A).Pairwise (fun p q => ¬ ∃ r : P, r ≤ p ∧ r ≤ q) := by
    rintro p hp q hq hpq ⟨r, hrp, hrq⟩
    exact hA hp hq (fun h => hpq (f.injective h))
      ⟨f r, f.monotone hrp, f.monotone hrq⟩
  have himage := (hP _ hpre).image f
  simpa only [Set.image_preimage_eq_inter_range] using himage

variable {ι : Type} [Preorder ι] [IsDirectedOrder ι]
  {B : ι → Type} [∀ i, CompleteBooleanAlgebra (B i)]
  (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
  [DirectedSystem B (e · · ·)]
  (hinj : ∀ i j h, Function.Injective (e i j h))

theorem antichain_stage_countable (hB : ∀ i, Flypitch.BA_CCC (B i))
    (A : Set (Condition e))
    (hA : A.Pairwise (fun p q => ¬ ∃ r : Condition e, r ≤ p ∧ r ≤ q)) (i : ι) :
    (A ∩ Set.range (stageEmbedding e hinj i)).Countable :=
  antichain_inter_range_countable (nonzero_ccc (hB i)) (stageEmbedding e hinj i) A hA

include hinj in
theorem ccc_of_countable_cofinal (hB : ∀ i, Flypitch.BA_CCC (B i))
    (stages : ℕ → ι) (hcofinal : ∀ i, ∃ n, i ≤ stages n) :
    CountableChainCondition (Condition e) := by
  intro A hA
  have hcover : A = ⋃ n, A ∩ Set.range (stageEmbedding e hinj (stages n)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, b, hb, rfl⟩ := exists_ofStage e p
      obtain ⟨n, hin⟩ := hcofinal i
      refine Set.mem_iUnion.mpr ⟨n, hp, ?_⟩
      refine ⟨⟨e i (stages n) hin b, mapped_nonzero e hinj hin hb⟩, ?_⟩
      exact (ofStage_map e hinj hin b hb).symm
    · intro hp
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
      exact hn.1
  rw [hcover]
  exact Set.countable_iUnion (fun n => antichain_stage_countable e hinj hB A hA (stages n))

include hinj in
theorem completion_ccc_of_countable_cofinal (hB : ∀ i, Flypitch.BA_CCC (B i))
    (stages : ℕ → ι) (hcofinal : ∀ i, ∃ n, i ≤ stages n) :
    Flypitch.BA_CCC (PosetCompletion.Completion (Condition e)) :=
  PosetCompletion.completion_ccc (ccc_of_countable_cofinal e hinj hB stages hcofinal)

include hinj in
theorem ccc_of_aleph_one_ranges_bounded (hB : ∀ i, Flypitch.BA_CCC (B i))
    (hbounded : ∀ f : (ℵ₁ : Cardinal.{0}).out → ι, ∃ j, ∀ a, f a ≤ j) :
    CountableChainCondition (Condition e) := by
  classical
  intro A hA
  by_contra huncountable
  have hcard : ℵ₁ ≤ #A := by
    apply Cardinal.aleph_one_le_iff.mpr
    apply lt_of_not_ge
    exact fun h => huncountable (Cardinal.le_aleph0_iff_set_countable.mp h)
  obtain ⟨embed⟩ : Nonempty ((ℵ₁ : Cardinal.{0}).out ↪ A) :=
    (Cardinal.le_def _ _).mp (by simpa only [Cardinal.mk_out] using hcard)
  let f : (ℵ₁ : Cardinal.{0}).out → Condition e := fun a => (embed a).val
  let raw : (ℵ₁ : Cardinal.{0}).out → RawCondition e :=
    fun a => representative e (f a)
  obtain ⟨j, hj⟩ := hbounded (fun a => (raw a).index)
  have hmaps : Set.MapsTo f Set.univ (A ∩ Set.range (stageEmbedding e hinj j)) := by
    intro a _
    refine ⟨(embed a).property, ?_⟩
    refine ⟨⟨e (raw a).index j (hj a) (raw a).value,
      mapped_nonzero e hinj (hj a) (raw a).nonzero⟩, ?_⟩
    change ofStage e j _ _ = f a
    rw [← ofStage_map e hinj (hj a) (raw a).value (raw a).nonzero]
    exact ofRaw_representative e (f a)
  have hfinjective : Function.Injective f := by
    intro a b h
    exact embed.injective (Subtype.ext h)
  have hcount : (Set.univ : Set (ℵ₁ : Cardinal.{0}).out).Countable :=
    hmaps.countable_of_injOn hfinjective.injOn (antichain_stage_countable e hinj hB A hA j)
  have hsmall : #((ℵ₁ : Cardinal.{0}).out) ≤ ℵ₀ :=
    Cardinal.mk_le_aleph0_iff.mpr (Set.countable_univ_iff.mp hcount)
  exact Cardinal.aleph0_lt_aleph_one.not_ge (by simpa only [Cardinal.mk_out] using hsmall)

include hinj in
theorem completion_ccc_of_aleph_one_ranges_bounded (hB : ∀ i, Flypitch.BA_CCC (B i))
    (hbounded : ∀ f : (ℵ₁ : Cardinal.{0}).out → ι, ∃ j, ∀ a, f a ≤ j) :
    Flypitch.BA_CCC (PosetCompletion.Completion (Condition e)) :=
  PosetCompletion.completion_ccc (ccc_of_aleph_one_ranges_bounded e hinj hB hbounded)

theorem ccc_of_large_cofinality {J : Type} [LinearOrder J]
    {C : J → Type} [∀ j, CompleteBooleanAlgebra (C j)]
    (f : ∀ i j, i ≤ j → CompleteLatticeHom (C i) (C j))
    [DirectedSystem C (f · · ·)]
    (hfinj : ∀ i j h, Function.Injective (f i j h))
    (hC : ∀ j, Flypitch.BA_CCC (C j)) (hcof : ℵ₁ < Order.cof J) :
    CountableChainCondition (Condition f) := by
  apply ccc_of_aleph_one_ranges_bounded f hfinj hC
  intro g
  have hsmall : #(Set.range g) ≤ ℵ₁ :=
    Cardinal.mk_range_le.trans_eq (Cardinal.mk_out _)
  have hnot : ¬ IsCofinal (Set.range g) := by
    intro h
    exact hcof.not_ge ((Order.cof_le h).trans hsmall)
  obtain ⟨j, hj⟩ := not_isCofinal_iff.mp hnot
  exact ⟨j, fun a => (hj (g a) ⟨a, rfl⟩).le⟩

theorem completion_ccc_of_large_cofinality {J : Type} [LinearOrder J]
    {C : J → Type} [∀ j, CompleteBooleanAlgebra (C j)]
    (f : ∀ i j, i ≤ j → CompleteLatticeHom (C i) (C j))
    [DirectedSystem C (f · · ·)]
    (hfinj : ∀ i j h, Function.Injective (f i j h))
    (hC : ∀ j, Flypitch.BA_CCC (C j)) (hcof : ℵ₁ < Order.cof J) :
    Flypitch.BA_CCC (PosetCompletion.Completion (Condition f)) :=
  PosetCompletion.completion_ccc (ccc_of_large_cofinality f hfinj hC hcof)

end Erdos597Object.BooleanLimitCCC
