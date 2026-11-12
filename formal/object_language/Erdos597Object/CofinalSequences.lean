import Erdos597Object.StationaryLimits
import Erdos597Object.LimitCardinality

set_option backward.isDefEq.respectTransparency false

/-! Normal cofinal sequences and the general continuous-limit CCC theorem. -/

namespace Erdos597Object.CofinalSequences

open Set Order Cardinal
open scoped Cardinal
open BooleanDirectLimit MartinTransport IterationCardinals

section Normalization

variable {A D : Type} [LinearOrder A] [ConditionallyCompleteLinearOrderBot D]
  [SuccOrder D] [NoMaxOrder D] (f : A → D)

def successorsBelow (a : A) : Set D := (fun b => succ (f b)) '' Iio a

noncomputable def normalization (a : A) : D := sSup (successorsBelow f a)

theorem successorsBelow_bounded (hf : StrictMono f) (a : A) :
    BddAbove (successorsBelow f a) := by
  refine ⟨f a, ?_⟩
  rintro _ ⟨b, hba, rfl⟩
  exact succ_le_of_lt (hf hba)

theorem normalization_le (hf : StrictMono f) (a : A) : normalization f a ≤ f a := by
  apply csSup_le'
  rintro _ ⟨b, hba, rfl⟩
  exact succ_le_of_lt (hf hba)

theorem successor_le_normalization (hf : StrictMono f) {a b : A} (hba : b < a) :
    succ (f b) ≤ normalization f a :=
  le_csSup (successorsBelow_bounded f hf a) ⟨b, hba, rfl⟩

theorem normalization_strictMono (hf : StrictMono f) : StrictMono (normalization f) := by
  intro a b hab
  exact (normalization_le f hf a).trans_lt
    ((lt_succ_of_not_isMax (not_isMax (f a))).trans_le (successor_le_normalization f hf hab))

theorem normalization_isNormal (hf : StrictMono f) : Order.IsNormal (normalization f) := by
  refine ⟨normalization_strictMono f hf, ?_⟩
  intro a ha y hy
  apply csSup_le'
  rintro _ ⟨b, hba, rfl⟩
  obtain ⟨c, hbc, hca⟩ := ha.isSuccPrelimit.nonempty_Ioo_of_lt hba
  exact (successor_le_normalization f hf hbc).trans (hy ⟨c, hca, rfl⟩)

theorem normalization_isCofinal [NoMaxOrder A] (hf : StrictMono f)
    (hcofinal : IsCofinal (Set.range f)) : IsCofinal (Set.range (normalization f)) := by
  intro x
  obtain ⟨_, ⟨a, rfl⟩, hxa⟩ := hcofinal x
  obtain ⟨b, hab⟩ := exists_gt a
  refine ⟨normalization f b, ⟨b, rfl⟩, ?_⟩
  exact hxa.trans ((le_succ (f a)).trans (successor_le_normalization f hf hab))

end Normalization

section ContinuousSystem

variable {J : Type} [LinearOrder J] [WellFoundedLT J]
  {B : J → Type} [∀ j, CompleteBooleanAlgebra (B j)]
  (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
  [DirectedSystem B (e · · ·)]
  (hinj : ∀ i j h, Function.Injective (e i j h))

include hinj in
theorem ccc_of_small_cofinality (hB : ∀ j, Flypitch.BA_CCC (B j))
    (hcof : Order.cof J ≤ ℵ₀) : CountableChainCondition (Condition e) := by
  classical
  cases isEmpty_or_nonempty J with
  | inl hJ =>
      letI := hJ
      letI : IsEmpty (Condition e) := ⟨by
        intro p
        obtain ⟨r, _⟩ := exists_ofRaw e p
        exact isEmptyElim r.index⟩
      intro A _
      exact Set.to_countable A
  | inr hJ =>
      letI := hJ
      obtain ⟨s, hs, hsize⟩ := Order.exists_cof_eq J
      letI : Nonempty s := ⟨⟨hs.nonempty.choose, hs.nonempty.choose_spec⟩⟩
      letI : Countable s := Cardinal.mk_le_aleph0_iff.mp (hsize.trans_le hcof)
      obtain ⟨g, hg⟩ := exists_surjective_nat s
      apply BooleanLimitCCC.ccc_of_countable_cofinal e hinj hB (fun n => (g n).val)
      intro j
      obtain ⟨i, hi, hji⟩ := hs j
      obtain ⟨n, hn⟩ := hg ⟨i, hi⟩
      exact ⟨n, by simpa only [hn] using hji⟩

include hinj in
theorem ccc_of_aleph_one_cofinality (hB : ∀ j, Flypitch.BA_CCC (B j))
    (hcof : Order.cof J = ℵ₁)
    (hdensity : ∀ i, IsSuccLimit i → ∀ c : B i, c ≠ ⊥ →
      ∃ (j : J) (hji : j < i) (b : B j), b ≠ ⊥ ∧ e j i hji.le b ≤ c) :
    CountableChainCondition (Condition e) := by
  classical
  have hgt : ℵ₀ < Order.cof J := by simpa only [hcof] using Cardinal.aleph0_lt_aleph_one
  have hcard : 0 < #J := (Cardinal.aleph0_pos.trans hgt).trans_le (Order.cof_le_cardinalMk J)
  letI : Nonempty J := Cardinal.mk_ne_zero_iff.mp hcard.ne'
  letI : OrderBot J := WellFoundedLT.toOrderBot J
  letI : ConditionallyCompleteLinearOrderBot J := WellFoundedLT.conditionallyCompleteLinearOrderBot J
  letI : SuccOrder J := SuccOrder.ofLinearWellFoundedLT J
  letI : NoMaxOrder J := (noTopOrder_iff_noMaxOrder J).mp
    (Order.one_lt_cof_iff.mp (Cardinal.one_lt_aleph0.trans hgt))
  obtain ⟨s, hs, htype⟩ := Ordinal.exists_ord_cof_eq J
  have hcofs : Order.cof s = ℵ₁ := (Order.cof_eq_of_isCofinal hs).trans hcof
  letI : Nonempty s := ⟨⟨hs.nonempty.choose, hs.nonempty.choose_spec⟩⟩
  have hsone : 1 < Order.cof s := by
    simpa only [hcofs] using (Cardinal.one_lt_aleph0.trans Cardinal.aleph0_lt_aleph_one)
  letI : NoMaxOrder s := (noTopOrder_iff_noMaxOrder s).mp (Order.one_lt_cof_iff.mp hsone)
  letI : IsRegularCardinalOrder s := ⟨(htype.trans
    (congrArg Cardinal.ord (Order.cof_eq_of_isCofinal hs)).symm).le⟩
  let f : s → J := Subtype.val
  have hf : StrictMono f := Subtype.strictMono_coe s
  have hfcofinal : IsCofinal (Set.range f) := by
    intro j
    obtain ⟨i, hi, hji⟩ := hs j
    exact ⟨i, ⟨⟨i, hi⟩, rfl⟩, hji⟩
  let stages : s → J := normalization f
  have hnormal : Order.IsNormal stages := normalization_isNormal f hf
  have hcofinal : ∀ j, ∃ a, j ≤ stages a := by
    intro j
    obtain ⟨_, ⟨a, rfl⟩, hja⟩ := normalization_isCofinal f hf hfcofinal j
    exact ⟨a, hja⟩
  exact StationaryLimits.ccc_of_normal_cofinal e hinj hB hcofs stages hnormal hcofinal hdensity

include hinj in
theorem ccc_of_continuity (hB : ∀ j, Flypitch.BA_CCC (B j))
    (hdensity : ∀ i, IsSuccLimit i → ∀ c : B i, c ≠ ⊥ →
      ∃ (j : J) (hji : j < i) (b : B j), b ≠ ⊥ ∧ e j i hji.le b ≤ c) :
    CountableChainCondition (Condition e) := by
  rcases lt_trichotomy (Order.cof J) ℵ₁ with hsmall | heq | hlarge
  · exact ccc_of_small_cofinality e hinj hB (Cardinal.lt_aleph_one_iff.mp hsmall)
  · exact ccc_of_aleph_one_cofinality e hinj hB heq hdensity
  · exact BooleanLimitCCC.ccc_of_large_cofinality e hinj hB hlarge

include hinj in
theorem completion_ccc_of_continuity (hB : ∀ j, Flypitch.BA_CCC (B j))
    (hdensity : ∀ i, IsSuccLimit i → ∀ c : B i, c ≠ ⊥ →
      ∃ (j : J) (hji : j < i) (b : B j), b ≠ ⊥ ∧ e j i hji.le b ≤ c) :
    Flypitch.BA_CCC (PosetCompletion.Completion (Condition e)) :=
  PosetCompletion.completion_ccc (ccc_of_continuity e hinj hB hdensity)

include hinj in
theorem completion_card_le_of_continuity (hB : ∀ j, Flypitch.BA_CCC (B j))
    (hJ : #J ≤ iterationSize) (hsize : ∀ j, #(B j) ≤ iterationSize)
    (hdensity : ∀ i, IsSuccLimit i → ∀ c : B i, c ≠ ⊥ →
      ∃ (j : J) (hji : j < i) (b : B j), b ≠ ⊥ ∧ e j i hji.le b ≤ c) :
    #(PosetCompletion.Completion (Condition e)) ≤ iterationSize :=
  LimitCardinality.completion_card_le e hJ hsize (ccc_of_continuity e hinj hB hdensity)

end ContinuousSystem

end Erdos597Object.CofinalSequences
