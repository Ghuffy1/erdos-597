import Erdos597Object.MartinTransport
import Mathlib.SetTheory.Cardinal.Arithmetic

set_option backward.isDefEq.respectTransparency false

/-!
Reduction of Martin's axiom at aleph-one to posets of size at most aleph-one.
The hull preserves compatibility and all the specified dense requirements.
This is a reduction used in a forcing construction of Martin's axiom.
-/

namespace Erdos597Object.SmallMartin

open Cardinal Set
open scoped Cardinal
open Erdos597Object.MartinTransport

section Hull

variable {P I : Type}

def hullStage (seed : P) (combine : P → P → P) (step : I → P → P) : ℕ → Set P
  | 0 => {seed}
  | n + 1 =>
      hullStage seed combine step n ∪
        Set.image2 combine (hullStage seed combine step n) (hullStage seed combine step n) ∪
        ⋃ i, step i '' hullStage seed combine step n

def hull (seed : P) (combine : P → P → P) (step : I → P → P) : Set P :=
  ⋃ n, hullStage seed combine step n

theorem hullStage_subset_succ (seed : P) (combine : P → P → P) (step : I → P → P)
    (n : ℕ) : hullStage seed combine step n ⊆ hullStage seed combine step (n + 1) :=
  fun _ hx => Or.inl (Or.inl hx)

theorem hullStage_monotone (seed : P) (combine : P → P → P) (step : I → P → P) :
    Monotone (hullStage seed combine step) :=
  monotone_nat_of_le_succ (hullStage_subset_succ seed combine step)

theorem seed_mem_hull (seed : P) (combine : P → P → P) (step : I → P → P) :
    seed ∈ hull seed combine step :=
  Set.mem_iUnion.mpr ⟨0, rfl⟩

theorem combine_mem_hull (seed : P) (combine : P → P → P) (step : I → P → P)
    {x y : P} (hx : x ∈ hull seed combine step) (hy : y ∈ hull seed combine step) :
    combine x y ∈ hull seed combine step := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
  have hm' := hullStage_monotone seed combine step (Nat.le_max_left m n) hm
  have hn' := hullStage_monotone seed combine step (Nat.le_max_right m n) hn
  exact Set.mem_iUnion.mpr ⟨max m n + 1, Or.inl (Or.inr ⟨x, hm', y, hn', rfl⟩)⟩

theorem step_mem_hull (seed : P) (combine : P → P → P) (step : I → P → P)
    (i : I) {x : P} (hx : x ∈ hull seed combine step) :
    step i x ∈ hull seed combine step := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr (Set.mem_iUnion.mpr ⟨i, x, hn, rfl⟩)⟩

theorem union_card_le_aleph_one {s t : Set P} (hs : #s ≤ ℵ₁) (ht : #t ≤ ℵ₁) :
    #(s ∪ t : Set P) ≤ ℵ₁ := by
  calc
    #(s ∪ t : Set P) ≤ #s + #t := Cardinal.mk_union_le s t
    _ ≤ ℵ₁ + ℵ₁ := add_le_add hs ht
    _ = ℵ₁ := Cardinal.add_eq_self (Cardinal.aleph0_le_aleph 1)

theorem indexed_union_card_le_aleph_one (hI : #I ≤ ℵ₁) (s : I → Set P)
    (hs : ∀ i, #(s i) ≤ ℵ₁) : #(⋃ i, s i) ≤ ℵ₁ := by
  calc
    #(⋃ i, s i) ≤ #I * ⨆ i, #(s i) := Cardinal.mk_iUnion_le s
    _ ≤ ℵ₁ * ℵ₁ := mul_le_mul' hI (ciSup_le' hs)
    _ = ℵ₁ := Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)

theorem hullStage_card (seed : P) (combine : P → P → P) (step : I → P → P)
    (hI : #I ≤ ℵ₁) (n : ℕ) : #(hullStage seed combine step n) ≤ ℵ₁ := by
  induction n with
  | zero =>
    simpa [hullStage] using
      (Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_aleph 1))
  | succ n ih =>
    apply union_card_le_aleph_one
    · apply union_card_le_aleph_one ih
      calc
        #(Set.image2 combine (hullStage seed combine step n)
            (hullStage seed combine step n)) ≤
            #(hullStage seed combine step n) * #(hullStage seed combine step n) :=
          Cardinal.mk_image2_le
        _ ≤ ℵ₁ * ℵ₁ := mul_le_mul' ih ih
        _ = ℵ₁ := Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)
    · apply indexed_union_card_le_aleph_one hI
      intro i
      exact Cardinal.mk_image_le.trans ih

theorem hull_card (seed : P) (combine : P → P → P) (step : I → P → P)
    (hI : #I ≤ ℵ₁) : #(hull seed combine step) ≤ ℵ₁ := by
  apply indexed_union_card_le_aleph_one (I := ℕ)
  · simp
  · exact hullStage_card seed combine step hI

end Hull

theorem exists_small_compatible_subposet {P I : Type} [PartialOrder P]
    (hI : #I ≤ ℵ₁) (D : I → Set P) (hD : ∀ i p, ∃ q ∈ D i, q ≤ p) (seed : P) :
    ∃ Q : Set P, seed ∈ Q ∧ #Q ≤ ℵ₁ ∧
      (∀ x ∈ Q, ∀ y ∈ Q, (∃ r : P, r ≤ x ∧ r ≤ y) →
        ∃ r ∈ Q, r ≤ x ∧ r ≤ y) ∧
      (∀ i x, x ∈ Q → ∃ y ∈ Q, y ∈ D i ∧ y ≤ x) := by
  classical
  let combine (x y : P) : P :=
    if h : ∃ r : P, r ≤ x ∧ r ≤ y then h.choose else seed
  let step (i : I) (x : P) : P := (hD i x).choose
  refine ⟨hull seed combine step, seed_mem_hull seed combine step,
    hull_card seed combine step hI, ?_, ?_⟩
  · intro x hx y hy hxy
    refine ⟨combine x y, combine_mem_hull seed combine step hx hy, ?_⟩
    simpa only [combine, dite_eq_left hxy] using hxy.choose_spec
  · intro i x hx
    exact ⟨step i x, step_mem_hull seed combine step i hx,
      (hD i x).choose_spec⟩

theorem ccc_subposet {P : Type} [PartialOrder P] (hP : CountableChainCondition P)
    (Q : Set P)
    (hcompat : ∀ x ∈ Q, ∀ y ∈ Q, (∃ r : P, r ≤ x ∧ r ≤ y) →
      ∃ r ∈ Q, r ≤ x ∧ r ≤ y) : CountableChainCondition Q := by
  intro A hA
  have himage : (Subtype.val '' A).Pairwise (fun x y => ¬ ∃ r : P, r ≤ x ∧ r ≤ y) := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ hab hcommon
    obtain ⟨r, hr, hra, hrb⟩ := hcompat a.val a.property b.val b.property hcommon
    exact hA ha hb (fun h => hab (congrArg Subtype.val h)) ⟨⟨r, hr⟩, hra, hrb⟩
  have hcount := hP _ himage
  have hmaps : Set.MapsTo (fun q : Q => q.val) A (Subtype.val '' A) :=
    fun q hq => ⟨q, hq, rfl⟩
  exact hmaps.countable_of_injOn Subtype.val_injective.injOn hcount

def SmallPosetMartinAxiomAlephOne : Prop :=
  ∀ (P : Type) [PartialOrder P], #P ≤ ℵ₁ → CountableChainCondition P →
    ∀ (I : Type), #I ≤ ℵ₁ → ∀ D : I → Set P,
      (∀ i p, ∃ q ∈ D i, q ≤ p) →
        ∀ p : P, ∃ F : Order.PFilter P, p ∈ F ∧ ∀ i, ∃ q ∈ F, q ∈ D i

theorem small_poset_martin_of_martin (h : Erdos597.MartinAxiomAlephOne) :
    SmallPosetMartinAxiomAlephOne := by
  intro P inst _ hP I hI D hD p
  exact h P ((ccc_original_iff P).mp hP) I hI D hD p

theorem martin_of_small_poset_martin (h : SmallPosetMartinAxiomAlephOne) :
    Erdos597.MartinAxiomAlephOne := by
  intro P inst hP I hI D hD p
  obtain ⟨Q, hpQ, hQ, hcompat, hdense⟩ := exists_small_compatible_subposet hI D hD p
  have hcccQ : CountableChainCondition Q :=
    ccc_subposet ((ccc_original_iff P).mpr hP) Q hcompat
  let D' : I → Set Q := fun i => Subtype.val ⁻¹' D i
  have hD' : ∀ i q, ∃ r ∈ D' i, r ≤ q := by
    intro i q
    obtain ⟨r, hrQ, hrD, hrq⟩ := hdense i q.val q.property
    exact ⟨⟨r, hrQ⟩, hrD, hrq⟩
  obtain ⟨F, hp, hF⟩ := h Q hQ hcccQ I hI D' hD' ⟨p, hpQ⟩
  let A : Set P := {q | ∃ r ∈ F, r.val ≤ q}
  have hfilter : Order.IsPFilter A := Order.IsPFilter.of_def
    (by
      obtain ⟨r, hr⟩ := F.nonempty
      exact ⟨r.val, r, hr, le_rfl⟩)
    (by
      rintro x ⟨a, ha, hax⟩ y ⟨b, hb, hby⟩
      obtain ⟨c, hc, hca, hcb⟩ := F.directed a ha b hb
      exact ⟨c.val, ⟨c, hc, le_rfl⟩,
        (show c.val ≤ a.val from hca).trans hax,
        (show c.val ≤ b.val from hcb).trans hby⟩)
    (by
      rintro x y hxy ⟨r, hr, hrx⟩
      exact ⟨r, hr, hrx.trans hxy⟩)
  refine ⟨hfilter.toPFilter, ⟨⟨p, hpQ⟩, hp, le_rfl⟩, ?_⟩
  intro i
  obtain ⟨r, hr, hrD⟩ := hF i
  exact ⟨r.val, ⟨r, hr, le_rfl⟩, hrD⟩

theorem martin_iff_small_poset_martin :
    Erdos597.MartinAxiomAlephOne ↔ SmallPosetMartinAxiomAlephOne :=
  ⟨small_poset_martin_of_martin, martin_of_small_poset_martin⟩

end Erdos597Object.SmallMartin
