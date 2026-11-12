import Erdos597Object.OriginalPartition
import Mathlib.Order.Shrink

set_option backward.isDefEq.respectTransparency false

/-! Transport and normalization of the Martin-axiom formulation. -/

namespace Erdos597Object.MartinTransport

open Cardinal Set
open scoped Cardinal

def CountableChainCondition (P : Type*) [PartialOrder P] : Prop :=
  ∀ A : Set P, A.Pairwise (fun p q => ¬ ∃ r : P, r ≤ p ∧ r ≤ q) → A.Countable

theorem ccc_original_iff (P : Type) [PartialOrder P] :
    CountableChainCondition P ↔ Erdos597.CountableChainCondition P := Iff.rfl

theorem ccc_map_orderIso {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) (h : CountableChainCondition P) : CountableChainCondition Q := by
  intro A hA
  have hpre : (e ⁻¹' A).Pairwise (fun p q => ¬ ∃ r : P, r ≤ p ∧ r ≤ q) := by
    intro x hx y hy hxy hcommon
    obtain ⟨z, hzx, hzy⟩ := hcommon
    exact hA hx hy (fun heq => hxy (e.injective heq))
      ⟨e z, e.monotone hzx, e.monotone hzy⟩
  have himage := (h _ hpre).image e
  simpa only [Set.image_preimage_eq _ e.surjective] using himage

theorem ccc_orderIso_iff {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) : CountableChainCondition P ↔ CountableChainCondition Q :=
  ⟨ccc_map_orderIso e, ccc_map_orderIso e.symm⟩

noncomputable def pullbackFilter {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) (F : Order.PFilter Q) : Order.PFilter P :=
  (Order.IsPFilter.of_def
    (by
      obtain ⟨q, hq⟩ := F.nonempty
      exact ⟨e.symm q, by simpa using hq⟩)
    (by
      intro x hx y hy
      obtain ⟨q, hq, hqx, hqy⟩ := F.directed (e x) hx (e y) hy
      refine ⟨e.symm q, by simpa using hq, ?_, ?_⟩
      · simpa using e.symm.monotone hqx
      · simpa using e.symm.monotone hqy)
    (by
      intro x y hxy hx
      exact F.mem_of_le (e.monotone hxy) hx) : Order.IsPFilter (e ⁻¹' (F : Set Q))).toPFilter

@[simp] theorem mem_pullbackFilter {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) (F : Order.PFilter Q) (p : P) :
    p ∈ pullbackFilter e F ↔ e p ∈ F := Iff.rfl

theorem small_martin_axiom (h : Erdos597.MartinAxiomAlephOne)
    (P : Type*) [PartialOrder P] [Small.{0} P] (hccc : CountableChainCondition P)
    (I : Type*) [Small.{0} I] (hcard : #(Shrink.{0} I) ≤ ℵ₁)
    (D : I → Set P) (hdense : ∀ i p, ∃ q ∈ D i, q ≤ p) (p : P) :
    ∃ F : Order.PFilter P, p ∈ F ∧ ∀ i, ∃ q ∈ F, q ∈ D i := by
  let e : P ≃o Shrink.{0} P := orderIsoShrink P
  let d : Equiv I (Shrink.{0} I) := equivShrink I
  have hccc' : Erdos597.CountableChainCondition (Shrink.{0} P) :=
    (ccc_original_iff _).mp (ccc_map_orderIso e hccc)
  let D' : Shrink.{0} I → Set (Shrink.{0} P) := fun i => e.symm ⁻¹' D (d.symm i)
  have hdense' : ∀ i q, ∃ r ∈ D' i, r ≤ q := by
    intro i q
    obtain ⟨r, hr, hrq⟩ := hdense (d.symm i) (e.symm q)
    exact ⟨e r, by simpa [D'] using hr, by simpa using e.monotone hrq⟩
  obtain ⟨F, hp, hF⟩ := h (Shrink.{0} P) hccc' (Shrink.{0} I) hcard D' hdense' (e p)
  refine ⟨pullbackFilter e F, hp, ?_⟩
  intro i
  obtain ⟨q, hq, hqD⟩ := hF (d i)
  exact ⟨e.symm q, by simpa using hq, by simpa [D'] using hqD⟩

def UnbasedMartinAxiomAlephOne : Prop :=
  ∀ (P : Type) [PartialOrder P], Nonempty P → Erdos597.CountableChainCondition P →
    ∀ (I : Type), #I ≤ ℵ₁ → ∀ D : I → Set P,
      (∀ i p, ∃ q ∈ D i, q ≤ p) → ∃ F : Order.PFilter P, ∀ i, ∃ q ∈ F, q ∈ D i

theorem based_to_unbased (h : Erdos597.MartinAxiomAlephOne) :
    UnbasedMartinAxiomAlephOne := by
  intro P inst hP hccc I hI D hD
  obtain ⟨F, _, hF⟩ := h P hccc I hI D hD hP.some
  exact ⟨F, hF⟩

theorem ccc_below {P : Type*} [PartialOrder P] (h : CountableChainCondition P) (p : P) :
    CountableChainCondition {q : P // q ≤ p} := by
  intro A hA
  have himage : (Subtype.val '' A).Pairwise (fun x y => ¬ ∃ z : P, z ≤ x ∧ z ≤ y) := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ hab ⟨z, hza, hzb⟩
    exact hA ha hb (fun h => hab (congrArg Subtype.val h))
      ⟨⟨z, hza.trans a.property⟩, hza, hzb⟩
  have hc := h _ himage
  have hmaps : Set.MapsTo (fun q : {q : P // q ≤ p} => q.val) A (Subtype.val '' A) :=
    fun q hq => ⟨q, hq, rfl⟩
  exact hmaps.countable_of_injOn Subtype.val_injective.injOn hc

theorem unbased_to_based (h : UnbasedMartinAxiomAlephOne) :
    Erdos597.MartinAxiomAlephOne := by
  intro P inst hccc I hI D hD p
  let Q := {q : P // q ≤ p}
  have hQ : Nonempty Q := ⟨⟨p, le_rfl⟩⟩
  have hcccQ : Erdos597.CountableChainCondition Q :=
    (ccc_original_iff _).mp (ccc_below ((ccc_original_iff _).mpr hccc) p)
  let D' : I → Set Q := fun i => Subtype.val ⁻¹' D i
  have hdense : ∀ i q, ∃ r ∈ D' i, r ≤ q := by
    intro i q
    obtain ⟨r, hrD, hrq⟩ := hD i q.val
    exact ⟨⟨r, hrq.trans q.property⟩, hrD, hrq⟩
  obtain ⟨F, hF⟩ := h Q hQ hcccQ I hI D' hdense
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
  refine ⟨hfilter.toPFilter, ?_, ?_⟩
  · obtain ⟨r, hr⟩ := F.nonempty
    exact ⟨r, hr, r.property⟩
  · intro i
    obtain ⟨r, hr, hrD⟩ := hF i
    exact ⟨r.val, ⟨r, hr, le_rfl⟩, hrD⟩

theorem based_unbased_iff :
    Erdos597.MartinAxiomAlephOne ↔ UnbasedMartinAxiomAlephOne :=
  ⟨based_to_unbased, unbased_to_based⟩

end Erdos597Object.MartinTransport
