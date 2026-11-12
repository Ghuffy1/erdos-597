import Erdos597Object.BooleanProjection
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.DirectedInverseSystem

set_option backward.isDefEq.respectTransparency false

/-! The forcing poset of the direct limit of a coherent system of Boolean algebras. -/

namespace Erdos597Object.BooleanDirectLimit

open Set DirectedSystem

variable {ι : Type} [Preorder ι] [IsDirectedOrder ι]
  {B : ι → Type} [∀ i, CompleteBooleanAlgebra (B i)]
  (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
  [DirectedSystem B (e · · ·)]

structure RawCondition (maps : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j)) where
  index : ι
  value : B index
  nonzero : value ≠ ⊥

def RawLE (p q : RawCondition e) : Prop :=
  ∃ (k : ι) (hp : p.index ≤ k) (hq : q.index ≤ k),
    e p.index k hp p.value ≤ e q.index k hq q.value

theorem rawLE_refl (p : RawCondition e) : RawLE e p p :=
  ⟨p.index, le_rfl, le_rfl, le_rfl⟩

theorem rawLE_trans {p q r : RawCondition e}
    (hpq : RawLE e p q) (hqr : RawLE e q r) : RawLE e p r := by
  obtain ⟨i, hpi, hqi, hpq⟩ := hpq
  obtain ⟨j, hqj, hrj, hqr⟩ := hqr
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  refine ⟨k, hpi.trans hik, hrj.trans hjk, ?_⟩
  have hpq' := OrderHomClass.monotone (e i k hik) hpq
  have hqr' := OrderHomClass.monotone (e j k hjk) hqr
  simp only [DirectedSystem.map_map' e] at hpq' hqr'
  exact hpq'.trans hqr'

instance rawPreorder : Preorder (RawCondition e) where
  le := RawLE e
  le_refl := rawLE_refl e
  le_trans _ _ _ := rawLE_trans e

def Condition := Antisymmetrization (RawCondition e) (fun p q => p ≤ q)

instance conditionPartialOrder : PartialOrder (Condition e) :=
  inferInstanceAs (PartialOrder (Antisymmetrization (RawCondition e) (· ≤ ·)))

def ofRaw (p : RawCondition e) : Condition e := toAntisymmetrization (fun p q => p ≤ q) p

noncomputable def representative (p : Condition e) : RawCondition e :=
  ofAntisymmetrization (fun p q => p ≤ q) p

theorem ofRaw_representative (p : Condition e) : ofRaw e (representative e p) = p :=
  toAntisymmetrization_ofAntisymmetrization (fun p q : RawCondition e => p ≤ q) p

def ofStage (i : ι) (b : B i) (hb : b ≠ ⊥) : Condition e := ofRaw e ⟨i, b, hb⟩

theorem exists_ofRaw (p : Condition e) : ∃ q, ofRaw e q = p :=
  ⟨representative e p, ofRaw_representative e p⟩

theorem ofRaw_le_iff (p q : RawCondition e) :
    ofRaw e p ≤ ofRaw e q ↔ RawLE e p q := Iff.rfl

variable (hinj : ∀ i j h, Function.Injective (e i j h))

include hinj in
theorem mapped_nonzero {i j : ι} (h : i ≤ j) {b : B i} (hb : b ≠ ⊥) : e i j h b ≠ ⊥ := by
  intro hzero
  apply hb
  apply hinj i j h
  simpa only [map_bot] using hzero

include hinj in
theorem rawLE_iff_at (p q : RawCondition e) (k : ι)
    (hp : p.index ≤ k) (hq : q.index ≤ k) :
    RawLE e p q ↔ e p.index k hp p.value ≤ e q.index k hq q.value := by
  constructor
  · rintro ⟨j, hpj, hqj, hle⟩
    obtain ⟨m, hkm, hjm⟩ := exists_ge_ge k j
    apply (BooleanProjection.map_le_map_iff (e k m hkm) (hinj k m hkm) _ _).mp
    have h := OrderHomClass.monotone (e j m hjm) hle
    simpa only [DirectedSystem.map_map' e] using h
  · intro hle
    exact ⟨k, hp, hq, hle⟩

include hinj in
theorem ofStage_le_iff (i : ι) (b c : B i) (hb : b ≠ ⊥) (hc : c ≠ ⊥) :
    ofStage e i b hb ≤ ofStage e i c hc ↔ b ≤ c := by
  change RawLE e ⟨i, b, hb⟩ ⟨i, c, hc⟩ ↔ b ≤ c
  rw [rawLE_iff_at e hinj _ _ i le_rfl le_rfl]
  simp only [DirectedSystem.map_self' e]

include hinj in
def stageEmbedding (i : ι) : {b : B i // b ≠ ⊥} ↪o Condition e where
  toFun b := ofStage e i b.val b.property
  inj' := by
    intro b c heq
    apply Subtype.ext
    exact le_antisymm ((ofStage_le_iff e hinj i b.val c.val b.property c.property).mp heq.le)
      ((ofStage_le_iff e hinj i c.val b.val c.property b.property).mp heq.ge)
  map_rel_iff' := by
    intro b c
    exact ofStage_le_iff e hinj i b.val c.val b.property c.property

include hinj in
theorem ofStage_map {i j : ι} (h : i ≤ j) (b : B i) (hb : b ≠ ⊥) :
    ofStage e i b hb = ofStage e j (e i j h b) (mapped_nonzero e hinj h hb) := by
  apply le_antisymm
  · change RawLE e ⟨i, b, hb⟩ ⟨j, e i j h b, _⟩
    refine ⟨j, h, le_rfl, ?_⟩
    simp only [DirectedSystem.map_self' e]
    exact le_rfl
  · change RawLE e ⟨j, e i j h b, _⟩ ⟨i, b, hb⟩
    refine ⟨j, le_rfl, h, ?_⟩
    simp only [DirectedSystem.map_self' e]
    exact le_rfl

theorem compatible_ofRaw_iff (p q : RawCondition e) :
    (∃ r : Condition e, r ≤ ofRaw e p ∧ r ≤ ofRaw e q) ↔
      ∃ r : RawCondition e, RawLE e r p ∧ RawLE e r q := by
  constructor
  · rintro ⟨r, hrp, hrq⟩
    obtain ⟨s, rfl⟩ := exists_ofRaw e r
    exact ⟨s, hrp, hrq⟩
  · rintro ⟨r, hrp, hrq⟩
    exact ⟨ofRaw e r, hrp, hrq⟩

include hinj in
theorem raw_compatible_iff_at (p q : RawCondition e) (k : ι)
    (hp : p.index ≤ k) (hq : q.index ≤ k) :
    (∃ r : RawCondition e, RawLE e r p ∧ RawLE e r q) ↔
      e p.index k hp p.value ⊓ e q.index k hq q.value ≠ ⊥ := by
  constructor
  · rintro ⟨r, hrp, hrq⟩ hzero
    obtain ⟨m, hrm, hkm⟩ := exists_ge_ge r.index k
    have hrp' := (rawLE_iff_at e hinj r p m hrm (hp.trans hkm)).mp hrp
    have hrq' := (rawLE_iff_at e hinj r q m hrm (hq.trans hkm)).mp hrq
    have hbound : e r.index m hrm r.value ≤
        e k m hkm (e p.index k hp p.value ⊓ e q.index k hq q.value) := by
      rw [map_inf]
      simp only [DirectedSystem.map_map' e]
      exact le_inf hrp' hrq'
    rw [hzero, map_bot] at hbound
    exact mapped_nonzero e hinj hrm r.nonzero (bot_unique hbound)
  · intro hnonzero
    let r : RawCondition e :=
      ⟨k, e p.index k hp p.value ⊓ e q.index k hq q.value, hnonzero⟩
    refine ⟨r, ⟨k, le_rfl, hp, ?_⟩, ⟨k, le_rfl, hq, ?_⟩⟩
    · simpa only [r, DirectedSystem.map_self' e] using
        (inf_le_left : r.value ≤ e p.index k hp p.value)
    · simpa only [r, DirectedSystem.map_self' e] using
        (inf_le_right : r.value ≤ e q.index k hq q.value)

include hinj in
theorem compatible_ofStage_iff (i : ι) (b c : B i) (hb : b ≠ ⊥) (hc : c ≠ ⊥) :
    (∃ r : Condition e, r ≤ ofStage e i b hb ∧ r ≤ ofStage e i c hc) ↔ b ⊓ c ≠ ⊥ := by
  rw [ofStage, ofStage, compatible_ofRaw_iff,
    raw_compatible_iff_at e hinj _ _ i le_rfl le_rfl]
  simp only [DirectedSystem.map_self' e]

theorem exists_ofStage (p : Condition e) : ∃ i b hb, ofStage e i b hb = p := by
  obtain ⟨r, hr⟩ := exists_ofRaw e p
  exact ⟨r.index, r.value, r.nonzero, hr⟩

end Erdos597Object.BooleanDirectLimit
