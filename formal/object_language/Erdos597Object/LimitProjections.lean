import Erdos597Object.BooleanDirectLimit

set_option backward.isDefEq.respectTransparency false

/-! Projections from the direct-limit forcing to each Boolean-algebra stage. -/

namespace Erdos597Object.LimitProjections

open BooleanDirectLimit

variable {ι : Type} [Preorder ι] [IsDirectedOrder ι]
  {B : ι → Type} [∀ i, CompleteBooleanAlgebra (B i)]
  (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
  [DirectedSystem B (e · · ·)]
  (hinj : ∀ i j h, Function.Injective (e i j h))

theorem transition_comp {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) :
    e i k (hij.trans hjk) = (e j k hjk).comp (e i j hij) := by
  ext b
  exact (DirectedSystem.map_map' e hij hjk b).symm

include hinj in
theorem projection_later {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (b : B j) :
    BooleanProjection.projection (e i k (hij.trans hjk)) (e j k hjk b) =
      BooleanProjection.projection (e i j hij) b := by
  rw [transition_comp e hij hjk, BooleanProjection.projection_comp,
    BooleanProjection.projection_image _ (hinj j k hjk)]

noncomputable def commonUpper (i j : ι) : {k : ι // i ≤ k ∧ j ≤ k} :=
  ⟨Classical.choose (exists_ge_ge i j), Classical.choose_spec (exists_ge_ge i j)⟩

noncomputable def rawProjection (i : ι) (p : RawCondition e) : B i :=
  let upper := commonUpper i p.index
  BooleanProjection.projection (e i upper.val upper.property.1)
    (e p.index upper.val upper.property.2 p.value)

include hinj in
theorem rawProjection_eq (i : ι) (p : RawCondition e) (k : ι)
    (hik : i ≤ k) (hpk : p.index ≤ k) :
    rawProjection e i p = BooleanProjection.projection (e i k hik) (e p.index k hpk p.value) := by
  let upper := commonUpper i p.index
  obtain ⟨m, hum, hkm⟩ := exists_ge_ge upper.val k
  calc
    rawProjection e i p = BooleanProjection.projection (e i upper.val upper.property.1)
        (e p.index upper.val upper.property.2 p.value) := rfl
    _ = BooleanProjection.projection (e i m (hik.trans hkm))
        (e p.index m (hpk.trans hkm) p.value) := by
      have h := projection_later e hinj upper.property.1 hum
        (e p.index upper.val upper.property.2 p.value)
      simpa only [DirectedSystem.map_map' e] using h.symm
    _ = BooleanProjection.projection (e i k hik) (e p.index k hpk p.value) := by
      have h := projection_later e hinj hik hkm (e p.index k hpk p.value)
      simpa only [DirectedSystem.map_map' e] using h

include hinj in
theorem rawProjection_monotone (i : ι) : Monotone (rawProjection e i) := by
  rintro p q ⟨j, hpj, hqj, hle⟩
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  rw [rawProjection_eq e hinj i p k hik (hpj.trans hjk),
    rawProjection_eq e hinj i q k hik (hqj.trans hjk)]
  apply BooleanProjection.projection_monotone
  have h := OrderHomClass.monotone (e j k hjk) hle
  simpa only [DirectedSystem.map_map' e] using h

include hinj in
noncomputable def stageProjection (i : ι) : Condition e → B i :=
  Quotient.lift (rawProjection e i) (by
    intro p q hpq
    exact le_antisymm (rawProjection_monotone e hinj i hpq.1)
      (rawProjection_monotone e hinj i hpq.2))

theorem stageProjection_ofRaw (i : ι) (p : RawCondition e) :
    stageProjection e hinj i (ofRaw e p) = rawProjection e i p := rfl

theorem stageProjection_monotone (i : ι) : Monotone (stageProjection e hinj i) := by
  intro p q
  obtain ⟨r, rfl⟩ := exists_ofRaw e p
  obtain ⟨s, rfl⟩ := exists_ofRaw e q
  intro h
  exact rawProjection_monotone e hinj i h

theorem stageProjection_nonzero (i : ι) (p : Condition e) :
    stageProjection e hinj i p ≠ ⊥ := by
  obtain ⟨r, rfl⟩ := exists_ofRaw e p
  let upper := commonUpper i r.index
  change rawProjection e i r ≠ ⊥
  rw [rawProjection_eq e hinj i r upper.val upper.property.1 upper.property.2]
  exact BooleanProjection.projection_nonzero _ (mapped_nonzero e hinj upper.property.2 r.nonzero)

theorem stageProjection_ofStage (i : ι) (b : B i) (hb : b ≠ ⊥) :
    stageProjection e hinj i (ofStage e i b hb) = b := by
  change rawProjection e i ⟨i, b, hb⟩ = b
  rw [rawProjection_eq e hinj i _ i le_rfl le_rfl]
  exact BooleanProjection.projection_image _ (hinj i i le_rfl) b

theorem compatible_stage_iff (i : ι) (p : Condition e) (b : B i) (hb : b ≠ ⊥) :
    (∃ q : Condition e, q ≤ p ∧ q ≤ ofStage e i b hb) ↔
      stageProjection e hinj i p ⊓ b ≠ ⊥ := by
  obtain ⟨r, rfl⟩ := exists_ofRaw e p
  let upper := commonUpper i r.index
  change (∃ q : Condition e, q ≤ ofRaw e r ∧ q ≤ ofRaw e ⟨i, b, hb⟩) ↔ _
  rw [compatible_ofRaw_iff,
    raw_compatible_iff_at e hinj r ⟨i, b, hb⟩ upper.val upper.property.2 upper.property.1,
    stageProjection_ofRaw, rawProjection_eq e hinj i r upper.val upper.property.1 upper.property.2]
  exact BooleanProjection.inf_image_nonzero_iff (e i upper.val upper.property.1)
    (e r.index upper.val upper.property.2 r.value) b

theorem le_stage_iff (i : ι) (p : Condition e) (b : B i) (hb : b ≠ ⊥) :
    p ≤ ofStage e i b hb ↔ stageProjection e hinj i p ≤ b := by
  obtain ⟨r, rfl⟩ := exists_ofRaw e p
  let upper := commonUpper i r.index
  change RawLE e r ⟨i, b, hb⟩ ↔ rawProjection e i r ≤ b
  rw [rawLE_iff_at e hinj r ⟨i, b, hb⟩ upper.val upper.property.2 upper.property.1,
    rawProjection_eq e hinj i r upper.val upper.property.1 upper.property.2]
  exact (BooleanProjection.projection_le_iff (e i upper.val upper.property.1) _ b).symm

theorem stageProjection_comp {i j : ι} (hij : i ≤ j) (p : Condition e) :
    BooleanProjection.projection (e i j hij) (stageProjection e hinj j p) =
      stageProjection e hinj i p := by
  obtain ⟨r, rfl⟩ := exists_ofRaw e p
  let upper := commonUpper j r.index
  rw [stageProjection_ofRaw, stageProjection_ofRaw,
    rawProjection_eq e hinj j r upper.val upper.property.1 upper.property.2,
    rawProjection_eq e hinj i r upper.val (hij.trans upper.property.1) upper.property.2,
    transition_comp e hij upper.property.1, BooleanProjection.projection_comp]

end Erdos597Object.LimitProjections
