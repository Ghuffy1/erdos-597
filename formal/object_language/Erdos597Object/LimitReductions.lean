import Erdos597Object.LimitEmbeddings

set_option backward.isDefEq.respectTransparency false

/-! Compatibility transfers through projections to an earlier forcing stage. -/

namespace Erdos597Object.LimitReductions

open BooleanDirectLimit LimitProjections

variable {ι : Type} [Preorder ι] [IsDirectedOrder ι]
  {B : ι → Type} [∀ i, CompleteBooleanAlgebra (B i)]
  (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
  [DirectedSystem B (e · · ·)]
  (hinj : ∀ i j h, Function.Injective (e i j h))

theorem stageProjection_ofStage_above {i j : ι} (hij : i ≤ j) (b : B j) (hb : b ≠ ⊥) :
    stageProjection e hinj i (ofStage e j b hb) = BooleanProjection.projection (e i j hij) b := by
  change rawProjection e i ⟨j, b, hb⟩ = _
  rw [rawProjection_eq e hinj i _ j hij le_rfl]
  simp only [DirectedSystem.map_self' e]

theorem pullback_bound {i j : ι} (hij : i ≤ j) (p : Condition e) (b : B i)
    (h : e i j hij b ≤ stageProjection e hinj j p) : b ≤ stageProjection e hinj i p := by
  have hprojection := BooleanProjection.projection_monotone (e i j hij) h
  rw [BooleanProjection.projection_image _ (hinj i j hij), stageProjection_comp e hinj hij p]
    at hprojection
  exact hprojection

theorem compatible_of_reductions {i j : ι} (hij : i ≤ j) (p q : Condition e)
    (hp : ∃ (c : B j) (hc : c ≠ ⊥), ofStage e j c hc = p)
    (a b : B i) (ha : a ≤ stageProjection e hinj i p)
    (hb : e i j hij b ≤ stageProjection e hinj j q) (hab : a ⊓ b ≠ ⊥) :
    ∃ r : Condition e, r ≤ p ∧ r ≤ q := by
  obtain ⟨c, hc, rfl⟩ := hp
  have hleft : stageProjection e hinj i (ofStage e j c hc) ⊓ b ≠ ⊥ := by
    intro hzero
    apply hab
    exact bot_unique ((inf_le_inf_right b ha).trans hzero.le)
  rw [stageProjection_ofStage_above e hinj hij c hc] at hleft
  have hmiddle : c ⊓ e i j hij b ≠ ⊥ :=
    (BooleanProjection.inf_image_nonzero_iff (e i j hij) c b).mpr hleft
  have hright : stageProjection e hinj j q ⊓ c ≠ ⊥ := by
    intro hzero
    apply hmiddle
    apply bot_unique
    calc
      c ⊓ e i j hij b ≤ c ⊓ stageProjection e hinj j q := inf_le_inf_left c hb
      _ = ⊥ := by simpa only [inf_comm] using hzero
  obtain ⟨r, hrq, hrp⟩ := (compatible_stage_iff e hinj j q c hc).mpr hright
  exact ⟨r, hrp, hrq⟩

end Erdos597Object.LimitReductions
