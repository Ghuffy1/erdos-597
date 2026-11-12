import Erdos597Object.LimitProjections
import Erdos597Object.ProjectionCompletion

set_option backward.isDefEq.respectTransparency false

/-! Coherent complete embeddings into the Boolean completion of the direct limit. -/

namespace Erdos597Object.LimitEmbeddings

open Set TopologicalSpace
open Topology.WithLowerSet
open BooleanDirectLimit LimitProjections PosetCompletion ProjectionCompletion

variable {ι : Type} [Preorder ι] [IsDirectedOrder ι]
  {B : ι → Type} [∀ i, CompleteBooleanAlgebra (B i)]
  (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
  [DirectedSystem B (e · · ·)]
  (hinj : ∀ i j h, Function.Injective (e i j h))

noncomputable def limitProjection (i : ι) : PosetProjection (B i) (Condition e) where
  value := stageProjection e hinj i
  nonzero := stageProjection_nonzero e hinj i
  monotone := stageProjection_monotone e hinj i
  condition := ofStage e i
  condition_value := stageProjection_ofStage e hinj i
  compatible := compatible_stage_iff e hinj i

noncomputable def stageHom (i : ι) : CompleteLatticeHom (B i) (Completion (Condition e)) :=
  completeHom (limitProjection e hinj i)

theorem stageHom_injective (i : ι) : Function.Injective (stageHom e hinj i) :=
  completeHom_injective (limitProjection e hinj i)

theorem stageHom_coherent {i j : ι} (hij : i ≤ j) (b : B i) :
    stageHom e hinj i b = stageHom e hinj j (e i j hij b) := by
  apply Subtype.ext
  ext p
  change stageProjection e hinj i (ofLowerSet p) ≤ b ↔
    stageProjection e hinj j (ofLowerSet p) ≤ e i j hij b
  rw [← stageProjection_comp e hinj hij (ofLowerSet p)]
  exact BooleanProjection.projection_le_iff _ _ _

theorem stageHom_principal (i : ι) (b : B i) (hb : b ≠ ⊥) :
    stageHom e hinj i b = principal (ofStage e i b hb) := by
  apply le_antisymm
  · intro p hp
    have hle : ofLowerSet p ≤ ofStage e i b hb := (le_stage_iff e hinj i _ b hb).mpr hp
    exact cone_subset_principal (ofStage e i b hb) hle
  · exact principal_condition_le (limitProjection e hinj i) b hb

theorem stageHom_dense (u : Completion (Condition e)) (hu : u ≠ ⊥) :
    ∃ (i : ι) (b : B i), b ≠ ⊥ ∧ stageHom e hinj i b ≤ u := by
  obtain ⟨p, hp⟩ := principal_dense u hu
  obtain ⟨i, b, hb, rfl⟩ := exists_ofStage e p
  refine ⟨i, b, hb, ?_⟩
  rw [stageHom_principal e hinj i b hb]
  exact hp

end Erdos597Object.LimitEmbeddings
