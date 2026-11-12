import Erdos597Object.ScheduledCoverage

set_option backward.isDefEq.respectTransparency false

/-! Identifying a selected successor completion with its place in the global iteration. -/

namespace Erdos597Object.SuccessorBridge

open Set Order
open CanonicalIteration IterationSystems SystemRestrictions SystemGluing PrefixExtensions
open ScheduledIteration IterationPrefixes AlgebraTransport

theorem successorIso_endpoint (j : Index) :
    (successorIso j).symm (endpoint (succ j)) = ⊤ := by
  change (successorIso j).symm ⊤ = ⊤
  exact (successorIso j).symm.map_top

theorem successorPrefix_object {L : Type} (j : Index) (S : Prefix j)
    (P : BooleanIteration.BooleanPoset (S.system.obj (endpoint j)) L)
    (hccc : MartinTransport.CountableChainCondition (BooleanIteration.Condition P))
    (hL : Cardinal.mk L ≤ Cardinal.aleph 1) (hcover : (⨆ a, P.member a) = ⊤) :
    (successorPrefix j S P hccc hL hcover).system.obj (endpoint (succ j)) =
      S.system.successorAlgebra (endpoint j) P hccc hL hcover := by
  change (S.system.successor (endpoint j) (fun a => a.property) P hccc hL hcover).obj
    ((successorIso j).symm (endpoint (succ j))) = _
  rw [successorIso_endpoint]
  rfl

theorem successorPrefix_map {L : Type} (j : Index) (S : Prefix j)
    (P : BooleanIteration.BooleanPoset (S.system.obj (endpoint j)) L)
    (hccc : MartinTransport.CountableChainCondition (BooleanIteration.Condition P))
    (hL : Cardinal.mk L ≤ Cardinal.aleph 1) (hcover : (⨆ a, P.member a) = ⊤) :
    HEq ((successorPrefix j S P hccc hL hcover).system.map
      ⟨j, Set.mem_Iic.mpr (le_succ j)⟩ (endpoint (succ j)) (le_succ j))
      (CompletionEmbedding.baseHom P) := by
  let T := S.system.successor (endpoint j) (fun a => a.property) P hccc hL hcover
  change HEq (T.map ((successorIso j).symm ⟨j, Set.mem_Iic.mpr (le_succ j)⟩)
    ((successorIso j).symm (endpoint (succ j))) _) _
  have hfirst : (successorIso j).symm ⟨j, Set.mem_Iic.mpr (le_succ j)⟩ =
      ((endpoint j : Iic j) : WithTop (Iic j)) :=
    successorIso_symm_coe j (endpoint j)
  refine (map_heq_of_indices T hfirst (successorIso_endpoint j) _ le_top).trans ?_
  change HEq ((CompletionEmbedding.baseHom P).comp
    (S.system.map (endpoint j) (endpoint j) le_rfl)) (CompletionEmbedding.baseHom P)
  apply heq_of_eq
  ext b
  change CompletionEmbedding.baseHom P (S.system.map (endpoint j) (endpoint j) le_rfl b) = _
  exact congrArg (CompletionEmbedding.baseHom P) (DirectedSystem.map_self' S.system.map b)

theorem prefix_successor_of_step (j : Index)
    (step : TransfiniteSystems.NextStep (ScheduledIteration.system.obj j))
    (hstep : ScheduledIteration.next j (stagePrefix j) = step) :
    stagePrefix (succ j) = successorPrefix j (stagePrefix j) step.forcing step.ccc step.card_le step.cover := by
  cases hstep
  exact prefix_successor j

theorem successor_object (j : Index)
    (step : TransfiniteSystems.NextStep (ScheduledIteration.system.obj j))
    (hstep : ScheduledIteration.next j (stagePrefix j) = step) :
    ScheduledIteration.system.obj (succ j) =
      (stagePrefix j).system.successorAlgebra (endpoint j) step.forcing step.ccc step.card_le step.cover := by
  calc
    ScheduledIteration.system.obj (succ j) =
        (stagePrefix (succ j)).system.obj (endpoint (succ j)) := rfl
    _ = (successorPrefix j (stagePrefix j) step.forcing step.ccc step.card_le step.cover).system.obj
        (endpoint (succ j)) :=
      congrArg (fun S : Prefix (succ j) => S.system.obj (endpoint (succ j)))
        (prefix_successor_of_step j step hstep)
    _ = _ := successorPrefix_object j (stagePrefix j) step.forcing step.ccc step.card_le step.cover

theorem successor_map_heq (j : Index)
    (step : TransfiniteSystems.NextStep (ScheduledIteration.system.obj j))
    (hstep : ScheduledIteration.next j (stagePrefix j) = step) :
    HEq (ScheduledIteration.system.map j (succ j) (le_succ j))
      (CompletionEmbedding.baseHom step.forcing) := by
  have hglobal := system_map_heq (global_restrict (succ j))
    (⟨j, Set.mem_Iic.mpr (le_succ j)⟩ : Iic (succ j)) (endpoint (succ j)) (le_succ j)
  have hprefix := system_map_heq (congrArg Prefix.system (prefix_successor_of_step j step hstep))
    (⟨j, Set.mem_Iic.mpr (le_succ j)⟩ : Iic (succ j)) (endpoint (succ j)) (le_succ j)
  exact hglobal.trans (hprefix.trans
    (successorPrefix_map j (stagePrefix j) step.forcing step.ccc step.card_le step.cover))

theorem successor_embedding (j : Index)
    (step : TransfiniteSystems.NextStep (ScheduledIteration.system.obj j))
    (hstep : ScheduledIteration.next j (stagePrefix j) = step) :
    (castHom (successor_object j step hstep)).comp
      (ScheduledIteration.system.map j (succ j) (le_succ j)) =
      CompletionEmbedding.baseHom step.forcing := by
  apply eq_of_heq
  change HEq (transportMap rfl (successor_object j step hstep)
    (ScheduledIteration.system.map j (succ j) (le_succ j))) _
  exact (transportMap_heq rfl (successor_object j step hstep) _).trans
    (successor_map_heq j step hstep)

noncomputable def completionToFinal (j : Index)
    (step : TransfiniteSystems.NextStep (ScheduledIteration.system.obj j))
    (hstep : ScheduledIteration.next j (stagePrefix j) = step) :
    CompleteLatticeHom (PosetCompletion.Completion (BooleanIteration.Condition step.forcing))
      ScheduledIteration.finalAlgebra :=
  (ScheduledCoverage.finalEmbedding (succ j)).comp (castHom (successor_object j step hstep).symm)

theorem completionToFinal_injective (j : Index)
    (step : TransfiniteSystems.NextStep (ScheduledIteration.system.obj j))
    (hstep : ScheduledIteration.next j (stagePrefix j) = step) :
    Function.Injective (completionToFinal j step hstep) :=
  (ScheduledCoverage.finalEmbedding_injective (succ j)).comp
    (castHom_injective (successor_object j step hstep).symm)

theorem completionToFinal_base (j : Index)
    (step : TransfiniteSystems.NextStep (ScheduledIteration.system.obj j))
    (hstep : ScheduledIteration.next j (stagePrefix j) = step) :
    (completionToFinal j step hstep).comp (CompletionEmbedding.baseHom step.forcing) =
      ScheduledCoverage.finalEmbedding j := by
  have hcancel : (castHom (successor_object j step hstep).symm).comp
      (castHom (successor_object j step hstep)) =
      CompleteLatticeHom.id (ScheduledIteration.system.obj (succ j)) := by
    rw [castHom_comp]
    rfl
  rw [← successor_embedding j step hstep]
  ext b
  change ScheduledCoverage.finalEmbedding (succ j)
    (((castHom (successor_object j step hstep).symm).comp
      (castHom (successor_object j step hstep)))
        (ScheduledIteration.system.map j (succ j) (le_succ j) b)) = _
  rw [hcancel]
  exact DFunLike.congr_fun (ScheduledCoverage.finalEmbedding_comp (le_succ j)) b

end Erdos597Object.SuccessorBridge
