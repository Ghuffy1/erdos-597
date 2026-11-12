import Erdos597Object.IterationPrefixes

set_option backward.isDefEq.respectTransparency false

/-! Every earlier fixed-label requirement whose final image is CCC is eventually selected. -/

namespace Erdos597Object.ScheduledCoverage

open Set CanonicalIteration IterationSystems SystemGluing
open ScheduledIteration IterationPrefixes IterationNameTransport AlgebraTransport

theorem selectedRequirement_eq (i j code : Index) (hij : i ≤ j)
    (hschedule : BookkeepingSchedule.schedule j = (i, code)) :
    selectedRequirement j (stagePrefix j) =
      mapRequirement (ScheduledIteration.system.map i j hij)
        (RequirementCodes.requirementAt (ScheduledIteration.system.obj i).card_le
          labels_card.le labels_card.le code) := by
  classical
  let fromPair (indices : Index × Index) :=
    if h : indices.1 ≤ j then
      let earlier : Iic j := ⟨indices.1, Set.mem_Iic.mpr h⟩
      let transition := (stagePrefix j).system.map earlier (endpoint j) h
      mapRequirement transition
        (RequirementCodes.requirementAt ((stagePrefix j).system.obj earlier).card_le
          labels_card.le labels_card.le indices.2)
    else none
  change fromPair (BookkeepingSchedule.schedule j) = _
  rw [hschedule]
  dsimp only [fromPair, Prod.fst, Prod.snd]
  rw [dite_eq_left hij]
  change mapRequirement
    ((stagePrefix j).system.map ⟨i, Set.mem_Iic.mpr hij⟩ (endpoint j) hij)
    (RequirementCodes.requirementAt
      ((stagePrefix j).system.obj ⟨i, Set.mem_Iic.mpr hij⟩).card_le
      labels_card.le labels_card.le code) = _
  rw [global_map hij, ← mapRequirement_comp, requirementAt_cast]

theorem eventually_enumerated (i bound : Index)
    (P : BooleanIteration.BooleanPoset (ScheduledIteration.system.obj i) Labels)
    (dense : Labels → Labels → ScheduledIteration.system.obj i) :
    ∃ (j : Index) (hij : i ≤ j), bound < j ∧
      selectedRequirement j (stagePrefix j) =
        some (mapPoset (ScheduledIteration.system.map i j hij) P,
          fun d a => ScheduledIteration.system.map i j hij (dense d a)) := by
  obtain ⟨code, hcode⟩ := RequirementCodes.every_requirement_has_code
    (ScheduledIteration.system.obj i).card_le labels_card.le labels_card.le P dense
  obtain ⟨j, hij, hbound, hschedule⟩ := BookkeepingSchedule.scheduled_after_stage i code bound
  refine ⟨j, hij.le, hbound, ?_⟩
  rw [selectedRequirement_eq i j code hij.le hschedule, hcode]
  rfl

noncomputable def finalEmbedding (i : Index) :
    CompleteLatticeHom (ScheduledIteration.system.obj i) ScheduledIteration.finalAlgebra :=
  CanonicalIteration.finalEmbedding ScheduledIteration.next i

theorem finalEmbedding_injective (i : Index) : Function.Injective (finalEmbedding i) :=
  CanonicalIteration.finalEmbedding_injective ScheduledIteration.next i

theorem finalEmbedding_comp {i j : Index} (hij : i ≤ j) :
    (finalEmbedding j).comp (ScheduledIteration.system.map i j hij) = finalEmbedding i := by
  ext b
  exact (LimitEmbeddings.stageHom_coherent ScheduledIteration.system.map
    ScheduledIteration.system.injective hij b).symm

theorem poset_final_image {i j : Index} (hij : i ≤ j)
    (P : BooleanIteration.BooleanPoset (ScheduledIteration.system.obj i) Labels) :
    mapPoset (finalEmbedding j) (mapPoset (ScheduledIteration.system.map i j hij) P) =
      mapPoset (finalEmbedding i) P := by
  rw [mapPoset_comp, finalEmbedding_comp hij]

set_option maxHeartbeats 800000 in
theorem eventually_selected (i bound : Index)
    (P : BooleanIteration.BooleanPoset (ScheduledIteration.system.obj i) Labels)
    (dense : Labels → Labels → ScheduledIteration.system.obj i)
    (hccc : MartinTransport.CountableChainCondition
      (BooleanIteration.Condition (mapPoset (finalEmbedding i) P)))
    (hcover : (⨆ a, (mapPoset (finalEmbedding i) P).member a) = ⊤) :
    ∃ (j : Index) (hij : i ≤ j)
      (hccc' : MartinTransport.CountableChainCondition
        (BooleanIteration.Condition (mapPoset (ScheduledIteration.system.map i j hij) P)))
      (hcover' : (⨆ a, (mapPoset (ScheduledIteration.system.map i j hij) P).member a) = ⊤),
      bound < j ∧ ScheduledIteration.next j (stagePrefix j) =
        ({ Labels := Labels
           forcing := mapPoset (ScheduledIteration.system.map i j hij) P
           ccc := hccc'
           card_le := labels_card.le
           cover := hcover' } : TransfiniteSystems.NextStep (ScheduledIteration.system.obj j)) := by
  obtain ⟨j, hij, hbound, hselected⟩ := eventually_enumerated i bound P dense
  let Q := mapPoset (ScheduledIteration.system.map i j hij) P
  have hQ : MartinTransport.CountableChainCondition (BooleanIteration.Condition Q) := by
    apply PosetStageCapture.ccc_reflected (finalEmbedding j) (finalEmbedding_injective j) Q
    exact Eq.mpr (congrArg (fun R : BooleanIteration.BooleanPoset ScheduledIteration.finalAlgebra Labels =>
      MartinTransport.CountableChainCondition
      (BooleanIteration.Condition R)) (poset_final_image hij P)) hccc
  have hQcover : (⨆ a, Q.member a) = ⊤ := by
    apply finalEmbedding_injective j
    rw [map_iSup, map_top]
    change (⨆ a, (mapPoset (finalEmbedding j)
      (mapPoset (ScheduledIteration.system.map i j hij) P)).member a) = ⊤
    exact (congrArg (fun R : BooleanIteration.BooleanPoset ScheduledIteration.finalAlgebra Labels =>
      ⨆ a : Labels, R.member a) (poset_final_image hij P)).trans hcover
  refine ⟨j, hij, hQ, hQcover, hbound, ?_⟩
  rw [ScheduledIteration.next, hselected]
  exact guardedStep_good _ Q _ hQ hQcover

end Erdos597Object.ScheduledCoverage
