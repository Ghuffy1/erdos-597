import Erdos597Object.AlgebraTransport

set_option backward.isDefEq.respectTransparency false

/-! Exact prefix and transition identities for the scheduled global iteration. -/

namespace Erdos597Object.IterationPrefixes

open Set CategoryTheory Opposite
open CanonicalIteration IterationSystems SystemRestrictions SystemGluing

noncomputable def stagePrefix (j : Index) : Prefix j :=
  (TransfiniteSystems.prefixes index_card.le ScheduledIteration.next
    TransfiniteSystems.initialPrefix).val (op j)

theorem prefix_compatible {i j : Index} (hij : i ≤ j) :
    (stagePrefix j).restrict hij = stagePrefix i :=
  TransfiniteSystems.prefixes_compatible index_card.le ScheduledIteration.next
    TransfiniteSystems.initialPrefix i j hij

theorem global_object (j : Index) :
    ScheduledIteration.system.obj j = (stagePrefix j).system.obj (ScheduledIteration.endpoint j) := rfl

theorem prefix_object {i j : Index} (hij : i ≤ j) :
    (stagePrefix j).system.obj ⟨i, Set.mem_Iic.mpr hij⟩ = ScheduledIteration.system.obj i :=
  congrArg (fun S : Prefix i => S.system.obj (ScheduledIteration.endpoint i))
    (prefix_compatible hij)

theorem global_restrict (j : Index) :
    ScheduledIteration.system.reindex (fun i : Iic j => i.val) (fun _ _ h => h) =
      (stagePrefix j).system :=
  TransfiniteSystems.system_restrict index_card.le ScheduledIteration.next
    TransfiniteSystems.initialPrefix j

theorem global_map {i j : Index} (hij : i ≤ j) :
    ScheduledIteration.system.map i j hij =
      ((stagePrefix j).system.map ⟨i, Set.mem_Iic.mpr hij⟩ (ScheduledIteration.endpoint j) hij).comp
        (castHom (prefix_object hij).symm) := by
  rfl

theorem prefix_successor (j : Index) : stagePrefix (Order.succ j) =
    TransfiniteSystems.chosenSuccessor ScheduledIteration.next j (stagePrefix j) :=
  TransfiniteSystems.prefixes_successor index_card.le ScheduledIteration.next
    TransfiniteSystems.initialPrefix j

end Erdos597Object.IterationPrefixes
