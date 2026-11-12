import Erdos597Object.PosetStageCapture

set_option backward.isDefEq.respectTransparency false

/-! The iteration on the initial ordinal of two to the aleph-one, and its final completion. -/

namespace Erdos597Object.CanonicalIteration

open Cardinal Set
open scoped Cardinal
open IterationCardinals IterationSystems SystemRestrictions TransfiniteSystems

abbrev Index : Type := iterationSize.ord.ToType

theorem index_card : #Index = iterationSize := by
  simp only [Index, Cardinal.mk_toType, Cardinal.card_ord]

theorem index_cofinality : ℵ₁ < Order.cof Index := by
  simpa only [Index, Ordinal.cof_toType] using aleph_one_lt_iterationSize_cofinality

instance indexNonempty : Nonempty Index :=
  Cardinal.mk_ne_zero_iff.mp (index_card.trans_ne iterationSize_ne_zero)

noncomputable instance indexOrderBot : OrderBot Index := WellFoundedLT.toOrderBot Index

instance indexNoMaxOrder : NoMaxOrder Index :=
  (noTopOrder_iff_noMaxOrder Index).mp (Order.one_lt_cof_iff.mp
    (Cardinal.one_lt_aleph0.trans (Cardinal.aleph0_lt_aleph_one.trans index_cofinality)))

variable (next : ∀ (j : Index) (S : Prefix j),
  NextStep (S.system.obj ⟨j, Set.mem_Iic.mpr (le_refl j)⟩))

noncomputable def iteration : System Index :=
  TransfiniteSystems.system index_card.le next initialPrefix

theorem iteration_continuous : ExtensionContinuity.Continuous (iteration next).map :=
  TransfiniteSystems.system_continuous index_card.le next initialPrefix

noncomputable def finalAlgebra : Algebra :=
  (iteration next).limitAlgebra (iteration_continuous next) index_card.le

noncomputable def finalEmbedding (j : Index) :
    CompleteLatticeHom ((iteration next).obj j) (finalAlgebra next) :=
  LimitEmbeddings.stageHom (iteration next).map (iteration next).injective j

theorem finalEmbedding_injective (j : Index) : Function.Injective (finalEmbedding next j) :=
  LimitEmbeddings.stageHom_injective (iteration next).map (iteration next).injective j

theorem final_family_captured {A : Type} (hA : #A ≤ ℵ₁) (values : A → finalAlgebra next) :
    ∃ (j : Index) (earlier : A → (iteration next).obj j),
      ∀ a, finalEmbedding next j (earlier a) = values a :=
  StageCapture.completion_small_family_at_stage (iteration next).map (iteration next).injective
    (fun j => ((iteration next).obj j).ccc) index_cofinality hA values

theorem final_poset_family_captured {I D : Type} (hI : #I ≤ ℵ₁) (hD : #D ≤ ℵ₁)
    (P : BooleanIteration.BooleanPoset (finalAlgebra next) I)
    (dense : D → I → finalAlgebra next) :
    ∃ (j : Index) (earlier : BooleanIteration.BooleanPoset ((iteration next).obj j) I)
      (dense' : D → I → (iteration next).obj j),
      IterationNameTransport.mapPoset (finalEmbedding next j) earlier = P ∧
      ∀ d i, finalEmbedding next j (dense' d i) = dense d i :=
  PosetStageCapture.poset_and_family_at_stage (iteration next).map (iteration next).injective
    (fun j => ((iteration next).obj j).ccc) index_cofinality hI hD P dense

theorem final_requirement_captured {I D : Type} (hI : #I ≤ ℵ₁) (hD : #D ≤ ℵ₁)
    (P : BooleanIteration.BooleanPoset (finalAlgebra next) I)
    (hP : MartinTransport.CountableChainCondition (BooleanIteration.Condition P))
    (hcover : (⨆ i, P.member i) = ⊤) (dense : D → I → finalAlgebra next) :
    ∃ (j : Index) (earlier : BooleanIteration.BooleanPoset ((iteration next).obj j) I)
      (dense' : D → I → (iteration next).obj j),
      IterationNameTransport.mapPoset (finalEmbedding next j) earlier = P ∧
      MartinTransport.CountableChainCondition (BooleanIteration.Condition earlier) ∧
      (⨆ i, earlier.member i) = ⊤ ∧
      ∀ d i, finalEmbedding next j (dense' d i) = dense d i :=
  PosetStageCapture.ccc_poset_and_family_at_stage (iteration next).map (iteration next).injective
    (fun j => ((iteration next).obj j).ccc) index_cofinality hI hD P hP hcover dense

end Erdos597Object.CanonicalIteration
