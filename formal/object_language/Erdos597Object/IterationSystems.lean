import Erdos597Object.SystemReindexing

set_option backward.isDefEq.respectTransparency false

/-! Bundled small CCC algebras and the successor and limit operations on their systems. -/

namespace Erdos597Object.IterationSystems

open Cardinal Set
open scoped Cardinal
open IterationCardinals SystemExtension

structure Algebra where
  Carrier : Type
  algebra : CompleteBooleanAlgebra Carrier
  nontrivial : Nontrivial Carrier
  ccc : @Flypitch.BA_CCC Carrier algebra
  card_le : #Carrier ≤ iterationSize

instance : CoeSort Algebra Type := ⟨Algebra.Carrier⟩

instance (A : Algebra) : CompleteBooleanAlgebra A := A.algebra

instance (A : Algebra) : Nontrivial A := A.nontrivial

structure System (I : Type) [Preorder I] where
  obj : I → Algebra
  map : ∀ i j, i ≤ j → CompleteLatticeHom (obj i) (obj j)
  coherent : DirectedSystem (fun i => (obj i : Type)) (map · · ·)
  injective : ∀ i j h, Function.Injective (map i j h)

instance {I : Type} [Preorder I] (S : System I) :
    DirectedSystem (fun i => (S.obj i : Type)) (S.map · · ·) := S.coherent

namespace System

variable {I J : Type} [Preorder I] [Preorder J]

theorem ext {S T : System I} (hobj : S.obj = T.obj)
    (hmap : ∀ i j h, HEq (S.map i j h) (T.map i j h)) : S = T := by
  cases S with
  | mk obj map coherent injective =>
    cases T with
    | mk otherObj otherMap otherCoherent otherInjective =>
      dsimp at hobj hmap
      subst otherObj
      have hm : map = otherMap := by
        funext i j h
        exact eq_of_heq (hmap i j h)
      subst otherMap
      rfl

def reindex (S : System I) (r : J → I) (hr : Monotone r) : System J where
  obj j := S.obj (r j)
  map := SystemReindexing.pullbackMap S.map r hr
  coherent := SystemReindexing.pullback_directedSystem S.map r hr
  injective := SystemReindexing.pullback_injective S.map r hr S.injective

theorem reindex_id (S : System I) : S.reindex id monotone_id = S := by
  apply ext rfl
  intro i j h
  rfl

theorem reindex_comp {K : Type} [Preorder K] (S : System I)
    (r : J → I) (hr : Monotone r) (s : K → J) (hs : Monotone s) :
    (S.reindex r hr).reindex s hs = S.reindex (r ∘ s) (hr.comp hs) := rfl

theorem reindex_obj (S : System I) (r : J → I) (hr : Monotone r) (j : J) :
    (S.reindex r hr).obj j = S.obj (r j) := rfl

theorem reindex_map (S : System I) (r : J → I) (hr : Monotone r)
    (i j : J) (hij : i ≤ j) :
    (S.reindex r hr).map i j hij = S.map (r i) (r j) (hr hij) := rfl

def extendedObject (S : System I) (C : Algebra) (i : WithTop I) : Algebra where
  Carrier := extendedFamily (fun j => (S.obj j : Type)) C i
  algebra := extendedAlgebra i
  nontrivial := by
    cases i with
    | top => exact C.nontrivial
    | coe i => exact (S.obj i).nontrivial
  ccc := extendedFamily_ccc (fun j => (S.obj j).ccc) C.ccc i
  card_le := extendedFamily_card_le (fun j => (S.obj j).card_le) C.card_le i

def extend (S : System I) (C : Algebra)
    (legs : ∀ i, CompleteLatticeHom (S.obj i) C)
    (hlegs : ∀ i j (h : i ≤ j) (b : S.obj i), legs j (S.map i j h b) = legs i b)
    (hinj : ∀ i, Function.Injective (legs i)) : System (WithTop I) where
  obj := S.extendedObject C
  map := extendedMap S.map legs
  coherent := extendedDirectedSystem S.map legs hlegs
  injective := extendedMap_injective S.map legs S.injective hinj

theorem extend_old (S : System I) (C : Algebra)
    (legs : ∀ i, CompleteLatticeHom (S.obj i) C)
    (hlegs : ∀ i j (h : i ≤ j) (b : S.obj i), legs j (S.map i j h b) = legs i b)
    (hinj : ∀ i, Function.Injective (legs i)) (i : I) :
    (S.extend C legs hlegs hinj).obj i = S.obj i := rfl

theorem extend_top (S : System I) (C : Algebra)
    (legs : ∀ i, CompleteLatticeHom (S.obj i) C)
    (hlegs : ∀ i j (h : i ≤ j) (b : S.obj i), legs j (S.map i j h b) = legs i b)
    (hinj : ∀ i, Function.Injective (legs i)) :
    (S.extend C legs hlegs hinj).obj ⊤ = C := by
  cases C
  rfl

theorem extend_continuous (S : System I) (C : Algebra)
    (legs : ∀ i, CompleteLatticeHom (S.obj i) C)
    (hlegs : ∀ i j (h : i ≤ j) (b : S.obj i), legs j (S.map i j h b) = legs i b)
    (hinj : ∀ i, Function.Injective (legs i))
    (hcontinuous : ExtensionContinuity.Continuous S.map)
    (htop : Order.IsSuccLimit (⊤ : WithTop I) →
      ∀ c : C, c ≠ ⊥ → ∃ (i : I) (b : S.obj i), b ≠ ⊥ ∧ legs i b ≤ c) :
    ExtensionContinuity.Continuous (S.extend C legs hlegs hinj).map :=
  ExtensionContinuity.extended_continuous S.map legs hcontinuous htop

end System

namespace System

variable {I : Type} [LinearOrder I] [WellFoundedLT I] [Nonempty I]

noncomputable def limitAlgebra (S : System I)
    (hcontinuous : ExtensionContinuity.Continuous S.map)
    (hI : #I ≤ iterationSize) : Algebra where
  Carrier := PosetCompletion.Completion (BooleanDirectLimit.Condition S.map)
  algebra := inferInstance
  nontrivial := by
    classical
    let i : I := Classical.choice inferInstance
    letI : Nonempty (BooleanDirectLimit.Condition S.map) :=
      ⟨BooleanDirectLimit.ofStage S.map i ⊤ top_ne_bot⟩
    infer_instance
  ccc := ExtensionContinuity.limit_algebra_ccc S.map S.injective
    (fun i => (S.obj i).ccc) hcontinuous
  card_le := CofinalSequences.completion_card_le_of_continuity S.map S.injective
    (fun i => (S.obj i).ccc) hI (fun i => (S.obj i).card_le) hcontinuous

noncomputable def limit (S : System I)
    (hcontinuous : ExtensionContinuity.Continuous S.map)
    (hI : #I ≤ iterationSize) : System (WithTop I) :=
  S.extend (S.limitAlgebra hcontinuous hI) (LimitEmbeddings.stageHom S.map S.injective)
    (fun _ _ h b => (LimitEmbeddings.stageHom_coherent S.map S.injective h b).symm)
    (LimitEmbeddings.stageHom_injective S.map S.injective)

theorem limit_continuous (S : System I)
    (hcontinuous : ExtensionContinuity.Continuous S.map)
    (hI : #I ≤ iterationSize) :
    ExtensionContinuity.Continuous (S.limit hcontinuous hI).map :=
  ExtensionContinuity.limit_continuous S.map S.injective hcontinuous

noncomputable def closePrefix {K : Type} [LinearOrder K] [WellFoundedLT K]
    (j : K) (hj : Order.IsSuccLimit j) (S : System (Iio j))
    (hcontinuous : ExtensionContinuity.Continuous S.map)
    (hI : #(Iio j) ≤ iterationSize) : System (Iic j) := by
  letI : Nonempty (Iio j) := hj.nonempty_Iio.to_subtype
  exact (S.limit hcontinuous hI).reindex (SystemReindexing.prefixIso j).symm
    (SystemReindexing.prefixIso j).symm.monotone

theorem closePrefix_continuous {K : Type} [LinearOrder K] [WellFoundedLT K]
    (j : K) (hj : Order.IsSuccLimit j) (S : System (Iio j))
    (hcontinuous : ExtensionContinuity.Continuous S.map)
    (hI : #(Iio j) ≤ iterationSize) :
    ExtensionContinuity.Continuous (closePrefix j hj S hcontinuous hI).map := by
  letI : Nonempty (Iio j) := hj.nonempty_Iio.to_subtype
  exact SystemReindexing.pullback_continuous (S.limit hcontinuous hI).map
    (SystemReindexing.prefixIso j).symm (S.limit_continuous hcontinuous hI)

end System

namespace System

variable {I L : Type} [Preorder I]

noncomputable def successorAlgebra (S : System I) (last : I)
    (Q : BooleanIteration.BooleanPoset (S.obj last) L)
    (hccc : MartinTransport.CountableChainCondition (BooleanIteration.Condition Q))
    (hL : #L ≤ ℵ₁) (hcover : (⨆ i, Q.member i) = ⊤) : Algebra where
  Carrier := PosetCompletion.Completion (BooleanIteration.Condition Q)
  algebra := inferInstance
  nontrivial := by
    obtain ⟨p, _⟩ := CompletionEmbedding.exists_condition_below Q hcover ⊤ top_ne_bot
    letI : Nonempty (BooleanIteration.Condition Q) := ⟨p⟩
    infer_instance
  ccc := PosetCompletion.completion_ccc hccc
  card_le := PosetCompletion.two_step_completion_card_le Q hccc (S.obj last).card_le hL

noncomputable def successor (S : System I) (last : I) (hlast : ∀ i, i ≤ last)
    (Q : BooleanIteration.BooleanPoset (S.obj last) L)
    (hccc : MartinTransport.CountableChainCondition (BooleanIteration.Condition Q))
    (hL : #L ≤ ℵ₁) (hcover : (⨆ i, Q.member i) = ⊤) : System (WithTop I) :=
  S.extend (S.successorAlgebra last Q hccc hL hcover) (successorLeg S.map last hlast Q)
    (successorLeg_coherent S.map last hlast Q)
    (successorLeg_injective S.map last hlast Q S.injective hcover)

theorem successor_continuous (S : System I) (last : I) (hlast : ∀ i, i ≤ last)
    (Q : BooleanIteration.BooleanPoset (S.obj last) L)
    (hccc : MartinTransport.CountableChainCondition (BooleanIteration.Condition Q))
    (hL : #L ≤ ℵ₁) (hcover : (⨆ i, Q.member i) = ⊤)
    (hcontinuous : ExtensionContinuity.Continuous S.map) :
    ExtensionContinuity.Continuous (S.successor last hlast Q hccc hL hcover).map :=
  ExtensionContinuity.successor_continuous S.map last hlast Q hcontinuous

end System

end Erdos597Object.IterationSystems
