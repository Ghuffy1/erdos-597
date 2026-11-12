import Erdos597Object.PrefixExtensions

set_option backward.isDefEq.respectTransparency false

/-! Transfinite construction from a chosen successor forcing at each prefix. -/

namespace Erdos597Object.TransfiniteSystems

open Set Order Cardinal CategoryTheory Opposite
open scoped Cardinal
open IterationSystems SystemRestrictions PrefixExtensions

structure NextStep (A : Algebra) where
  Labels : Type
  forcing : BooleanIteration.BooleanPoset A Labels
  ccc : MartinTransport.CountableChainCondition (BooleanIteration.Condition forcing)
  card_le : #Labels ≤ ℵ₁
  cover : (⨆ a, forcing.member a) = ⊤

variable {J : Type} [LinearOrder J] [SuccOrder J] [NoMaxOrder J]

noncomputable def chosenSuccessor
    (next : ∀ (j : J) (S : Prefix j), NextStep (S.system.obj ⟨j, le_rfl⟩))
    (j : J) (S : Prefix j) : Prefix (succ j) :=
  let step := next j S
  successorPrefix j S step.forcing step.ccc step.card_le step.cover

theorem chosenSuccessor_restrict
    (next : ∀ (j : J) (S : Prefix j), NextStep (S.system.obj ⟨j, le_rfl⟩))
    (j : J) (S : Prefix j) : (chosenSuccessor next j S).restrict (le_succ j) = S :=
  successorPrefix_restrict j S (next j S).forcing (next j S).ccc
    (next j S).card_le (next j S).cover

def sectionFamily (j : J)
    (x : ((OrderHom.Subtype.val (· ∈ Iio j)).monotone.functor.op ⋙ prefixFunctor J).sections)
    (i : Iio j) : Prefix i.val := x.val (op i)

theorem sectionFamily_compatible (j : J)
    (x : ((OrderHom.Subtype.val (· ∈ Iio j)).monotone.functor.op ⋙ prefixFunctor J).sections)
    (i k : Iio j) (hik : i ≤ k) :
    (sectionFamily j x k).restrict hik = sectionFamily j x i :=
  x.property (homOfLE hik).op

variable [WellFoundedLT J]

noncomputable def limitFromSection (hsize : #J ≤ IterationCardinals.iterationSize)
    (j : J) (hj : IsSuccLimit j)
    (x : ((OrderHom.Subtype.val (· ∈ Iio j)).monotone.functor.op ⋙ prefixFunctor J).sections) :
    Prefix j :=
  limitPrefix j hj (sectionFamily j x) (sectionFamily_compatible j x)
    ((Cardinal.mk_subtype_le _).trans hsize)

theorem limitFromSection_restrict (hsize : #J ≤ IterationCardinals.iterationSize)
    (j : J) (hj : IsSuccLimit j)
    (x : ((OrderHom.Subtype.val (· ∈ Iio j)).monotone.functor.op ⋙ prefixFunctor J).sections)
    (i : J) (hij : i < j) :
    (limitFromSection hsize j hj x).restrict hij.le = x.val (op ⟨i, hij⟩) :=
  limitPrefix_restrict j hj _ _ _ ⟨i, hij⟩

noncomputable def inductionData (hsize : #J ≤ IterationCardinals.iterationSize)
    (next : ∀ (j : J) (S : Prefix j), NextStep (S.system.obj ⟨j, le_rfl⟩)) :
    (prefixFunctor J).WellOrderInductionData where
  succ j _ S := chosenSuccessor next j S
  map_succ j _ S := chosenSuccessor_restrict next j S
  lift j hj x := limitFromSection hsize j hj x
  map_lift j hj x i hij := limitFromSection_restrict hsize j hj x i hij

variable [OrderBot J]

def initialAlgebra : Algebra where
  Carrier := Set PUnit
  algebra := inferInstance
  nontrivial := inferInstance
  ccc := by
    intro A _ _
    exact Set.to_countable A
  card_le := Cardinal.mk_le_aleph0.trans IterationCardinals.iterationSize_infinite

def constantSystem {I : Type} [Preorder I] (A : Algebra) : System I where
  obj _ := A
  map _ _ _ := CompleteLatticeHom.id A
  coherent := { map_self := fun _ _ => rfl, map_map := fun _ _ _ _ _ _ => rfl }
  injective := fun _ _ _ => Function.injective_id

theorem constantSystem_continuous {I : Type} [LinearOrder I] (A : Algebra) :
    ExtensionContinuity.Continuous (constantSystem (I := I) A).map := by
  intro i hi b hb
  obtain ⟨j, hji⟩ := not_isMin_iff.mp hi.not_isMin
  exact ⟨j, hji, b, hb, le_rfl⟩

def initialPrefix : Prefix (⊥ : J) where
  system := constantSystem initialAlgebra
  continuous := constantSystem_continuous initialAlgebra

noncomputable def prefixes (hsize : #J ≤ IterationCardinals.iterationSize)
    (next : ∀ (j : J) (S : Prefix j), NextStep (S.system.obj ⟨j, le_rfl⟩))
    (initial : Prefix (⊥ : J)) : (prefixFunctor J).sections :=
  (inductionData hsize next).sectionsMk initial

theorem prefixes_initial (hsize : #J ≤ IterationCardinals.iterationSize)
    (next : ∀ (j : J) (S : Prefix j), NextStep (S.system.obj ⟨j, le_rfl⟩))
    (initial : Prefix (⊥ : J)) :
    (prefixes hsize next initial).val (op (⊥ : J)) = initial :=
  (inductionData hsize next).sectionsMk_val_op_bot initial

theorem prefixes_compatible (hsize : #J ≤ IterationCardinals.iterationSize)
    (next : ∀ (j : J) (S : Prefix j), NextStep (S.system.obj ⟨j, le_rfl⟩))
    (initial : Prefix (⊥ : J)) (i j : J) (hij : i ≤ j) :
    ((prefixes hsize next initial).val (op j)).restrict hij =
      (prefixes hsize next initial).val (op i) :=
  (prefixes hsize next initial).property (homOfLE hij).op

theorem prefixes_successor (hsize : #J ≤ IterationCardinals.iterationSize)
    (next : ∀ (j : J) (S : Prefix j), NextStep (S.system.obj ⟨j, le_rfl⟩))
    (initial : Prefix (⊥ : J)) (i : J) :
    (prefixes hsize next initial).val (op (succ i)) =
      chosenSuccessor next i ((prefixes hsize next initial).val (op i)) := by
  let d := inductionData hsize next
  change (default : d.Extension initial (succ i)).val =
    chosenSuccessor next i (default : d.Extension initial i).val
  have h := (default : d.Extension initial (succ i)).map_succ i
    (lt_succ_of_not_isMax (not_isMax i))
  change (default : d.Extension initial (succ i)).val.restrict le_rfl =
    chosenSuccessor next i ((default : d.Extension initial (succ i)).val.restrict (le_succ i)) at h
  rw [Prefix.restrict_refl] at h
  have hc : (default : d.Extension initial (succ i)).val.restrict (le_succ i) =
      (default : d.Extension initial i).val :=
    (default : d.Extension initial (succ i)).compatibility
      (default : d.Extension initial i) (le_succ i)
  simpa only [hc] using h

def univIso : J ≃o (univ : Set J) where
  toFun j := ⟨j, mem_univ j⟩
  invFun j := j.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

noncomputable def system (hsize : #J ≤ IterationCardinals.iterationSize)
    (next : ∀ (j : J) (S : Prefix j), NextStep (S.system.obj ⟨j, le_rfl⟩))
    (initial : Prefix (⊥ : J)) : System J :=
  (SystemGluing.glue
    (fun i : (univ : Set J) => ((prefixes hsize next initial).val (op i.val)).system)
    (fun i j hij => congrArg Prefix.system (prefixes_compatible hsize next initial i.val j.val hij))).reindex
      (univIso (J := J)) (univIso (J := J)).monotone

theorem system_continuous (hsize : #J ≤ IterationCardinals.iterationSize)
    (next : ∀ (j : J) (S : Prefix j), NextStep (S.system.obj ⟨j, le_rfl⟩))
    (initial : Prefix (⊥ : J)) :
    ExtensionContinuity.Continuous (system hsize next initial).map :=
  SystemReindexing.pullback_continuous _ (univIso (J := J))
    (SystemGluing.glue_continuous
      (fun i : (univ : Set J) => ((prefixes hsize next initial).val (op i.val)).system)
      (fun i j hij => congrArg Prefix.system (prefixes_compatible hsize next initial i.val j.val hij))
      isLowerSet_univ (fun i =>
      ((prefixes hsize next initial).val (op i.val)).continuous))

theorem system_restrict (hsize : #J ≤ IterationCardinals.iterationSize)
    (next : ∀ (j : J) (S : Prefix j), NextStep (S.system.obj ⟨j, le_rfl⟩))
    (initial : Prefix (⊥ : J)) (j : J) :
    (system hsize next initial).reindex (fun a : Iic j => a.val) (fun _ _ h => h) =
      ((prefixes hsize next initial).val (op j)).system :=
  SystemGluing.glue_restrict
    (fun i : (univ : Set J) => ((prefixes hsize next initial).val (op i.val)).system)
    (fun i k hik => congrArg Prefix.system (prefixes_compatible hsize next initial i.val k.val hik))
    isLowerSet_univ ⟨j, mem_univ j⟩

end Erdos597Object.TransfiniteSystems
