import Erdos597Object.ContextCompletion

set_option backward.isDefEq.respectTransparency false

/-! Relabel Boolean posets by an equivalence, preserving their forcing properties. -/

namespace Erdos597Object.PosetRelabeling

open BooleanIteration

variable {B I J : Type} [CompleteBooleanAlgebra B]

def relabel (e : J ≃ I) (P : BooleanPoset B I) : BooleanPoset B J where
  member j := P.member (e j)
  leValue j k := P.leValue (e j) (e k)
  le_members j k := P.le_members (e j) (e k)
  reflexive j := P.reflexive (e j)
  transitive j k l := P.transitive (e j) (e k) (e l)
  antisymmetric j k hjk := P.antisymmetric (e j) (e k) (fun h => hjk (e.injective h))

theorem relabel_compatible (e : J ≃ I) (P : BooleanPoset B I) (j k : J) :
    BooleanIteration.compatibleValue (relabel e P) j k =
      BooleanIteration.compatibleValue P (e j) (e k) :=
  e.surjective.iSup_comp (fun i => P.leValue i (e j) ⊓ P.leValue i (e k))

theorem relabel_members (e : J ≃ I) (P : BooleanPoset B I) :
    (⨆ j, (relabel e P).member j) = ⨆ i, P.member i :=
  e.surjective.iSup_comp P.member

theorem relabel_booleanCCC (e : J ≃ I) (P : BooleanPoset B I)
    (hP : BooleanCountableChainCondition P) :
    BooleanCountableChainCondition (relabel e P) := by
  intro K label values hvalues hincompatible
  apply hP K (fun k => e (label k)) values hvalues
  intro j k hjk
  rw [← relabel_compatible e P]
  exact hincompatible j k hjk

theorem relabel_ccc (hB : Flypitch.BA_CCC B) (e : J ≃ I) (P : BooleanPoset B I)
    (hP : BooleanCountableChainCondition P) :
    MartinTransport.CountableChainCondition (Condition (relabel e P)) :=
  two_step_ccc hB _ (relabel_booleanCCC e P hP)

noncomputable def optionEquiv (I : Type) [Infinite I] : Option I ≃ I :=
  Classical.choice (Cardinal.eq.mp (by
    rw [Cardinal.mk_option, Cardinal.mk_add_one_eq]))

noncomputable def completeContext [Infinite I] (context : B) (P : BooleanPoset B I) :
    BooleanPoset B I :=
  relabel (optionEquiv I).symm (ContextCompletion.withOutside context P)

theorem completeContext_cover [Infinite I] (context : B) (P : BooleanPoset B I)
    (hcover : (⨆ i, P.member i) = context) :
    (⨆ i, (completeContext context P).member i) = ⊤ := by
  rw [completeContext, relabel_members, ContextCompletion.withOutside_cover context P hcover]

theorem completeContext_booleanCCC [Infinite I] (context : B) (P : BooleanPoset B I)
    (hP : BooleanCountableChainCondition P) :
    BooleanCountableChainCondition (completeContext context P) :=
  relabel_booleanCCC _ _ (ContextCompletion.withOutside_booleanCCC context P hP)

theorem completeContext_ccc [Infinite I] (hB : Flypitch.BA_CCC B)
    (context : B) (P : BooleanPoset B I) (hP : BooleanCountableChainCondition P) :
    MartinTransport.CountableChainCondition (Condition (completeContext context P)) :=
  two_step_ccc hB _ (completeContext_booleanCCC context P hP)

end Erdos597Object.PosetRelabeling
