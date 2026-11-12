import Erdos597Object.BooleanCCCSemantics

set_option backward.isDefEq.respectTransparency false

/-!
Set names for a Boolean-valued poset and the first-order CCC bridge.
Distinct labels are represented by check-names of distinct ordinals.
-/

namespace Erdos597Object.BooleanPosetCoding

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open scoped Flypitch.bSet
open Erdos597Object.BooleanSets Erdos597Object.BooleanAntichains
open Erdos597Object.BooleanCCCSemantics Erdos597Object.BooleanIteration

variable {B I : Type} [CompleteBooleanAlgebra B]

noncomputable def checkLabel (i : I) : bSet B :=
  bSet.check (Ordinal.toPSet (Ordinal.typein WellOrderingRel i))

theorem checkLabel_discrete {i j : I} (hij : i ≠ j) :
    (checkLabel (B := B) i =ᴮ checkLabel j) = ⊥ := by
  apply bSet.check_bv_eq_bot_of_not_equiv
  intro h
  exact hij (Ordinal.typein_injective WellOrderingRel (Flypitch.ordinal.mk_inj h))

theorem member_weightedSet_discrete (element : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (element i =ᴮ element j) = ⊥)
    (weight : I → B) (i : I) :
    (element i ∈ᴮ weightedSet element weight) = weight i := by
  classical
  rw [member_weightedSet]
  apply le_antisymm
  · apply iSup_le
    intro j
    by_cases hij : i = j
    · subst j
      simp
    · rw [hdiscrete i j hij, inf_bot_eq]
      exact bot_le
  · exact le_iSup_of_le i (by simp)

def pairLabels (element : I → bSet B) (ij : I × I) : bSet B :=
  bSet.pair (element ij.1) (element ij.2)

theorem pairLabels_discrete (element : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (element i =ᴮ element j) = ⊥) :
    ∀ ij kl, ij ≠ kl → (pairLabels element ij =ᴮ pairLabels element kl) = ⊥ := by
  classical
  intro ij kl hne
  by_cases hleft : ij.1 = kl.1
  · have hright : ij.2 ≠ kl.2 := fun h => hne (Prod.ext hleft h)
    exact bot_unique (bSet.eq_of_eq_pair_right.trans_eq (hdiscrete _ _ hright))
  · exact bot_unique (bSet.eq_of_eq_pair_left.trans_eq (hdiscrete _ _ hleft))

def domainName (P : BooleanPoset B I) (element : I → bSet B) : bSet B :=
  weightedSet element P.member

def orderName (P : BooleanPoset B I) (element : I → bSet B) : bSet B :=
  weightedSet (pairLabels element) (fun ij => P.leValue ij.1 ij.2)

theorem domainName_member (P : BooleanPoset B I) (element : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (element i =ᴮ element j) = ⊥) (i : I) :
    (element i ∈ᴮ domainName P element) = P.member i :=
  member_weightedSet_discrete element hdiscrete P.member i

theorem orderName_edge (P : BooleanPoset B I) (element : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (element i =ᴮ element j) = ⊥) (i j : I) :
    edgeValue (V B) (orderName P element) (element i) (element j) = P.leValue i j :=
  member_weightedSet_discrete (pairLabels element) (pairLabels_discrete element hdiscrete)
    (fun ij => P.leValue ij.1 ij.2) (i, j)

theorem compatibility_eq (P : BooleanPoset B I) (element : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (element i =ᴮ element j) = ⊥) (i j : I) :
    Erdos597Object.compatibleValue (V B) (domainName P element) (orderName P element)
      (element i) (element j) = BooleanIteration.compatibleValue P i j := by
  unfold Erdos597Object.compatibleValue
  change (⨆ z : bSet B, (z ∈ᴮ weightedSet element P.member) ⊓
    (edgeValue (V B) (orderName P element) z (element i) ⊓
      edgeValue (V B) (orderName P element) z (element j))) = _
  rw [weighted_bounded_exists element P.member _
    (compatibleWitness_ext (orderName P element) (element i) (element j))]
  unfold BooleanIteration.compatibleValue
  apply iSup_congr
  intro k
  rw [orderName_edge P element hdiscrete, orderName_edge P element hdiscrete]
  exact inf_eq_right.mpr ((inf_le_left : P.leValue k i ⊓ P.leValue k j ≤ P.leValue k i).trans
    ((P.le_members k i).trans inf_le_left))

theorem booleanCCC_of_firstOrder (P : BooleanPoset B I) (element : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (element i =ᴮ element j) = ⊥)
    (hccc : ⊤ ≤ countableChainConditionValue (V B) (domainName P element) (orderName P element)) :
    BooleanCountableChainCondition P := by
  intro J label weight hvalid hincompatible
  apply countable_cover_of_firstOrder_ccc (fun j => element (label j)) weight
    (domainName P element) (orderName P element)
  · intro j
    rw [domainName_member P element hdiscrete]
    exact hvalid j
  · intro j
    rw [orderName_edge P element hdiscrete]
    exact (hvalid j).trans (P.reflexive (label j))
  · intro j k hjk
    rw [compatibility_eq P element hdiscrete]
    exact hincompatible j k hjk
  · exact hccc

theorem two_step_ccc_of_firstOrder (hB : Flypitch.BA_CCC B)
    (P : BooleanPoset B I) (element : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (element i =ᴮ element j) = ⊥)
    (hccc : ⊤ ≤ countableChainConditionValue (V B) (domainName P element) (orderName P element)) :
    Erdos597Object.MartinTransport.CountableChainCondition (Condition P) :=
  two_step_ccc hB P (booleanCCC_of_firstOrder P element hdiscrete hccc)

theorem two_step_ccc_checkLabels (hB : Flypitch.BA_CCC B) (P : BooleanPoset B I)
    (hccc : ⊤ ≤ countableChainConditionValue (V B)
      (domainName P checkLabel) (orderName P checkLabel)) :
    Erdos597Object.MartinTransport.CountableChainCondition (Condition P) :=
  two_step_ccc_of_firstOrder hB P checkLabel (fun _ _ h => checkLabel_discrete h) hccc

end Erdos597Object.BooleanPosetCoding
