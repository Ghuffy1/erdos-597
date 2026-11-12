import Erdos597Object.PosetRelabeling
import Erdos597Object.WeightedFilterModel

set_option backward.isDefEq.respectTransparency false

/-! Dense coefficient arrays and completion outside a Boolean context. -/

namespace Erdos597Object.CodedDensity

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanIteration BooleanSets BooleanPosetCoding

variable {B I J : Type} [CompleteBooleanAlgebra B]

theorem denseValue_of_coefficients (P : BooleanPoset B I) (dense : I → B)
    (hsubset : ∀ i, dense i ≤ P.member i)
    (hdense : ∀ j, P.member j ≤ ⨆ i, dense i ⊓ P.leValue i j) :
    ⊤ ≤ denseValue (V B) (domainName P checkLabel) (orderName P checkLabel)
      (weightedSet checkLabel dense) := by
  have hdiscrete : ∀ i j : I, i ≠ j →
      (checkLabel (B := B) i =ᴮ checkLabel j) = ⊥ :=
    fun _ _ h => checkLabel_discrete h
  apply le_inf
  · rw [BooleanAntichains.weighted_subset_value]
    apply le_iInf
    intro i
    rw [domainName_member P checkLabel hdiscrete]
    exact (lattice.imp_eq_top_iff.mpr (hsubset i)).ge
  · change ⊤ ≤ ⨅ y : bSet B, lattice.imp (y ∈ᴮ weightedSet checkLabel P.member)
      (⨆ x : bSet B, (x ∈ᴮ weightedSet checkLabel dense) ⊓
        edgeValue (V B) (orderName P checkLabel) x y)
    rw [weighted_bounded_forall checkLabel P.member _
      (bSet.B_ext_iSup fun x => bSet.B_ext_inf (bSet.B_ext_const _)
        (BooleanInjections.edge_right_ext (orderName P checkLabel) x))]
    apply le_iInf
    intro j
    apply lattice.bv_imp_intro
    rw [top_inf_eq, weighted_bounded_exists checkLabel dense _
      (BooleanInjections.edge_left_ext (orderName P checkLabel) (checkLabel j))]
    simpa only [orderName_edge P checkLabel hdiscrete] using! hdense j

def outsideDense (context active : B) (P : BooleanPoset B I) (dense : I → B) : Option I → B
  | none => contextᶜ
  | some i => (activeᶜ ⊓ P.member i) ⊔ dense i

theorem outsideDense_subset (context active : B) (P : BooleanPoset B I) (dense : I → B)
    (hsubset : ∀ i, dense i ≤ P.member i) :
    ∀ i, outsideDense context active P dense i ≤ (ContextCompletion.withOutside context P).member i := by
  intro i
  cases i with
  | none => exact le_rfl
  | some i => exact sup_le inf_le_right (hsubset i)

theorem outsideDense_dense (context active : B) (P : BooleanPoset B I) (dense : I → B)
    (hdense : ∀ j, active ⊓ P.member j ≤ ⨆ i, dense i ⊓ P.leValue i j) :
    ∀ j, (ContextCompletion.withOutside context P).member j ≤
      ⨆ i, outsideDense context active P dense i ⊓
        (ContextCompletion.withOutside context P).leValue i j := by
  intro j
  cases j with
  | none => exact le_iSup_of_le none (by simp [outsideDense, ContextCompletion.withOutside])
  | some j =>
    change P.member j ≤ _
    have hinactive : activeᶜ ⊓ P.member j ≤
        outsideDense context active P dense (some j) ⊓
          (ContextCompletion.withOutside context P).leValue (some j) (some j) :=
      le_inf le_sup_left (inf_le_right.trans (P.reflexive j))
    have hactive : active ⊓ P.member j ≤
        ⨆ i, outsideDense context active P dense i ⊓
          (ContextCompletion.withOutside context P).leValue i (some j) :=
      (hdense j).trans (iSup_le fun i => le_iSup_of_le (some i) (inf_le_inf le_sup_right le_rfl))
    have hsplit : P.member j = (activeᶜ ⊓ P.member j) ⊔ (active ⊓ P.member j) := by
      rw [← inf_sup_right, compl_sup_eq_top, top_inf_eq]
    calc
      P.member j = (activeᶜ ⊓ P.member j) ⊔ (active ⊓ P.member j) := hsplit
      _ ≤ _ := sup_le (le_iSup_of_le (some j) hinactive) hactive

theorem relabel_dense (e : J ≃ I) (P : BooleanPoset B I) (dense : I → B)
    (hdense : ∀ j, P.member j ≤ ⨆ i, dense i ⊓ P.leValue i j) :
    ∀ j, (PosetRelabeling.relabel e P).member j ≤
      ⨆ i, dense (e i) ⊓ (PosetRelabeling.relabel e P).leValue i j := by
  intro j
  change P.member (e j) ≤ ⨆ i, dense (e i) ⊓ P.leValue (e i) (e j)
  exact (hdense (e j)).trans_eq
    (e.surjective.iSup_comp (fun i => dense i ⊓ P.leValue i (e j))).symm

end Erdos597Object.CodedDensity
