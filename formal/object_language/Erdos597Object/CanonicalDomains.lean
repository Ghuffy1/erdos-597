import Erdos597Object.CanonicalRelations
import Erdos597Object.OmegaOneLabels

set_option backward.isDefEq.respectTransparency false

/-! Canonical labelled domains for the ordinal square and the red target. -/

namespace Erdos597Object.CanonicalDomains

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet Ordinal
open BooleanSets BooleanFiniteGraphs BooleanSetRelabeling CanonicalRelations

variable {B I J : Type} [CompleteBooleanAlgebra B]

noncomputable def omegaOneName : bSet B := bSet.check (ω₁ : Ordinal.{0}).toPSet

theorem product_labelDomain (left : I → bSet B) (right : J → bSet B) :
    bSet.prod (labelDomain left) (labelDomain right) =
      labelDomain (fun ij : I × J => bSet.pair (left ij.1) (right ij.2)) := by
  simp [labelDomain, weightedSet, bSet.prod, bSet.type, bSet.func, bSet.bval]

theorem omega_labelDomain :
    (⊤ : B) ≤ labelDomain (fun n : ℕ => bSet.ofNat n) =ᴮ bSet.omega := by
  have h := weighted_relabel (B := B) (Equiv.ulift.symm : ℕ ≃ ULift ℕ)
    (fun n => bSet.ofNat n.down) (fun _ => ⊤)
  exact h

theorem pair_discrete (left : I → bSet B) (right : J → bSet B)
    (hleft : ∀ i j, i ≠ j → (left i =ᴮ left j) = ⊥)
    (hright : ∀ i j, i ≠ j → (right i =ᴮ right j) = ⊥) :
    ∀ ij kl : I × J, ij ≠ kl →
      (bSet.pair (left ij.1) (right ij.2) =ᴮ bSet.pair (left kl.1) (right kl.2)) = ⊥ := by
  classical
  intro ij kl hne
  by_cases hfirst : ij.1 = kl.1
  · have hsecond : ij.2 ≠ kl.2 := fun h => hne (Prod.ext hfirst h)
    exact bot_unique (bSet.eq_of_eq_pair_right.trans_eq (hright _ _ hsecond))
  · exact bot_unique (bSet.eq_of_eq_pair_left.trans_eq (hleft _ _ hfirst))

noncomputable def squareLabel (ij : ScheduledIteration.Labels × ScheduledIteration.Labels) : bSet B :=
  bSet.pair (OmegaOneLabels.element ij.1) (OmegaOneLabels.element ij.2)

noncomputable def blockLabel (ij : ℕ × ScheduledIteration.Labels) : bSet B :=
  bSet.pair (bSet.ofNat ij.1) (OmegaOneLabels.element ij.2)

noncomputable def squareDomain : bSet B := labelDomain squareLabel

noncomputable def blockDomain : bSet B := labelDomain blockLabel

noncomputable def squareOrder : bSet B := lexOrderName squareLabel

noncomputable def blockOrder : bSet B := lexOrderName blockLabel

theorem squareLabel_discrete :
    ∀ i j, i ≠ j → (squareLabel (B := B) i =ᴮ squareLabel j) = ⊥ :=
  pair_discrete OmegaOneLabels.element OmegaOneLabels.element
    OmegaOneLabels.element_discrete OmegaOneLabels.element_discrete

theorem blockLabel_discrete :
    ∀ i j, i ≠ j → (blockLabel (B := B) i =ᴮ blockLabel j) = ⊥ :=
  pair_discrete (fun n => bSet.ofNat n) OmegaOneLabels.element
    (fun _ _ h => bSet.ofNat_inj h) OmegaOneLabels.element_discrete

theorem squareDomain_eq_product :
    (⊤ : B) ≤ squareDomain =ᴮ bSet.prod omegaOneName omegaOneName := by
  unfold squareDomain squareLabel
  rw [← product_labelDomain]
  exact bSet.prod_congr OmegaOneLabels.labelSet_eq_check OmegaOneLabels.labelSet_eq_check

theorem blockDomain_eq_product :
    (⊤ : B) ≤ blockDomain =ᴮ bSet.prod bSet.omega omegaOneName := by
  unfold blockDomain blockLabel
  rw [← product_labelDomain]
  exact bSet.prod_congr omega_labelDomain OmegaOneLabels.labelSet_eq_check

theorem square_product_spec :
    (⊤ : B) ≤ cartesianProductValue (V B) omegaOneName omegaOneName squareDomain := by
  rw [cartesianProduct_eq]
  exact squareDomain_eq_product

theorem block_product_spec :
    (⊤ : B) ≤ cartesianProductValue (V B) bSet.omega omegaOneName blockDomain := by
  rw [cartesianProduct_eq]
  exact blockDomain_eq_product

theorem square_order_spec : (⊤ : B) ≤ lexOrderValue (V B) squareDomain squareOrder :=
  lexOrderName_spec squareLabel squareLabel_discrete

theorem block_order_spec : (⊤ : B) ≤ lexOrderValue (V B) blockDomain blockOrder :=
  lexOrderName_spec blockLabel blockLabel_discrete

end Erdos597Object.CanonicalDomains
