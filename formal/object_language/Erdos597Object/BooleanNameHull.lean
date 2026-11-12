import Erdos597Object.IndexedHull
import Erdos597Object.PosetNameWitnesses

set_option backward.isDefEq.respectTransparency false

/-! A small indexed family of condition names closed under the required witnesses. -/

namespace Erdos597Object.BooleanNameHull

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet Cardinal
open BooleanSets PosetNameWitnesses

variable {B I : Type} [CompleteBooleanAlgebra B]

noncomputable def combine (context : B) (domain relation seed : bSet B)
    (hseed : context ≤ seed ∈ᴮ domain) (x y : bSet B) : bSet B :=
  Classical.choose (exists_common_witness domain relation seed x y hseed)

theorem combine_spec (context : B) (domain relation seed : bSet B)
    (hseed : context ≤ seed ∈ᴮ domain) (x y : bSet B) :
    context ≤ combine context domain relation seed hseed x y ∈ᴮ domain ∧
      context ⊓ Erdos597Object.compatibleValue (V B) domain relation x y ≤
        edgeValue (V B) relation (combine context domain relation seed hseed x y) x ⊓
          edgeValue (V B) relation (combine context domain relation seed hseed x y) y :=
  Classical.choose_spec (exists_common_witness domain relation seed x y hseed)

noncomputable def step (context : B) (domain relation seed : bSet B)
    (hseed : context ≤ seed ∈ᴮ domain) (active : I → B) (denseSet : I → bSet B)
    (hdense : ∀ i, context ⊓ active i ≤ denseValue (V B) domain relation (denseSet i))
    (i : I) (x : bSet B) : bSet B :=
  Classical.choose (exists_dense_witness domain relation (denseSet i) seed x hseed
    (active i ⊓ (x ∈ᴮ domain)) (inf_le_right.trans inf_le_right)
    ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans (hdense i)))

theorem step_spec (context : B) (domain relation seed : bSet B)
    (hseed : context ≤ seed ∈ᴮ domain) (active : I → B) (denseSet : I → bSet B)
    (hdense : ∀ i, context ⊓ active i ≤ denseValue (V B) domain relation (denseSet i))
    (i : I) (x : bSet B) :
    context ≤ step context domain relation seed hseed active denseSet hdense i x ∈ᴮ domain ∧
      context ⊓ (active i ⊓ (x ∈ᴮ domain)) ≤
        (step context domain relation seed hseed active denseSet hdense i x ∈ᴮ denseSet i) ⊓
          edgeValue (V B) relation (step context domain relation seed hseed active denseSet hdense i x) x :=
  Classical.choose_spec (exists_dense_witness domain relation (denseSet i) seed x hseed
    (active i ⊓ (x ∈ᴮ domain)) (inf_le_right.trans inf_le_right)
    ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans (hdense i)))

noncomputable def name (context : B) (domain relation seed : bSet B)
    (hseed : context ≤ seed ∈ᴮ domain) (active : I → B) (denseSet : I → bSet B)
    (hdense : ∀ i, context ⊓ active i ≤ denseValue (V B) domain relation (denseSet i)) :
    IndexedHull.Labels I → bSet B :=
  IndexedHull.evaluate seed (combine context domain relation seed hseed)
    (step context domain relation seed hseed active denseSet hdense)

theorem name_member (context : B) (domain relation seed : bSet B)
    (hseed : context ≤ seed ∈ᴮ domain) (active : I → B) (denseSet : I → bSet B)
    (hdense : ∀ i, context ⊓ active i ≤ denseValue (V B) domain relation (denseSet i))
    (label : IndexedHull.Labels I) :
    context ≤ name context domain relation seed hseed active denseSet hdense label ∈ᴮ domain :=
  IndexedHull.evaluateStage_property seed _ _ (fun x => context ≤ x ∈ᴮ domain) hseed
    (fun x y _ _ => (combine_spec context domain relation seed hseed x y).1)
    (fun i x _ => (step_spec context domain relation seed hseed active denseSet hdense i x).1)
    label.1 label.2

theorem name_common (context : B) (domain relation seed : bSet B)
    (hseed : context ≤ seed ∈ᴮ domain) (active : I → B) (denseSet : I → bSet B)
    (hdense : ∀ i, context ⊓ active i ≤ denseValue (V B) domain relation (denseSet i))
    (a b : IndexedHull.Labels I) :
    ∃ k : IndexedHull.Labels I,
      context ⊓ Erdos597Object.compatibleValue (V B) domain relation
        (name context domain relation seed hseed active denseSet hdense a)
        (name context domain relation seed hseed active denseSet hdense b) ≤
      edgeValue (V B) relation (name context domain relation seed hseed active denseSet hdense k)
        (name context domain relation seed hseed active denseSet hdense a) ⊓
      edgeValue (V B) relation (name context domain relation seed hseed active denseSet hdense k)
        (name context domain relation seed hseed active denseSet hdense b) := by
  obtain ⟨k, hk⟩ := IndexedHull.evaluate_combine seed
    (combine context domain relation seed hseed) (step context domain relation seed hseed active denseSet hdense) a b
  refine ⟨k, ?_⟩
  change name context domain relation seed hseed active denseSet hdense k = _ at hk
  rw [hk]
  exact (combine_spec context domain relation seed hseed _ _).2

theorem name_dense (context : B) (domain relation seed : bSet B)
    (hseed : context ≤ seed ∈ᴮ domain) (active : I → B) (denseSet : I → bSet B)
    (hdense : ∀ i, context ⊓ active i ≤ denseValue (V B) domain relation (denseSet i))
    (d : I) (a : IndexedHull.Labels I) :
    ∃ k : IndexedHull.Labels I, context ⊓ active d ≤
      (name context domain relation seed hseed active denseSet hdense k ∈ᴮ denseSet d) ⊓
        edgeValue (V B) relation (name context domain relation seed hseed active denseSet hdense k)
          (name context domain relation seed hseed active denseSet hdense a) := by
  obtain ⟨k, hk⟩ := IndexedHull.evaluate_step seed
    (combine context domain relation seed hseed) (step context domain relation seed hseed active denseSet hdense) d a
  refine ⟨k, ?_⟩
  change name context domain relation seed hseed active denseSet hdense k = _ at hk
  rw [hk]
  apply (le_inf inf_le_left (le_inf inf_le_right
    (inf_le_left.trans (name_member context domain relation seed hseed active denseSet hdense a)))).trans
  exact (step_spec context domain relation seed hseed active denseSet hdense d _).2

end Erdos597Object.BooleanNameHull
