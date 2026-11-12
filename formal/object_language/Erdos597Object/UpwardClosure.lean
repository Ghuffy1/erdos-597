import Erdos597Object.HullCoefficients

set_option backward.isDefEq.respectTransparency false

/-! Extend a filter on the witness-closed family to a filter on the original poset. -/

namespace Erdos597Object.UpwardClosure

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanAntichains PresentedPosets

variable {B I : Type} [CompleteBooleanAlgebra B]

noncomputable def predicate (relation : bSet B) (element : I → bSet B) (value : I → B) (x : bSet B) : B :=
  ⨆ i, value i ⊓ edgeValue (V B) relation (element i) x

noncomputable def weight (domain relation : bSet B) (element : I → bSet B) (value : I → B)
    (a : domain.type) : B := domain.bval a ⊓ predicate relation element value (domain.func a)

theorem predicate_ext (relation : bSet B) (element : I → bSet B) (value : I → B) :
    bSet.B_ext (predicate relation element value) :=
  bSet.B_ext_iSup fun i => bSet.B_ext_inf (bSet.B_ext_const _) (edge_right_ext relation (element i))

theorem predicate_context {context : B} (relation : bSet B) (element : I → bSet B) (value : I → B)
    (hcontext : ∀ i, value i ≤ context) (x : bSet B) : predicate relation element value x ≤ context :=
  iSup_le fun i => inf_le_left.trans (hcontext i)

theorem generator_value {context : B} (domain relation : bSet B) (element : I → bSet B) (value : I → B)
    (hcontext : ∀ i, value i ≤ context) (hmembers : ∀ i, value i ≤ element i ∈ᴮ domain)
    (horder : context ≤ partialOrderValue (V B) domain relation) (i : I) :
    value i ≤ predicate relation element value (element i) :=
  le_iSup_of_le i (le_inf le_rfl
    (reflexive_at domain relation (element i) ((hcontext i).trans horder) (hmembers i)))

theorem generator_cover {context : B} (domain relation : bSet B) (element : I → bSet B) (value : I → B)
    (hcontext : ∀ i, value i ≤ context) (hmembers : ∀ i, value i ≤ element i ∈ᴮ domain)
    (horder : context ≤ partialOrderValue (V B) domain relation) (i : I) :
    value i ≤ ⨆ a, weight domain relation element value a := by
  have h : value i ≤ ⨆ x : bSet B, (x ∈ᴮ domain) ⊓ predicate relation element value x :=
    le_iSup_of_le (element i) (le_inf (hmembers i)
      (generator_value domain relation element value hcontext hmembers horder i))
  rw [← bSet.bounded_exists domain _ (predicate_ext relation element value)] at h
  exact h

theorem predicate_upward {context bound : B} (domain relation : bSet B)
    (element : I → bSet B) (value : I → B)
    (hmembers : ∀ i, value i ≤ element i ∈ᴮ domain)
    (horder : context ≤ partialOrderValue (V B) domain relation)
    (x y : bSet B) (hc : bound ≤ context) (hx : bound ≤ x ∈ᴮ domain) (hy : bound ≤ y ∈ᴮ domain)
    (hxy : bound ≤ edgeValue (V B) relation x y) (hvalue : bound ≤ predicate relation element value x) :
    bound ≤ predicate relation element value y := by
  apply (le_inf le_rfl hvalue).trans
  apply lattice.bv_cases_right
  intro i
  let part := bound ⊓ (value i ⊓ edgeValue (V B) relation (element i) x)
  have hiy : part ≤ edgeValue (V B) relation (element i) y :=
    transitive_at domain relation (element i) x y ((inf_le_left.trans hc).trans horder)
      ((inf_le_right.trans inf_le_left).trans (hmembers i)) (inf_le_left.trans hx)
      (inf_le_left.trans hy) (inf_le_right.trans inf_le_right) (inf_le_left.trans hxy)
  exact le_iSup_of_le i (le_inf (inf_le_right.trans inf_le_left) hiy)

theorem predicate_directed {context bound : B} (domain relation : bSet B)
    (element : I → bSet B) (value : I → B)
    (hcontext : ∀ i, value i ≤ context) (hmembers : ∀ i, value i ≤ element i ∈ᴮ domain)
    (horder : context ≤ partialOrderValue (V B) domain relation)
    (hdir : ∀ i j, value i ⊓ value j ≤ ⨆ k, value k ⊓
      (edgeValue (V B) relation (element k) (element i) ⊓ edgeValue (V B) relation (element k) (element j)))
    (x y : bSet B) (hc : bound ≤ context) (hx : bound ≤ x ∈ᴮ domain) (hy : bound ≤ y ∈ᴮ domain)
    (hvalueX : bound ≤ predicate relation element value x) (hvalueY : bound ≤ predicate relation element value y) :
    bound ≤ ⨆ z : bSet B, (z ∈ᴮ domain) ⊓ (predicate relation element value z ⊓
      (edgeValue (V B) relation z x ⊓ edgeValue (V B) relation z y)) := by
  apply (le_inf le_rfl hvalueX).trans
  apply lattice.bv_cases_right
  intro i
  let firstPart := bound ⊓ (value i ⊓ edgeValue (V B) relation (element i) x)
  have hsecond : firstPart ≤ predicate relation element value y := inf_le_left.trans hvalueY
  apply (le_inf le_rfl hsecond).trans
  apply lattice.bv_cases_right
  intro j
  let pairPart := firstPart ⊓ (value j ⊓ edgeValue (V B) relation (element j) y)
  have hi : pairPart ≤ value i := inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hj : pairPart ≤ value j := inf_le_right.trans inf_le_left
  have hix : pairPart ≤ edgeValue (V B) relation (element i) x :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hjy : pairPart ≤ edgeValue (V B) relation (element j) y := inf_le_right.trans inf_le_right
  have hbase : pairPart ≤ bound := inf_le_left.trans inf_le_left
  have hlower := (le_inf hi hj).trans (hdir i j)
  apply (le_inf le_rfl hlower).trans
  apply lattice.bv_cases_right
  intro k
  let lowerPart := pairPart ⊓ (value k ⊓
    (edgeValue (V B) relation (element k) (element i) ⊓ edgeValue (V B) relation (element k) (element j)))
  have hk : lowerPart ≤ value k := inf_le_right.trans inf_le_left
  have hc' : lowerPart ≤ context := (inf_le_left.trans hbase).trans hc
  have hkx := transitive_at domain relation (element k) (element i) x (hc'.trans horder)
    (hk.trans (hmembers k)) ((inf_le_left.trans hi).trans (hmembers i))
    ((inf_le_left.trans hbase).trans hx)
    (inf_le_right.trans (inf_le_right.trans inf_le_left)) (inf_le_left.trans hix)
  have hky := transitive_at domain relation (element k) (element j) y (hc'.trans horder)
    (hk.trans (hmembers k)) ((inf_le_left.trans hj).trans (hmembers j))
    ((inf_le_left.trans hbase).trans hy)
    (inf_le_right.trans (inf_le_right.trans inf_le_right)) (inf_le_left.trans hjy)
  exact le_iSup_of_le (element k) (le_inf (hk.trans (hmembers k))
    (le_inf (hk.trans (generator_value domain relation element value hcontext hmembers horder k))
      (le_inf hkx hky)))

theorem orderFilter_value {context : B} (domain relation : bSet B)
    (element : I → bSet B) (value : I → B)
    (hcontext : ∀ i, value i ≤ context) (hmembers : ∀ i, value i ≤ element i ∈ᴮ domain)
    (horder : context ≤ partialOrderValue (V B) domain relation)
    (hcover : context ≤ ⨆ i, value i)
    (hdir : ∀ i j, value i ⊓ value j ≤ ⨆ k, value k ⊓
      (edgeValue (V B) relation (element k) (element i) ⊓ edgeValue (V B) relation (element k) (element j))) :
    context ≤ orderFilterValue (V B) domain relation
      (weightedSet domain.func (weight domain relation element value)) := by
  have hself : context ≤ domain =ᴮ weightedSet domain.func domain.bval := by
    cases domain
    exact bSet.bv_refl
  apply PresentedFilters.orderFilter_from_weights context domain relation domain.func domain.bval
    (weight domain relation element value) hself
  · intro a
    exact inf_le_left.trans (bSet.mem.mk' domain a)
  · exact hcover.trans (iSup_le (generator_cover domain relation element value hcontext hmembers horder))
  · intro a b
    let part := weight domain relation element value a ⊓ domain.bval b ⊓
      edgeValue (V B) relation (domain.func a) (domain.func b)
    have hwa : part ≤ weight domain relation element value a := inf_le_left.trans inf_le_left
    exact le_inf (inf_le_left.trans inf_le_right)
      (predicate_upward domain relation element value hmembers horder _ _
        ((hwa.trans inf_le_right).trans (predicate_context relation element value hcontext _))
        ((hwa.trans inf_le_left).trans (bSet.mem.mk' domain a))
        ((inf_le_left.trans inf_le_right).trans (bSet.mem.mk' domain b))
        inf_le_right (hwa.trans inf_le_right))
  · intro a b
    let part := weight domain relation element value a ⊓ weight domain relation element value b
    have hwa : part ≤ weight domain relation element value a := inf_le_left
    have hwb : part ≤ weight domain relation element value b := inf_le_right
    have h := predicate_directed domain relation element value hcontext hmembers horder hdir _ _
      ((hwa.trans inf_le_right).trans (predicate_context relation element value hcontext _))
      ((hwa.trans inf_le_left).trans (bSet.mem.mk' domain a))
      ((hwb.trans inf_le_left).trans (bSet.mem.mk' domain b))
      (hwa.trans inf_le_right) (hwb.trans inf_le_right)
    rw [← bSet.bounded_exists domain _ (bSet.B_ext_inf (predicate_ext relation element value)
      (compatibleWitness_ext relation (domain.func a) (domain.func b)))] at h
    simpa only [part, weight, inf_assoc] using! h

theorem meets_value {context active : B} (domain relation denseSet : bSet B)
    (element : I → bSet B) (value : I → B)
    (hcontext : ∀ i, value i ≤ context) (hmembers : ∀ i, value i ≤ element i ∈ᴮ domain)
    (horder : context ≤ partialOrderValue (V B) domain relation)
    (hmeets : active ≤ ⨆ i, value i ⊓ (element i ∈ᴮ denseSet)) :
    active ≤ ⨆ a, weight domain relation element value a ⊓ (domain.func a ∈ᴮ denseSet) := by
  have hpoint (i : I) : value i ⊓ (element i ∈ᴮ denseSet) ≤
      ⨆ x : bSet B, (x ∈ᴮ domain) ⊓ (predicate relation element value x ⊓ (x ∈ᴮ denseSet)) :=
    le_iSup_of_le (element i) (le_inf (inf_le_left.trans (hmembers i))
      (le_inf (inf_le_left.trans (generator_value domain relation element value hcontext hmembers horder i)) inf_le_right))
  have h := hmeets.trans (iSup_le hpoint)
  rw [← bSet.bounded_exists domain _ (bSet.B_ext_inf (predicate_ext relation element value)
    (bSet.B_ext_mem_left denseSet))] at h
  simpa only [weight, inf_assoc] using! h

end Erdos597Object.UpwardClosure
