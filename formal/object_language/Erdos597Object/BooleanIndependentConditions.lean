import Erdos597Object.BooleanWeakRows

set_option backward.isDefEq.respectTransparency false

/-! Finite independent conditions on the canonical weak row family. -/

namespace Erdos597Object.BooleanIndependentConditions

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet Cardinal
open BooleanSets BooleanIteration BooleanPosetCoding BooleanPosetModel
open BooleanColumns CanonicalDomains

abbrev Vertex := ℕ × (ℕ × ScheduledIteration.Labels)

variable {B : Type} [CompleteBooleanAlgebra B]

open Classical in
attribute [local instance] propDecidable

noncomputable def vertexWeight (rows : ℕ → bSet B) (cut : Erdos597.One) (v : Vertex) : B := by
  classical
  exact if cut < column v.2.2 then blockLabel v.2 ∈ᴮ rows v.1 else ⊥

noncomputable def independentWeight (relation : bSet B) (left right : Finset Vertex) : B := by
  classical
  exact ⨅ x ∈ left, ⨅ y ∈ right,
    if x.1 = y.1 then ⊤ else (edgeValue (V B) relation (blockLabel x.2) (blockLabel y.2))ᶜ

noncomputable def weight (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (points : Finset Vertex) : B :=
  base ⊓ ((⨅ v ∈ points, vertexWeight rows cut v) ⊓ independentWeight relation points points)

theorem independentWeight_mono (relation : bSet B) {left right bigLeft bigRight : Finset Vertex}
    (hleft : left ⊆ bigLeft) (hright : right ⊆ bigRight) :
    independentWeight relation bigLeft bigRight ≤ independentWeight relation left right := by
  apply le_iInf
  intro x
  apply le_iInf
  intro hx
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  exact (iInf_le _ x).trans ((iInf_le _ (hleft hx)).trans
    ((iInf_le _ y).trans (iInf_le _ (hright hy))))

theorem weight_le_base (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (points : Finset Vertex) : weight base rows relation cut points ≤ base :=
  inf_le_left

theorem weight_vertex (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (points : Finset Vertex) (v : Vertex) (hv : v ∈ points) :
    weight base rows relation cut points ≤ vertexWeight rows cut v :=
  (inf_le_right.trans inf_le_left).trans ((iInf_le _ v).trans (iInf_le _ hv))

theorem weight_row_member (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (points : Finset Vertex) (v : Vertex) (hv : v ∈ points) :
    weight base rows relation cut points ≤ blockLabel v.2 ∈ᴮ rows v.1 := by
  classical
  apply (weight_vertex base rows relation cut points v hv).trans
  unfold vertexWeight
  split_ifs <;> simp only [le_refl, bot_le]

theorem weight_below_cut (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (points : Finset Vertex) (v : Vertex) (hv : v ∈ points)
    (hcut : ¬ cut < column v.2.2) : weight base rows relation cut points = ⊥ := by
  apply bot_unique
  simpa only [vertexWeight, ite_eq_right hcut] using weight_vertex base rows relation cut points v hv

theorem weight_independent (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (points : Finset Vertex) (x y : Vertex)
    (hx : x ∈ points) (hy : y ∈ points) (hne : x.1 ≠ y.1) :
    weight base rows relation cut points ≤
      (edgeValue (V B) relation (blockLabel x.2) (blockLabel y.2))ᶜ := by
  have h := (inf_le_right.trans inf_le_right :
    weight base rows relation cut points ≤ independentWeight relation points points)
  have hxy := h.trans ((iInf_le _ x).trans ((iInf_le _ hx).trans
    ((iInf_le _ y).trans (iInf_le _ hy))))
  simpa only [weight, ite_eq_right hne] using hxy

theorem weight_mono (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) {small large : Finset Vertex} (hsub : small ⊆ large) :
    weight base rows relation cut large ≤ weight base rows relation cut small := by
  apply le_inf inf_le_left
  apply le_inf
  · apply le_iInf
    intro v
    apply le_iInf
    intro hv
    exact weight_vertex base rows relation cut large v (hsub hv)
  · exact (inf_le_right.trans inf_le_right).trans (independentWeight_mono relation hsub hsub)

theorem weight_empty (base : B) (rows : ℕ → bSet B) (relation : bSet B) (cut : Erdos597.One) :
    weight base rows relation cut ∅ = base := by
  simp [weight, independentWeight]

theorem weight_union (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (left right : Finset Vertex) :
    weight base rows relation cut (left ∪ right) =
      (weight base rows relation cut left ⊓ weight base rows relation cut right) ⊓
        (independentWeight relation left right ⊓ independentWeight relation right left) := by
  classical
  apply le_antisymm
  · apply le_inf
    · exact le_inf (weight_mono base rows relation cut Finset.subset_union_left)
        (weight_mono base rows relation cut Finset.subset_union_right)
    · exact le_inf
        ((inf_le_right.trans inf_le_right).trans
          (independentWeight_mono relation Finset.subset_union_left Finset.subset_union_right))
        ((inf_le_right.trans inf_le_right).trans
          (independentWeight_mono relation Finset.subset_union_right Finset.subset_union_left))
  · let part := (weight base rows relation cut left ⊓ weight base rows relation cut right) ⊓
        (independentWeight relation left right ⊓ independentWeight relation right left)
    have hleft : part ≤ weight base rows relation cut left := inf_le_left.trans inf_le_left
    have hright : part ≤ weight base rows relation cut right := inf_le_left.trans inf_le_right
    apply le_inf (hleft.trans inf_le_left)
    apply le_inf
    · apply le_iInf
      intro v
      apply le_iInf
      intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hleft.trans (weight_vertex base rows relation cut left v hv)
      · exact hright.trans (weight_vertex base rows relation cut right v hv)
    · apply le_iInf
      intro x
      apply le_iInf
      intro hx
      apply le_iInf
      intro y
      apply le_iInf
      intro hy
      rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
      · exact (hleft.trans (inf_le_right.trans inf_le_right)).trans
          ((iInf_le _ x).trans ((iInf_le _ hx).trans ((iInf_le _ y).trans (iInf_le _ hy))))
      · exact (inf_le_right.trans inf_le_left : part ≤ independentWeight relation left right).trans
          ((iInf_le _ x).trans ((iInf_le _ hx).trans ((iInf_le _ y).trans (iInf_le _ hy))))
      · exact (inf_le_right.trans inf_le_right : part ≤ independentWeight relation right left).trans
          ((iInf_le _ x).trans ((iInf_le _ hx).trans ((iInf_le _ y).trans (iInf_le _ hy))))
      · exact (hright.trans (inf_le_right.trans inf_le_right)).trans
          ((iInf_le _ x).trans ((iInf_le _ hx).trans ((iInf_le _ y).trans (iInf_le _ hy))))

noncomputable def forcing (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) : BooleanPoset B (Finset Vertex) := by
  classical
  refine {
    member := weight base rows relation cut
    leValue := fun left right => if right ⊆ left then weight base rows relation cut left else ⊥
    le_members := ?_
    reflexive := ?_
    transitive := ?_
    antisymmetric := ?_
  }
  · intro left right
    by_cases h : right ⊆ left
    · rw [ite_eq_left h]
      exact le_inf le_rfl (weight_mono base rows relation cut h)
    · simp only [ite_eq_right h, bot_le]
  · intro points
    simp only [ite_true, le_refl]
  · intro left middle right
    by_cases hleft : middle ⊆ left
    · by_cases hright : right ⊆ middle
      · simp only [ite_eq_left hleft, ite_eq_left hright, ite_eq_left (hright.trans hleft)]
        exact inf_le_left
      · simp only [ite_eq_left hleft, ite_eq_right hright, inf_bot_eq, bot_le]
    · simp only [ite_eq_right hleft, bot_inf_eq, bot_le]
  · intro left right hne
    by_cases hleft : right ⊆ left
    · by_cases hright : left ⊆ right
      · exact False.elim (hne (Finset.Subset.antisymm hright hleft))
      · simp only [ite_eq_left hleft, ite_eq_right hright, inf_bot_eq]
    · simp only [ite_eq_right hleft, bot_inf_eq]

theorem compatible_eq_union (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (left right : Finset Vertex) :
    BooleanIteration.compatibleValue (forcing base rows relation cut) left right =
      weight base rows relation cut (left ∪ right) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro points
    change (if left ⊆ points then weight base rows relation cut points else ⊥) ⊓
      (if right ⊆ points then weight base rows relation cut points else ⊥) ≤ _
    by_cases hleft : left ⊆ points
    · by_cases hright : right ⊆ points
      · simp only [ite_eq_left hleft, ite_eq_left hright, inf_idem]
        exact weight_mono base rows relation cut (Finset.union_subset hleft hright)
      · simp only [ite_eq_right hright, inf_bot_eq, bot_le]
    · simp only [ite_eq_right hleft, bot_inf_eq, bot_le]
  · apply le_iSup_of_le (left ∪ right)
    change _ ≤ (if left ⊆ left ∪ right then weight base rows relation cut (left ∪ right) else ⊥) ⊓
      (if right ⊆ left ∪ right then weight base rows relation cut (left ∪ right) else ⊥)
    simp only [ite_eq_left Finset.subset_union_left, ite_eq_left Finset.subset_union_right, inf_idem, le_refl]

theorem forcing_nonempty (base : B) (rows : ℕ → bSet B) (relation : bSet B) (cut : Erdos597.One) :
    base ≤ nonemptyValue (V B) (domainName (forcing base rows relation cut) checkLabel) := by
  apply le_iSup_of_le (checkLabel (B := B) (∅ : Finset Vertex))
  have h : base ≤ (forcing base rows relation cut).member ∅ := by
    rw [show (forcing base rows relation cut).member ∅ = weight base rows relation cut ∅ from rfl,
      weight_empty]
  exact h.trans (weight_le_member checkLabel (forcing base rows relation cut).member ∅)

theorem forcing_partialOrder (base : B) (rows : ℕ → bSet B) (relation : bSet B) (cut : Erdos597.One) :
    (⊤ : B) ≤ partialOrderValue (V B) (domainName (forcing base rows relation cut) checkLabel)
      (orderName (forcing base rows relation cut) checkLabel) :=
  partialOrderValue_checkLabels _

end Erdos597Object.BooleanIndependentConditions
