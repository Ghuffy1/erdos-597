import Erdos597Object.BooleanUnboundedRows
import Erdos597Object.BooleanRowSlices
import Erdos597Object.BooleanScheduledGraph

set_option backward.isDefEq.respectTransparency false

/-! Ground-labelled images of an injective ordinal-block map. -/

namespace Erdos597Object.BooleanRedImages

open Erdos597 Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanFiniteGraphs CanonicalDomains BooleanScheduledGraph
open BooleanUnboundedRows

variable {B : Type} [CompleteBooleanAlgebra B]

open Classical in
attribute [local instance] propDecidable

noncomputable def vertexLabel (v : Vertex) : bSet B := squareLabel (vertexEquiv.symm v)

theorem vertexLabel_discrete (u v : Vertex) (hne : u ≠ v) :
    (vertexLabel (B := B) u =ᴮ vertexLabel v) = ⊥ :=
  squareLabel_discrete _ _ (fun h => hne (vertexEquiv.symm.injective h))

theorem vertexLabel_domain : (⊤ : B) ≤ labelDomain vertexLabel =ᴮ squareDomain :=
  BooleanSetRelabeling.weighted_relabel vertexEquiv.symm squareLabel (fun _ => ⊤)

theorem vertexLabel_member (v : Vertex) : (⊤ : B) ≤ vertexLabel v ∈ᴮ squareDomain :=
  weight_le_member squareLabel (fun _ => ⊤) (vertexEquiv.symm v)

theorem element_equal (i j : ScheduledIteration.Labels) :
    (OmegaOneLabels.element (B := B) i =ᴮ OmegaOneLabels.element j) =
      if BooleanColumns.column i = BooleanColumns.column j then ⊤ else ⊥ := by
  classical
  by_cases h : BooleanColumns.column i = BooleanColumns.column j
  · have hij := BooleanColumns.column_injective h
    subst j
    simp only [ite_true]
    exact top_unique bSet.bv_refl
  · rw [ite_eq_right h]
    exact OmegaOneLabels.element_discrete i j (fun hij => h (congrArg BooleanColumns.column hij))

theorem vertex_order_edge (u v : Vertex) :
    edgeValue (V B) squareOrder (vertexLabel u) (vertexLabel v) =
      if RowLt u v then ⊤ else ⊥ := by
  classical
  rw [vertexLabel, vertexLabel,
    show squareOrder = CanonicalRelations.lexOrderName squareLabel from rfl,
    CanonicalRelations.lexOrderName_edge squareLabel squareLabel_discrete]
  change lexLessValue (V B)
    (bSet.pair (OmegaOneLabels.element (BooleanColumns.columnEquiv.symm u.1))
      (OmegaOneLabels.element (BooleanColumns.columnEquiv.symm u.2)))
    (bSet.pair (OmegaOneLabels.element (BooleanColumns.columnEquiv.symm v.1))
      (OmegaOneLabels.element (BooleanColumns.columnEquiv.symm v.2))) = _
  rw [BooleanBlockOrder.lexLess_pair, BooleanColumns.element_member, element_equal,
    BooleanColumns.element_member]
  simp only [BooleanColumns.column, Equiv.apply_symm_apply]
  by_cases hrow : u.1 < v.1 <;> by_cases heq : u.1 = v.1 <;>
    by_cases hcolumn : u.2 < v.2 <;> simp [RowLt, hrow, heq, hcolumn]

theorem vertex_after_row (u v : Vertex) (hrow : v.1 < u.1) :
    edgeValue (V B) squareOrder (vertexLabel u) (vertexLabel v) = ⊥ := by
  classical
  rw [vertex_order_edge]
  have hnot : ¬ RowLt u v := by
    rintro (h | ⟨h, _⟩)
    · exact lt_asymm h hrow
    · exact (ne_of_lt hrow) h.symm
  simp only [hnot, ite_false]

theorem row_lt_of_unbounded_before (context : B) (hne : context ≠ ⊥)
    (row : One) (weight : One → B) (v : Vertex)
    (hunbounded : context ≤ unboundedValue weight)
    (hbefore : ∀ column, context ⊓ weight column ≤
      edgeValue (V B) squareOrder (vertexLabel (row, column)) (vertexLabel v)) : row < v.1 := by
  classical
  by_contra hrow
  have hzero : ∀ column, v.2 < column → context ⊓ weight column = ⊥ := by
    intro column hcolumn
    have hnot : ¬ RowLt (row, column) v := by
      rintro (h | ⟨_, h⟩)
      · exact hrow h
      · exact lt_asymm hcolumn h
    have hedge : edgeValue (V B) squareOrder (vertexLabel (row, column)) (vertexLabel v) = ⊥ := by
      rw [vertex_order_edge]
      simp only [hnot, ite_false]
    exact bot_unique ((hbefore column).trans_eq hedge)
  have htail : context ≤ tailValue weight v.2 := hunbounded.trans (unbounded_le_tail weight v.2)
  have hle : context ≤ ⨆ column : One, ⨆ (_ : v.2 < column), context ⊓ weight column := by
    simpa only [tailValue, inf_iSup_eq] using le_inf le_rfl htail
  have hz : (⨆ column : One, ⨆ (_ : v.2 < column), context ⊓ weight column) = ⊥ := by
    apply bot_unique
    exact iSup_le fun column => iSup_le fun h => (hzero column h).le
  exact hne (bot_unique (hle.trans_eq hz))

noncomputable def imageWeight (values : One → bSet B) (v : Vertex) : B :=
  ⨆ i, values i =ᴮ vertexLabel v

noncomputable def imageName (values : One → bSet B) : bSet B :=
  weightedSet vertexLabel (imageWeight values)

theorem value_mem_image (context : B) (values : One → bSet B) (i : One)
    (hmember : context ≤ values i ∈ᴮ squareDomain) :
    context ≤ values i ∈ᴮ imageName values := by
  have hcovered : context ≤ values i ∈ᴮ labelDomain vertexLabel :=
    bSet.subst_congr_mem_right' (le_top.trans (bSet.bv_symm vertexLabel_domain)) hmember
  change context ≤ values i ∈ᴮ weightedSet vertexLabel (fun _ => ⊤) at hcovered
  rw [member_weightedSet] at hcovered
  simp only [top_inf_eq] at hcovered
  apply (le_inf le_rfl hcovered).trans
  apply lattice.bv_cases_right
  intro v
  apply le_iSup_of_le v
  exact le_inf (le_iSup_of_le i inf_le_right) inf_le_right

theorem image_uncountable (hB : has_dense_omega_closed_subset B) (context : B)
    (values : One → bSet B) (hmembers : ∀ i, context ≤ values i ∈ᴮ squareDomain)
    (hdiscrete : ∀ i j, i ≠ j → context ⊓ (values i =ᴮ values j) = ⊥) :
    context ≤ (injectsIntoValue (V B) (imageName values) bSet.omega)ᶜ := by
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  by_contra hne
  let part := context ⊓ injectsIntoValue (V B) (imageName values) bSet.omega
  have hpart : part ≠ ⊥ := hne
  have hbase : part ≤ context := inf_le_left
  have hseparate : ∀ i j, i ≠ j → part ⊓ part ⊓ (values i =ᴮ values j) = ⊥ := by
    intro i j hij
    exact bot_unique ((le_inf ((inf_le_left.trans inf_le_left).trans hbase)
      inf_le_right).trans_eq (hdiscrete i j hij))
  have hcount : Countable One := BooleanCountableDecision.countable_of_constant_cover hB part hpart
    (ContextualCCC.cover_of_injected_members values (fun _ => part) (imageName values)
      (fun _ => le_rfl) (fun i => hbase.trans (value_mem_image context values i (hmembers i)))
      hseparate inf_le_right)
  exact not_countable hcount

theorem image_pair_transfer (context : B) (left right : One → bSet B)
    (predicate : bSet B → bSet B → B)
    (hleft : ∀ y, bSet.B_ext (fun x => predicate x y))
    (hright : ∀ x, bSet.B_ext (predicate x))
    (hvalues : ∀ i j, context ≤ predicate (left i) (right j)) (u v : Vertex) :
    (context ⊓ imageWeight left u) ⊓ imageWeight right v ≤ predicate (vertexLabel u) (vertexLabel v) := by
  simp only [imageWeight, inf_iSup_eq, iSup_inf_eq]
  apply iSup_le
  intro j
  apply iSup_le
  intro i
  let part := (context ⊓ (left i =ᴮ vertexLabel u)) ⊓ (right j =ᴮ vertexLabel v)
  have hbase : part ≤ context := inf_le_left.trans inf_le_left
  have hu : part ≤ left i =ᴮ vertexLabel u := inf_le_left.trans inf_le_right
  have hv : part ≤ right j =ᴮ vertexLabel v := inf_le_right
  have hfirst : part ≤ predicate (vertexLabel u) (right j) :=
    (le_inf hu (hbase.trans (hvalues i j))).trans (hleft (right j) (left i) (vertexLabel u))
  exact (le_inf hv hfirst).trans (hright (vertexLabel u) (right j) (vertexLabel v))

theorem image_rows_bounded (context : B) (values : One → bSet B) (rowBound : One)
    (hbounded : ∀ i v, rowBound < v.1 → context ⊓ (values i =ᴮ vertexLabel v) = ⊥) :
    ∀ v, rowBound < v.1 → context ⊓ imageWeight values v = ⊥ := by
  intro v hv
  simp only [imageWeight, inf_iSup_eq, hbounded, hv, iSup_bot]

theorem image_unboundedRow_cover (hB : has_dense_omega_closed_subset B) (context : B)
    (values : One → bSet B) (hmembers : ∀ i, context ≤ values i ∈ᴮ squareDomain)
    (hdiscrete : ∀ i j, i ≠ j → context ⊓ (values i =ᴮ values j) = ⊥)
    (rowBound : One)
    (hbounded : ∀ i v, rowBound < v.1 → context ⊓ (values i =ᴮ vertexLabel v) = ⊥) :
    context ≤ ⨆ row : One, unboundedValue (fun column => imageWeight values (row, column)) :=
  unboundedRow_cover hB context vertexLabel vertexLabel_discrete (imageWeight values) rowBound
    (image_rows_bounded context values rowBound hbounded) (image_uncountable hB context values hmembers hdiscrete)

end Erdos597Object.BooleanRedImages
