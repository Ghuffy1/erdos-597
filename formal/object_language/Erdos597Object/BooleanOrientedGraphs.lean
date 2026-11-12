import Erdos597Object.BooleanBlockOrder
import Erdos597Object.BooleanMaskedGraphs

set_option backward.isDefEq.respectTransparency false

/-! Upward and downward subgraphs in the actual canonical block order. -/

namespace Erdos597Object.BooleanOrientedGraphs

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open CanonicalDomains BooleanColumns BooleanBlockOrder BooleanMaskedGraphs

variable {B : Type} [CompleteBooleanAlgebra B]

def upMask (i j : ℕ × ScheduledIteration.Labels) : Prop :=
  (keyLess i j ∧ column i.2 < column j.2) ∨
    (keyLess j i ∧ column j.2 < column i.2)

def downMask (i j : ℕ × ScheduledIteration.Labels) : Prop := ¬ upMask i j

theorem upMask_symmetric (i j : ℕ × ScheduledIteration.Labels) :
    upMask i j ↔ upMask j i := or_comm

theorem downMask_symmetric (i j : ℕ × ScheduledIteration.Labels) :
    downMask i j ↔ downMask j i := not_congr (upMask_symmetric i j)

theorem upMask_forward {i j : ℕ × ScheduledIteration.Labels} (h : keyLess i j) :
    upMask i j ↔ column i.2 < column j.2 := by
  constructor
  · rintro (⟨_, hcol⟩ | ⟨hreverse, _⟩)
    · exact hcol
    · exact False.elim (keyLess_asymm h hreverse)
  · exact fun hcol => Or.inl ⟨h, hcol⟩

noncomputable def upPart (relation : bSet B) : bSet B :=
  maskedName blockLabel relation upMask

noncomputable def downPart (relation : bSet B) : bSet B :=
  maskedName blockLabel relation downMask

theorem upPart_subset (relation : bSet B) : (⊤ : B) ≤ upPart relation ⊆ᴮ relation :=
  masked_subset blockLabel relation upMask

theorem downPart_subset (relation : bSet B) : (⊤ : B) ≤ downPart relation ⊆ᴮ relation :=
  masked_subset blockLabel relation downMask

theorem upPart_graph (context : B) (relation : bSet B)
    (hgraph : context ≤ graphValue (V B) blockDomain relation) :
    context ≤ graphValue (V B) blockDomain (upPart relation) :=
  masked_graph context blockLabel blockLabel_discrete relation hgraph upMask upMask_symmetric

theorem downPart_graph (context : B) (relation : bSet B)
    (hgraph : context ≤ graphValue (V B) blockDomain relation) :
    context ≤ graphValue (V B) blockDomain (downPart relation) :=
  masked_graph context blockLabel blockLabel_discrete relation hgraph downMask downMask_symmetric

theorem parts_cover_labels (relation : bSet B) (i j : ℕ × ScheduledIteration.Labels) :
    edgeValue (V B) (upPart relation) (blockLabel i) (blockLabel j) ⊔
      edgeValue (V B) (downPart relation) (blockLabel i) (blockLabel j) =
        edgeValue (V B) relation (blockLabel i) (blockLabel j) :=
  complementary_edges blockLabel blockLabel_discrete relation upMask i j

theorem up_ordered_edge_bot (relation : bSet B) (i j : ℕ × ScheduledIteration.Labels)
    (hcol : ¬ column i.2 ≤ column j.2) :
    edgeValue (V B) blockOrder (blockLabel i) (blockLabel j) ⊓
      edgeValue (V B) (upPart relation) (blockLabel i) (blockLabel j) = ⊥ := by
  classical
  rw [blockOrder_edge, show upPart relation = maskedName blockLabel relation upMask from rfl,
    masked_edge blockLabel blockLabel_discrete]
  by_cases horder : keyLess i j
  · have hmask : ¬ upMask i j := fun h => hcol (le_of_lt ((upMask_forward horder).mp h))
    simp only [ite_eq_left horder, ite_eq_right hmask, inf_bot_eq]
  · simp only [ite_eq_right horder, bot_inf_eq]

theorem down_ordered_edge_bot (relation : bSet B) (i j : ℕ × ScheduledIteration.Labels)
    (hcol : ¬ column j.2 ≤ column i.2) :
    edgeValue (V B) blockOrder (blockLabel i) (blockLabel j) ⊓
      edgeValue (V B) (downPart relation) (blockLabel i) (blockLabel j) = ⊥ := by
  classical
  rw [blockOrder_edge, show downPart relation = maskedName blockLabel relation downMask from rfl,
    masked_edge blockLabel blockLabel_discrete]
  by_cases horder : keyLess i j
  · have hmask : ¬ downMask i j :=
      fun h => h ((upMask_forward horder).mpr (lt_of_not_ge hcol))
    simp only [ite_eq_left horder, ite_eq_right hmask, inf_bot_eq]
  · simp only [ite_eq_right horder, bot_inf_eq]

end Erdos597Object.BooleanOrientedGraphs
