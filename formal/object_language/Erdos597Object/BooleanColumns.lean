import Erdos597Object.BooleanCanonicalRows
import Erdos597Object.BooleanCountableNames

set_option backward.isDefEq.respectTransparency false

/-! Actual ordinal column coordinates and countable bounded-column domains. -/

namespace Erdos597Object.BooleanColumns

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet Ordinal Cardinal
open BooleanSets BooleanFiniteGraphs CanonicalDomains ScheduledIteration
open BooleanCountableNames

noncomputable def columnEquiv : Labels ≃ Erdos597.One :=
  OmegaOneLabels.indexEquiv.trans (Equiv.cast (Ordinal.type_toPSet (ω₁ : Ordinal.{0})))

noncomputable def column (i : Labels) : Erdos597.One := columnEquiv i

theorem column_injective : Function.Injective column := columnEquiv.injective

theorem ordinal_func_eq (o : Ordinal.{0}) : ∀ i : o.toPSet.Type,
    o.toPSet.Func i = ((Equiv.cast (Ordinal.type_toPSet o) i : o.ToType) : Ordinal).toPSet := by
  intro i
  have transport (left right : PSet) (h : left = right) (a : left.Type) :
      left.Func a = right.Func (cast (congrArg PSet.Type h) a) := by
    subst right
    rfl
  exact transport o.toPSet _ (Ordinal.toPSet.eq_1 o) i

variable {B : Type} [CompleteBooleanAlgebra B]

theorem element_eq (i : Labels) :
    OmegaOneLabels.element (B := B) i = bSet.check ((column i : Ordinal).toPSet) := by
  exact congrArg (fun x : PSet => (bSet.check x : bSet B))
    (ordinal_func_eq (ω₁ : Ordinal.{0}) (OmegaOneLabels.indexEquiv i))

theorem element_mem_of_lt {i j : Labels} (h : column i < column j) :
    (⊤ : B) ≤ OmegaOneLabels.element i ∈ᴮ OmegaOneLabels.element j := by
  rw [element_eq, element_eq]
  exact bSet.check_mem (Flypitch.ordinal.mk_mem_mk_of_lt h)

theorem element_mem_of_not_lt {i j : Labels} (h : ¬ column i < column j) :
    (OmegaOneLabels.element (B := B) i ∈ᴮ OmegaOneLabels.element j) = ⊥ := by
  rw [element_eq, element_eq]
  apply bSet.check_bv_mem_bot_of_not_mem
  intro hmem
  exact h (Flypitch.ordinal.lt_of_mk_mem hmem)

theorem element_member (i j : Labels) :
    (OmegaOneLabels.element (B := B) i ∈ᴮ OmegaOneLabels.element j) =
      if column i < column j then ⊤ else ⊥ := by
  classical
  by_cases h : column i < column j
  · rw [ite_eq_left h]
    exact top_unique (element_mem_of_lt h)
  · rw [ite_eq_right h]
    exact element_mem_of_not_lt h

def BoundedIndices (bound : Erdos597.One) :=
  {ij : ℕ × Labels // column ij.2 ≤ bound}

theorem bounded_indices_countable (bound : Erdos597.One) : Countable (BoundedIndices bound) := by
  have : Countable (Set.Iic bound) := (Erdos597.countable_initial_segment bound).to_subtype
  let encode : BoundedIndices bound → ℕ × Set.Iic bound :=
    fun ij => (ij.val.1, ⟨column ij.val.2, ij.property⟩)
  apply Function.Injective.countable (f := encode)
  intro left right h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun x : ℕ × Set.Iic bound => x.1) h
  · apply column_injective
    exact congrArg (fun x : ℕ × Set.Iic bound => x.2.val) h

noncomputable def boundedDomain (bound : Erdos597.One) : bSet B :=
  weightedSet (fun ij : BoundedIndices bound => blockLabel ij.val) (fun _ => ⊤)

theorem boundedDomain_countable (bound : Erdos597.One) :
    (⊤ : B) ≤ injectsIntoValue (V B) (boundedDomain bound) bSet.omega := by
  have := bounded_indices_countable bound
  apply weighted_countable
  intro i j hij
  exact blockLabel_discrete _ _ (fun h => hij (Subtype.ext h))

theorem boundedDomain_subset (bound : Erdos597.One) :
    (⊤ : B) ≤ boundedDomain bound ⊆ᴮ blockDomain := by
  apply bSet.subset_intro
  intro ij
  exact le_top.trans (weight_le_member blockLabel (fun _ => ⊤) ij.val)

theorem boundedDomain_member (bound : Erdos597.One) (row : ℕ) (i : Labels)
    (hi : column i ≤ bound) :
    (⊤ : B) ≤ blockLabel (row, i) ∈ᴮ boundedDomain bound :=
  weight_le_member (fun ij : BoundedIndices bound => blockLabel ij.val) (fun _ => ⊤)
    ⟨(row, i), hi⟩

theorem subset_bounded_of_label_members (context : B) (small : bSet B)
    (bound : Erdos597.One) (hsubset : context ≤ small ⊆ᴮ blockDomain)
    (hbound : ∀ i : ℕ × Labels, ¬ column i.2 ≤ bound →
      context ⊓ (blockLabel i ∈ᴮ small) ≤ ⊥) :
    context ≤ small ⊆ᴮ boundedDomain bound := by
  apply bSet.subset_unfold'.mpr
  apply le_iInf
  intro x
  apply lattice.bv_imp_intro
  let part : B := context ⊓ (x ∈ᴮ small)
  have hmember : part ≤ x ∈ᴮ blockDomain :=
    bSet.mem_of_mem_subset' (inf_le_left.trans hsubset) inf_le_right
  change part ≤ x ∈ᴮ weightedSet blockLabel (fun _ => ⊤) at hmember
  rw [member_weightedSet] at hmember
  simp only [top_inf_eq] at hmember
  apply (le_inf le_rfl hmember).trans
  apply lattice.bv_cases_right
  intro i
  by_cases hi : column i.2 ≤ bound
  · exact bSet.subst_congr_mem_left' (bSet.bv_symm inf_le_right)
      (le_top.trans (boundedDomain_member bound i.1 i.2 hi))
  · have hsmall : part ⊓ (x =ᴮ blockLabel i) ≤ blockLabel i ∈ᴮ small :=
      bSet.subst_congr_mem_left' inf_le_right (inf_le_left.trans inf_le_right)
    exact ((le_inf (inf_le_left.trans inf_le_left) hsmall).trans (hbound i hi)).trans bot_le

theorem countable_of_label_members (context : B) (small : bSet B)
    (bound : Erdos597.One) (hsubset : context ≤ small ⊆ᴮ blockDomain)
    (hbound : ∀ i : ℕ × Labels, ¬ column i.2 ≤ bound →
      context ⊓ (blockLabel i ∈ᴮ small) ≤ ⊥) :
    context ≤ injectsIntoValue (V B) small bSet.omega :=
  subset_countable small (boundedDomain bound)
    (subset_bounded_of_label_members context small bound hsubset hbound)
    (le_top.trans (boundedDomain_countable bound))

end Erdos597Object.BooleanColumns
