import Erdos597Object.BooleanInjections

set_option backward.isDefEq.respectTransparency false

/-! Separate a well-ordered family of names by assigning each equality class its first available weight. -/

namespace Erdos597Object.SeparatedNames

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets

variable {B I : Type} [CompleteBooleanAlgebra B]

noncomputable def priorEquality (element : I → bSet B) (i : I) : B :=
  ⨆ j : {j : I // WellOrderingRel j i}, element i =ᴮ element j.1

noncomputable def weight (context : B) (element : I → bSet B) (i : I) : B :=
  context ⊓ (priorEquality element i)ᶜ

theorem weight_le_context (context : B) (element : I → bSet B) (i : I) :
    weight context element i ≤ context := inf_le_left

theorem weight_avoids_prior (context : B) (element : I → bSet B)
    (i j : I) (hij : WellOrderingRel i j) :
    weight context element j ≤ (element j =ᴮ element i)ᶜ :=
  inf_le_right.trans (compl_le_compl (le_iSup (fun k : {k : I // WellOrderingRel k j} =>
    element j =ᴮ element k.1) ⟨i, hij⟩))

theorem weights_separated (context : B) (element : I → bSet B) :
    ∀ i j, i ≠ j → weight context element i ⊓ weight context element j ⊓ (element i =ᴮ element j) = ⊥ := by
  intro i j hne
  rcases trichotomous_of WellOrderingRel i j with hij | heq | hji
  · have hforward : weight context element i ⊓ weight context element j ⊓ (element i =ᴮ element j) ≤
        element j =ᴮ element i := bSet.bv_symm inf_le_right
    have hnegative : weight context element i ⊓ weight context element j ⊓ (element i =ᴮ element j) ≤
        (element j =ᴮ element i)ᶜ :=
      (inf_le_left.trans inf_le_right).trans (weight_avoids_prior context element i j hij)
    exact bot_unique ((le_inf hforward hnegative).trans (by simp))
  · exact (hne heq).elim
  · have hnegative : weight context element i ⊓ weight context element j ⊓ (element i =ᴮ element j) ≤
        (element i =ᴮ element j)ᶜ :=
      (inf_le_left.trans inf_le_left).trans (weight_avoids_prior context element j i hji)
    exact bot_unique ((le_inf inf_le_right hnegative).trans (by simp))

theorem weight_cover_each (context : B) (element : I → bSet B) (i : I) :
    context ≤ element i ∈ᴮ weightedSet element (weight context element) := by
  refine WellFounded.induction WellOrderingRel.isWellOrder.wf
    (C := fun i => context ≤ element i ∈ᴮ weightedSet element (weight context element)) i ?_
  intro j ih
  have hprior : context ⊓ priorEquality element j ≤
      element j ∈ᴮ weightedSet element (weight context element) := by
    unfold priorEquality
    rw [inf_iSup_eq]
    apply iSup_le
    intro k
    exact (le_inf (bSet.bv_symm inf_le_right) (inf_le_left.trans (ih k.1 k.2))).trans
      (bSet.B_ext_mem_left (weightedSet element (weight context element)) (element k.1) (element j))
  have hself : context ⊓ (priorEquality element j)ᶜ ≤
      element j ∈ᴮ weightedSet element (weight context element) :=
    weight_le_member element (weight context element) j
  calc
    context = context ⊓ (priorEquality element j ⊔ (priorEquality element j)ᶜ) := by simp
    _ = (context ⊓ priorEquality element j) ⊔ (context ⊓ (priorEquality element j)ᶜ) := inf_sup_left _ _ _
    _ ≤ _ := sup_le hprior hself

theorem weights_cover [Nonempty I] (context : B) (element : I → bSet B) :
    (⨆ i, weight context element i) = context := by
  apply le_antisymm (iSup_le (weight_le_context context element))
  let i : I := Classical.ofNonempty
  exact (weight_cover_each context element i).trans
    (iSup_le fun j => (inf_le_left : weight context element j ⊓ (element i =ᴮ element j) ≤ _).trans
      (le_iSup (weight context element) j))

theorem weighted_presentation (context : B) (element : I → bSet B) :
    context ≤ weightedSet element (fun _ => context) =ᴮ weightedSet element (weight context element) := by
  apply bSet.subset_ext
  · apply bSet.subset_intro
    intro i
    exact inf_le_left.trans (weight_cover_each context element i)
  · apply bSet.subset_intro
    intro i
    exact (inf_le_right.trans (weight_le_context context element i)).trans
      (weight_le_member element (fun _ => context) i)

end Erdos597Object.SeparatedNames
