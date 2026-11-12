import Erdos597Object.BooleanPartsGood
import Erdos597Object.BooleanGoodSupport

set_option backward.isDefEq.respectTransparency false

/-! The original graph supplies both oriented good-block support estimates. -/

namespace Erdos597Object.BooleanOrientedSupport

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet Cardinal
open BooleanSets BooleanFiniteGraphs BooleanSetRelabeling CanonicalDomains
open BooleanOrientedGraphs BooleanOrientedFibres BooleanGoodSupport BooleanRowOrder

variable {B : Type} [CompleteBooleanAlgebra B]

theorem block_labels_card : #(ℕ × ScheduledIteration.Labels) = ℵ₁ := by
  rw [Cardinal.mk_prod]
  simp only [Cardinal.lift_id, Cardinal.mk_nat, ScheduledIteration.labels_card]
  exact Cardinal.aleph0_mul_aleph 1

noncomputable def blockLabelsEquiv : Erdos597.One ≃ ℕ × ScheduledIteration.Labels :=
  Classical.choice (Cardinal.eq.mp (Erdos597.one_card.trans block_labels_card.symm))

noncomputable def allBlockLabel (i : Erdos597.One) : bSet B := blockLabel (blockLabelsEquiv i)

theorem allBlockLabel_discrete (i j : Erdos597.One) (hij : i ≠ j) :
    (allBlockLabel (B := B) i =ᴮ allBlockLabel j) = ⊥ :=
  blockLabel_discrete _ _ (fun h => hij (blockLabelsEquiv.injective h))

theorem allBlockDomain_eq :
    (⊤ : B) ≤ labelDomain allBlockLabel =ᴮ blockDomain :=
  weighted_relabel blockLabelsEquiv blockLabel (fun _ => ⊤)

theorem allBlockDomain_subset (context : B) (domain : bSet B)
    (hsubset : context ≤ domain ⊆ᴮ blockDomain) :
    context ≤ domain ⊆ᴮ labelDomain allBlockLabel :=
  BooleanUncountableRamsey.subset_trans hsubset
    (bSet.subset_of_eq (le_top.trans (bSet.bv_symm allBlockDomain_eq)))

theorem preservesRelation_mono_target (context : B) (source small large mapping : bSet B)
    (hsub : context ≤ small ⊆ᴮ large) :
    context ⊓ preservesRelationValue (V B) source small mapping ≤
      preservesRelationValue (V B) source large mapping := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  apply le_iInf
  intro a
  apply le_iInf
  intro b
  apply lattice.bv_imp_intro
  apply lattice.bv_imp_intro
  let part : B := ((context ⊓ preservesRelationValue (V B) source small mapping) ⊓
    (edgeValue (V B) mapping x a ⊓ edgeValue (V B) mapping y b)) ⊓ edgeValue (V B) source x y
  have hcontext : part ≤ context := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hpoint : part ≤ (edgeValue (V B) mapping x a ⊓ edgeValue (V B) mapping y b)ᶜ ⊔
      ((edgeValue (V B) source x y)ᶜ ⊔ edgeValue (V B) small a b) :=
    (inf_le_left.trans (inf_le_left.trans inf_le_right)).trans
      ((iInf_le _ x).trans ((iInf_le _ y).trans ((iInf_le _ a).trans (iInf_le _ b))))
  have hsmall : part ≤ edgeValue (V B) small a b :=
    lattice.bv_context_apply (lattice.bv_context_apply hpoint (inf_le_left.trans inf_le_right))
      inf_le_right
  exact bSet.mem_of_mem_subset' (hcontext.trans hsub) hsmall

theorem blueCopy_mono_target (context : B) (vertices host edges small large : bSet B)
    (hsub : context ≤ small ⊆ᴮ large) :
    context ⊓ blueCopyValue (V B) vertices host edges small ≤
      blueCopyValue (V B) vertices host edges large := by
  unfold blueCopyValue
  apply lattice.bv_cases_right
  intro mapping
  apply le_iSup_of_le mapping
  apply le_inf (inf_le_right.trans inf_le_left)
  apply le_inf (inf_le_right.trans (inf_le_right.trans inf_le_left))
  exact (le_inf inf_le_left (inf_le_right.trans (inf_le_right.trans inf_le_right))).trans
    (preservesRelation_mono_target context edges small large mapping hsub)

theorem no_blueCopy_of_subset (context : B) (vertices host edges small large : bSet B)
    (hsub : context ≤ small ⊆ᴮ large)
    (hno : context ≤ (blueCopyValue (V B) vertices host edges large)ᶜ) :
    context ≤ (blueCopyValue (V B) vertices host edges small)ᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  rw [disjoint_iff]
  apply bot_unique
  exact (le_inf (blueCopy_mono_target context vertices host edges small large hsub)
    (inf_le_left.trans hno)).trans_eq inf_compl_eq_bot

theorem up_support_of_no_blue (base : ScheduledIteration.finalAlgebra) (n : ℕ)
    (relation : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ blockDomain)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra)
      (domain r) bSet.omega)ᶜ)
    (hordered : ∀ r s, r < s → base ≤ allBefore blockOrder (domain r) (domain s))
    (hgraph : base ≤ graphValue (V ScheduledIteration.finalAlgebra) blockDomain relation)
    (hno : base ≤ (blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n) blockDomain
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation)ᶜ) :
    base ≤ blockSupport base domain (upPart relation) hlarge n := by
  apply support_of_no_blue base n blockDomain (upPart relation) domain (fun _ => allBlockLabel)
    (fun _ => allBlockLabel_discrete) (fun r => allBlockDomain_subset base (domain r) (hsubset r))
    hsubset hlarge (upPart_graph base relation hgraph)
  · intro r s hrs name
    exact up_predecessors_countable base relation (domain r) (domain s)
      (hsubset r) (hsubset s) (hordered r s hrs) name
  · exact no_blueCopy_of_subset base _ _ _ _ relation
      (le_top.trans (upPart_subset relation)) hno

theorem down_support_of_no_blue (base : ScheduledIteration.finalAlgebra) (n : ℕ)
    (relation : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ blockDomain)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra)
      (domain r) bSet.omega)ᶜ)
    (hordered : ∀ r s, r < s → base ≤ allBefore blockOrder (domain r) (domain s))
    (hgraph : base ≤ graphValue (V ScheduledIteration.finalAlgebra) blockDomain relation)
    (hno : base ≤ (blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n) blockDomain
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation)ᶜ) :
    base ≤ blockSupport base domain (downPart relation) hlarge n := by
  apply support_of_no_blue_forward base n blockDomain (downPart relation) domain (fun _ => allBlockLabel)
    (fun _ => allBlockLabel_discrete) (fun r => allBlockDomain_subset base (domain r) (hsubset r))
    hsubset hlarge (downPart_graph base relation hgraph)
  · intro r s hrs name
    exact down_neighborhood_countable base relation (domain r) (domain s)
      (hsubset r) (hsubset s) (hordered r s hrs) name
  · exact no_blueCopy_of_subset base _ _ _ _ relation
      (le_top.trans (downPart_subset relation)) hno

end Erdos597Object.BooleanOrientedSupport
