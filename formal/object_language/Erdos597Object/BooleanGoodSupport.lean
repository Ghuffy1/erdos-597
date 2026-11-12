import Erdos597Object.BooleanRamseyAlternatives
import Erdos597Object.BooleanBadBlocks

set_option backward.isDefEq.respectTransparency false

/-! Good homogeneous block support covers the absence of a finite blue clique. -/

namespace Erdos597Object.BooleanGoodSupport

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanInfiniteSets BooleanFiniteSelections BooleanGoodBlocks
open BooleanRamseyAlternatives BooleanBadBlocks BooleanCountableRectangles
open BooleanFiniteGraphs BooleanGraphNeighborhoods

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def blockSupport (base : B) (domain : ℕ → bSet B)
    (relation : bSet B)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (n : ℕ) : B :=
  ⨆ k : ℕ, ⨆ hk : 0 < k, ⨆ (_ : k ≤ n),
    goodSupport (k + k) (goodHalves base domain (fun _ _ => relation) hlarge k hk)

theorem good_or_blue_oriented (base : ScheduledIteration.finalAlgebra) (n : ℕ)
    (ambient relation : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (label : ℕ → Erdos597.One → bSet ScheduledIteration.finalAlgebra)
    (hdiscrete : ∀ r a b, a ≠ b → (label r a =ᴮ label r b) = ⊥)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ BooleanSets.weightedSet (label r) (fun _ => ⊤))
    (hambient : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra)
      (domain r) bSet.omega)ᶜ)
    (hgraph : base ≤ graphValue (V ScheduledIteration.finalAlgebra) ambient relation)
    (hfibres :
      (∀ r s, r < s → ∀ y, base ⊓ (y ∈ᴮ domain s) ≤
        injectsIntoValue (V ScheduledIteration.finalAlgebra) (predecessors (domain r) relation y) bSet.omega) ∨
      (∀ r s, r < s → ∀ x, base ⊓ (x ∈ᴮ domain r) ≤
        injectsIntoValue (V ScheduledIteration.finalAlgebra) (neighborhood (domain s) relation x) bSet.omega)) :
    base ≤ blockSupport base domain relation hlarge n ⊔
      blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n) ambient
        (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation := by
  let support := blockSupport base domain relation hlarge n
  let part := base ⊓ supportᶜ
  let color (k : ℕ) : (Fin ((k + 1) + (k + 1)) → ℕ) → ScheduledIteration.finalAlgebra :=
    goodHalves base domain (fun _ _ => relation) hlarge (k + 1) (Nat.zero_lt_succ k)
  have hinfinite : part ≤ infiniteValue (fun _ : ℕ => (⊤ : ScheduledIteration.finalAlgebra)) := by
    apply le_iInf
    intro bound
    apply le_iSup_of_le bound
    apply le_iSup_of_le (le_refl bound)
    exact le_top
  obtain ⟨selected, _hsub, hselected, hbad⟩ :=
    exists_all_bad part (fun k => (k + 1) + (k + 1)) color n (fun _ => ⊤) hinfinite (by
      intro k hk
      have hsupport : goodSupport ((k + 1) + (k + 1)) (color k) ≤ support := by
        apply le_iSup_of_le (k + 1)
        apply le_iSup_of_le (Nat.zero_lt_succ k)
        apply le_iSup_of_le (Nat.succ_le_iff.mpr hk)
        exact le_rfl
      exact inf_le_right.trans (compl_le_compl hsupport))
  have hblue : part ≤ blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n)
      ambient (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation := by
    apply blueCopy_of_bad_halves_oriented_at ScheduledIteration.finalAlgebra.ccc base part inf_le_left n
      ambient relation domain label hdiscrete hsubset hambient hlarge hgraph hfibres selected hselected
    intro k hk hkn tuple htuple
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    exact hbad j (by omega) tuple htuple
  change base ≤ support ⊔ _
  calc
    base = base ⊓ (support ⊔ supportᶜ) := by simp only [sup_compl_eq_top, inf_top_eq]
    _ = (base ⊓ support) ⊔ part := by simp only [part, inf_sup_left]
    _ ≤ support ⊔ _ := sup_le_sup inf_le_right hblue

theorem good_or_blue (base : ScheduledIteration.finalAlgebra) (n : ℕ)
    (ambient relation : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (label : ℕ → Erdos597.One → bSet ScheduledIteration.finalAlgebra)
    (hdiscrete : ∀ r a b, a ≠ b → (label r a =ᴮ label r b) = ⊥)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ BooleanSets.weightedSet (label r) (fun _ => ⊤))
    (hambient : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra)
      (domain r) bSet.omega)ᶜ)
    (hgraph : base ≤ graphValue (V ScheduledIteration.finalAlgebra) ambient relation)
    (hbackward : ∀ r s, r < s → ∀ y, base ⊓ (y ∈ᴮ domain s) ≤
      injectsIntoValue (V ScheduledIteration.finalAlgebra) (predecessors (domain r) relation y)
        bSet.omega) :
    base ≤ blockSupport base domain relation hlarge n ⊔
      blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n) ambient
        (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation := by
  exact good_or_blue_oriented base n ambient relation domain label hdiscrete hsubset hambient hlarge hgraph
    (Or.inl hbackward)


theorem good_or_blue_forward (base : ScheduledIteration.finalAlgebra) (n : ℕ)
    (ambient relation : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (label : ℕ → Erdos597.One → bSet ScheduledIteration.finalAlgebra)
    (hdiscrete : ∀ r a b, a ≠ b → (label r a =ᴮ label r b) = ⊥)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ BooleanSets.weightedSet (label r) (fun _ => ⊤))
    (hambient : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra)
      (domain r) bSet.omega)ᶜ)
    (hgraph : base ≤ graphValue (V ScheduledIteration.finalAlgebra) ambient relation)
    (hforward : ∀ r s, r < s → ∀ x, base ⊓ (x ∈ᴮ domain r) ≤
      injectsIntoValue (V ScheduledIteration.finalAlgebra) (neighborhood (domain s) relation x)
        bSet.omega) :
    base ≤ blockSupport base domain relation hlarge n ⊔
      blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n) ambient
        (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation := by
  exact good_or_blue_oriented base n ambient relation domain label hdiscrete hsubset hambient hlarge hgraph
    (Or.inr hforward)


theorem support_of_no_blue_oriented (base : ScheduledIteration.finalAlgebra) (n : ℕ)
    (ambient relation : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (label : ℕ → Erdos597.One → bSet ScheduledIteration.finalAlgebra)
    (hdiscrete : ∀ r a b, a ≠ b → (label r a =ᴮ label r b) = ⊥)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ BooleanSets.weightedSet (label r) (fun _ => ⊤))
    (hambient : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra)
      (domain r) bSet.omega)ᶜ)
    (hgraph : base ≤ graphValue (V ScheduledIteration.finalAlgebra) ambient relation)
    (hfibres :
      (∀ r s, r < s → ∀ y, base ⊓ (y ∈ᴮ domain s) ≤
        injectsIntoValue (V ScheduledIteration.finalAlgebra) (predecessors (domain r) relation y) bSet.omega) ∨
      (∀ r s, r < s → ∀ x, base ⊓ (x ∈ᴮ domain r) ≤
        injectsIntoValue (V ScheduledIteration.finalAlgebra) (neighborhood (domain s) relation x) bSet.omega))
    (hnoBlue : base ≤ (blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n)
      ambient (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation)ᶜ) :
    base ≤ blockSupport base domain relation hlarge n := by
  let blue := blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n)
    ambient (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation
  have hcover := good_or_blue_oriented base n ambient relation domain label
    hdiscrete hsubset hambient hlarge hgraph hfibres
  have hempty : base ⊓ blue ≤ (⊥ : ScheduledIteration.finalAlgebra) := by
    have hboth : base ⊓ blue ≤ blue ⊓ blueᶜ :=
      le_inf inf_le_right (inf_le_left.trans hnoBlue)
    simpa only [inf_compl_eq_bot] using hboth
  calc
    base ≤ base ⊓ (blockSupport base domain relation hlarge n ⊔ blue) := le_inf le_rfl hcover
    _ = (base ⊓ blockSupport base domain relation hlarge n) ⊔ (base ⊓ blue) := by
      simp only [inf_sup_left]
    _ ≤ blockSupport base domain relation hlarge n ⊔ ⊥ := sup_le_sup inf_le_right hempty
    _ = blockSupport base domain relation hlarge n := sup_bot_eq _

theorem support_of_no_blue (base : ScheduledIteration.finalAlgebra) (n : ℕ)
    (ambient relation : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (label : ℕ → Erdos597.One → bSet ScheduledIteration.finalAlgebra)
    (hdiscrete : ∀ r a b, a ≠ b → (label r a =ᴮ label r b) = ⊥)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ BooleanSets.weightedSet (label r) (fun _ => ⊤))
    (hambient : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra)
      (domain r) bSet.omega)ᶜ)
    (hgraph : base ≤ graphValue (V ScheduledIteration.finalAlgebra) ambient relation)
    (hbackward : ∀ r s, r < s → ∀ y, base ⊓ (y ∈ᴮ domain s) ≤
      injectsIntoValue (V ScheduledIteration.finalAlgebra) (predecessors (domain r) relation y)
        bSet.omega)
    (hnoBlue : base ≤ (blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n)
      ambient (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation)ᶜ) :
    base ≤ blockSupport base domain relation hlarge n := by
  exact support_of_no_blue_oriented base n ambient relation domain label hdiscrete hsubset hambient hlarge
    hgraph (Or.inl hbackward) hnoBlue


theorem support_of_no_blue_forward (base : ScheduledIteration.finalAlgebra) (n : ℕ)
    (ambient relation : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (label : ℕ → Erdos597.One → bSet ScheduledIteration.finalAlgebra)
    (hdiscrete : ∀ r a b, a ≠ b → (label r a =ᴮ label r b) = ⊥)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ BooleanSets.weightedSet (label r) (fun _ => ⊤))
    (hambient : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra)
      (domain r) bSet.omega)ᶜ)
    (hgraph : base ≤ graphValue (V ScheduledIteration.finalAlgebra) ambient relation)
    (hforward : ∀ r s, r < s → ∀ x, base ⊓ (x ∈ᴮ domain r) ≤
      injectsIntoValue (V ScheduledIteration.finalAlgebra) (neighborhood (domain s) relation x)
        bSet.omega)
    (hnoBlue : base ≤ (blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n)
      ambient (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation)ᶜ) :
    base ≤ blockSupport base domain relation hlarge n := by
  exact support_of_no_blue_oriented base n ambient relation domain label hdiscrete hsubset hambient hlarge
    hgraph (Or.inr hforward) hnoBlue

end Erdos597Object.BooleanGoodSupport
