import Erdos597Object.BooleanCliqueCopies
import Erdos597Object.CanonicalDomains

set_option backward.isDefEq.respectTransparency false

/-! Uncountable independent subsets of each canonical omega-one row. -/

namespace Erdos597Object.BooleanIndependentRows

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet Cardinal
open BooleanSets BooleanFiniteGraphs CanonicalDomains BooleanCliqueCopies BooleanLocalGraphs

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def oneLabelsEquiv : Erdos597.One ≃ ScheduledIteration.Labels :=
  Classical.choice (Cardinal.eq.mp (Erdos597.one_card.trans ScheduledIteration.labels_card.symm))

noncomputable def rowLabel (row : ℕ) (i : Erdos597.One) : bSet B :=
  blockLabel (row, oneLabelsEquiv i)

noncomputable def rowDomain (row : ℕ) : bSet B := labelDomain (rowLabel row)

theorem rowLabel_discrete (row : ℕ) (i j : Erdos597.One) (hij : i ≠ j) :
    (rowLabel (B := B) row i =ᴮ rowLabel row j) = ⊥ := by
  apply blockLabel_discrete
  intro h
  exact hij (oneLabelsEquiv.injective (congrArg Prod.snd h))

theorem rowDomain_subset (row : ℕ) : (⊤ : B) ≤ rowDomain row ⊆ᴮ blockDomain := by
  apply bSet.subset_intro
  intro i
  change Erdos597.One at i
  exact le_top.trans (weight_le_member blockLabel (fun _ => ⊤) (row, oneLabelsEquiv i))

theorem rowDomain_uncountable (hB : Flypitch.BA_CCC B) (row : ℕ) :
    (⊤ : B) ≤ (injectsIntoValue (V B) (rowDomain row) bSet.omega)ᶜ := by
  have h := BooleanUncountability.weighted_top_not_countable hB (rowLabel (B := B) row)
    (rowLabel_discrete row)
  change (⊤ : B) ≤ (injectsIntoValue (V B) (weightedSet (rowLabel row) (fun _ => ⊤)) bSet.omega)ᶜ
  rw [h, compl_bot]

theorem independent_row (hB : Flypitch.BA_CCC B) (context : B) (relation : bSet B) (n row : ℕ)
    (hgraph : context ≤ graphValue (V B) blockDomain relation)
    (hnoClique : context ≤ (blueCopyValue (V B) (bSet.ofNat n) blockDomain
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation)ᶜ) :
    ∃ independent : bSet B, context ≤ independent ⊆ᴮ rowDomain row ∧
      context ≤ (injectsIntoValue (V B) independent bSet.omega)ᶜ ∧
      context ≤ independentValue independent relation :=
  uncountable_independent_of_no_blueClique hB context (rowLabel row) (rowLabel_discrete row)
    (rowDomain row) blockDomain relation n bSet.subset_self
    (le_top.trans (rowDomain_subset row)) (le_top.trans (rowDomain_uncountable hB row)) hgraph hnoClique

theorem independent_row_family (hB : Flypitch.BA_CCC B) (context : B) (relation : bSet B) (n : ℕ)
    (hgraph : context ≤ graphValue (V B) blockDomain relation)
    (hnoClique : context ≤ (blueCopyValue (V B) (bSet.ofNat n) blockDomain
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation)ᶜ) :
    ∃ family : ℕ → bSet B, ∀ row, context ≤ family row ⊆ᴮ rowDomain row ∧
      context ≤ (injectsIntoValue (V B) (family row) bSet.omega)ᶜ ∧
      context ≤ independentValue (family row) relation := by
  exact ⟨fun row => Classical.choose (independent_row hB context relation n row hgraph hnoClique),
    fun row => Classical.choose_spec (independent_row hB context relation n row hgraph hnoClique)⟩

end Erdos597Object.BooleanIndependentRows
