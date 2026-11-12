import Erdos597Object.BooleanIndependentLimits
import Erdos597Object.BooleanCountableAvoidance

set_option backward.isDefEq.respectTransparency false

/-! Dense row requirements make the directed limit uncountable in every row. -/

namespace Erdos597Object.BooleanIndependentDensity

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanIndependentConditions BooleanIndependentFilters BooleanIndependentLimits
open BooleanColumns BooleanCountableAvoidance CanonicalDomains BooleanIteration
open BooleanRowValues BooleanGoodPairs BooleanRowOrder BooleanLocalGraphs BooleanUncountableRamsey

variable {B : Type} [CompleteBooleanAlgebra B]

theorem limitRow_uncountable (hB : Flypitch.BA_CCC B) (base : B)
    (rows : ℕ → bSet B) (relation : bSet B) (cut : Erdos597.One)
    (value : Finset Vertex → B) (row : ℕ)
    (hmeets : ∀ bound : Erdos597.One, base ≤
      ⨆ p, value p ⊓ denseWeight base rows relation cut (row, bound) p) :
    base ≤ (injectsIntoValue (V B) (limitRow value row) bSet.omega)ᶜ := by
  classical
  let part := base ⊓ injectsIntoValue (V B) (limitRow value row) bSet.omega
  let possible : Set (ℕ × ScheduledIteration.Labels) :=
    {key | part ⊓ (blockLabel key ∈ᴮ limitRow value row) ≠ ⊥}
  have hpossible : possible.Countable :=
    possible_members_countable hB part blockLabel
      (fun i j hij => by rw [blockLabel_discrete i j hij, inf_bot_eq])
      (limitRow value row) inf_le_right
  let : Countable possible := hpossible.to_subtype
  obtain ⟨bound, hbound⟩ := Erdos597.countable_family_bounded
    (fun key : possible => column key.val.2)
  have hzero (p : Finset Vertex) :
      part ⊓ (value p ⊓ denseWeight base rows relation cut (row, bound) p) ≤ ⊥ := by
    by_cases hexists : ∃ v ∈ p, v.1 = row ∧ bound < column v.2.2
    · obtain ⟨v, hv, hrow, hcol⟩ := hexists
      have hpoint : value p ≤ blockLabel v.2 ∈ᴮ limitRow value row := by
        rw [limitRow_member, show (row, v.2) = v from Prod.ext hrow.symm rfl]
        exact pointWeight_of_member value p v hv
      have hempty : part ⊓ value p = ⊥ := by
        by_contra hnonzero
        have hkey : v.2 ∈ possible := by
          intro hz
          exact hnonzero (bot_unique ((le_inf inf_le_left (inf_le_right.trans hpoint)).trans_eq hz))
        exact lt_asymm hcol (hbound ⟨v.2, hkey⟩)
      exact ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans_eq hempty).trans bot_le
    · simp only [denseWeight, ite_eq_right hexists, inf_bot_eq, bot_le]
  apply le_compl_iff_disjoint_right.mpr
  rw [disjoint_iff]
  apply bot_unique
  change part ≤ ⊥
  calc
    part = part ⊓ (⨆ p, value p ⊓ denseWeight base rows relation cut (row, bound) p) :=
      (inf_eq_left.mpr (inf_le_left.trans (hmeets bound))).symm
    _ = ⨆ p, part ⊓ (value p ⊓ denseWeight base rows relation cut (row, bound) p) := inf_iSup_eq _ _
    _ ≤ ⊥ := iSup_le hzero

theorem limit_family (hB : Flypitch.BA_CCC B) (base : B) (rows : ℕ → bSet B)
    (relation : bSet B) (cut : Erdos597.One) (value : Finset Vertex → B)
    (hrows : base ≤ rowFamilyValue blockDomain relation blockOrder rows)
    (hindependent : ∀ row, base ≤ independentValue (rows row) relation)
    (hvalid : ∀ p, value p ≤ (forcing base rows relation cut).member p)
    (hdir : ∀ p q, value p ⊓ value q ≤ ⨆ s, value s ⊓
      ((forcing base rows relation cut).leValue s p ⊓ (forcing base rows relation cut).leValue s q))
    (hmeets : ∀ d, base ≤ ⨆ p, value p ⊓ denseWeight base rows relation cut d p) :
    base ≤ rowFamilyValue blockDomain relation blockOrder (limitRow value) ∧
      (∀ row, base ≤ independentValue (limitRow value row) relation) ∧
      (∀ r s, r ≠ s → base ≤ BooleanRectangles.emptyRectangle relation (limitRow value r) (limitRow value s)) := by
  obtain ⟨_hlarge, hsubset, hgood, hordered⟩ :=
    (rowFamilyValue_spec base blockDomain relation blockOrder rows).mp hrows
  have hsub (row : ℕ) : base ≤ limitRow value row ⊆ᴮ rows row :=
    le_top.trans (limitRow_subset base rows relation cut value hvalid row)
  refine ⟨rowFamilyValue_intro base blockDomain relation blockOrder (limitRow value)
    (fun row => limitRow_uncountable hB base rows relation cut value row (fun bound => hmeets (row, bound)))
    (fun row => subset_trans (hsub row) (hsubset row)) ?_ ?_, ?_, ?_⟩
  · intro r s hrs
    exact goodPair_restrict base relation (rows r) (rows s) _ _ (hsub r) (hsub s) (hgood r s hrs)
  · intro r s hrs
    exact allBefore_restrict base blockOrder (rows r) (rows s) _ _ (hsub r) (hsub s) (hordered r s hrs)
  · exact fun row => limitRow_independent base rows relation cut value hvalid hindependent row
  · exact fun r s hrs => le_top.trans (limitRows_empty_rectangle base rows relation cut value hvalid hdir r s hrs)

theorem forcing_refinement (base : ScheduledIteration.finalAlgebra)
    (rows : ℕ → bSet ScheduledIteration.finalAlgebra)
    (relation : bSet ScheduledIteration.finalAlgebra) (cut : Erdos597.One)
    (hrows : base ≤ rowFamilyValue blockDomain relation blockOrder rows)
    (hindependent : ∀ row, base ≤ independentValue (rows row) relation)
    (hccc : BooleanCountableChainCondition (forcing base rows relation cut))
    (hdense : ∀ d p, (forcing base rows relation cut).member p ≤
      ⨆ q, denseWeight base rows relation cut d q ⊓ (forcing base rows relation cut).leValue q p) :
    ∃ refined, base ≤ rowFamilyValue blockDomain relation blockOrder refined ∧
      (∀ row, base ≤ independentValue (refined row) relation) ∧
      (∀ r s, r ≠ s → base ≤ BooleanRectangles.emptyRectangle relation (refined r) (refined s)) := by
  obtain ⟨value, hvalid, _hcover, _hup, hdir, hmeets⟩ :=
    filter_coefficients base rows relation cut hccc hdense
  exact ⟨limitRow value, limit_family ScheduledIteration.finalAlgebra.ccc base rows relation cut value
    hrows hindependent hvalid hdir hmeets⟩

end Erdos597Object.BooleanIndependentDensity
