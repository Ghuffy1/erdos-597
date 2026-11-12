import Erdos597Object.BooleanBadFibres
import Erdos597Object.BooleanCountableAvoidance
import Erdos597Object.BooleanCliqueCopies

set_option backward.isDefEq.respectTransparency false

/-! Finite point selections and weak clique copies from pairwise bad rows. -/

namespace Erdos597Object.BooleanBadCliques

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanRectangles BooleanGoodPairs BooleanBadFibres BooleanCountableAvoidance
open BooleanGraphNeighborhoods BooleanCountableRectangles BooleanUncountableRamsey
open BooleanCountableNames BooleanCliqueCopies BooleanFiniteGraphs

variable {B : Type} [CompleteBooleanAlgebra B]

theorem large_neighborhood_of_avoid (context : B) (relation left right name : bSet B)
    (hmember : context ≤ name ∈ᴮ left)
    (havoid : context ≤ (name ∈ᴮ smallFibres relation left right)ᶜ) :
    context ≤ (injectsIntoValue (V B) (neighborhood right relation name) bSet.omega)ᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  rw [disjoint_iff]
  apply bot_unique
  have hsmall : context ⊓ injectsIntoValue (V B) (neighborhood right relation name) bSet.omega ≤
      name ∈ᴮ smallFibres relation left right := by
    rw [member_smallFibres]
    exact le_inf (inf_le_left.trans hmember) inf_le_right
  exact (le_inf hsmall (inf_le_left.trans havoid)).trans_eq inf_compl_eq_bot

theorem select (hB : Flypitch.BA_CCC B) :
    ∀ (n : ℕ) (context : B) (relation : Fin n → Fin n → bSet B)
      (domain : Fin n → bSet B) (label : Fin n → Erdos597.One → bSet B),
      (∀ i a b, a ≠ b → (label i a =ᴮ label i b) = ⊥) →
      (∀ i, context ≤ domain i ⊆ᴮ weightedSet (label i) (fun _ => ⊤)) →
      (∀ i, context ≤ (injectsIntoValue (V B) (domain i) bSet.omega)ᶜ) →
      (∀ i j, i < j → context ≤ badPair (relation i j) (domain i) (domain j)) →
      (∀ i j, i < j → ∀ y, context ⊓ (y ∈ᴮ domain j) ≤
        injectsIntoValue (V B) (predecessors (domain i) (relation i j) y) bSet.omega) →
      ∃ names : Fin n → bSet B, (∀ i, context ≤ names i ∈ᴮ domain i) ∧
        ∀ i j, i < j → context ≤ edgeValue (V B) (relation i j) (names i) (names j) := by
  intro n
  induction n with
  | zero =>
    intro context relation domain label hdiscrete hsubset hlarge hbad hbackward
    exact ⟨Fin.elim0, (fun i => i.elim0), (fun i => i.elim0)⟩
  | succ n ih =>
    intro context relation domain label hdiscrete hsubset hlarge hbad hbackward
    let excluded : Fin n → bSet B := fun j => smallFibres (relation 0 j.succ) (domain 0) (domain j.succ)
    have hcountable (j : Fin n) : context ≤ injectsIntoValue (V B) (excluded j) bSet.omega :=
      countable_smallFibres hB context (relation 0 j.succ) (domain 0) (domain j.succ)
        (label 0) (label j.succ) (hdiscrete 0) (hdiscrete j.succ) (hsubset 0) (hsubset j.succ)
        (hlarge j.succ) (hbad 0 j.succ (Nat.zero_lt_succ j.val))
        (hbackward 0 j.succ (Nat.zero_lt_succ j.val))
    obtain ⟨first, hfirst, havoid⟩ := exists_avoiding_family hB context (domain 0) (label 0)
      (hdiscrete 0) (hsubset 0) (hlarge 0) excluded hcountable
    let nextDomain : Fin n → bSet B := fun j => neighborhood (domain j.succ) (relation 0 j.succ) first
    have hnextLarge (j : Fin n) :
        context ≤ (injectsIntoValue (V B) (nextDomain j) bSet.omega)ᶜ :=
      large_neighborhood_of_avoid context (relation 0 j.succ) (domain 0) (domain j.succ) first
        hfirst (havoid j)
    have hnextSubset (j : Fin n) :
        context ≤ nextDomain j ⊆ᴮ weightedSet (label j.succ) (fun _ => ⊤) :=
      subset_trans (le_top.trans (neighborhood_subset (domain j.succ) (relation 0 j.succ) first))
        (hsubset j.succ)
    have hnextBad (i j : Fin n) (hij : i < j) :
        context ≤ badPair (relation i.succ j.succ) (nextDomain i) (nextDomain j) :=
      badPair_restrict context (relation i.succ j.succ) (domain i.succ) (domain j.succ)
        (nextDomain i) (nextDomain j)
        (le_top.trans (neighborhood_subset (domain i.succ) (relation 0 i.succ) first))
        (le_top.trans (neighborhood_subset (domain j.succ) (relation 0 j.succ) first))
        (hbad i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij))
    have hnextBackward (i j : Fin n) (hij : i < j) (y : bSet B) :
        context ⊓ (y ∈ᴮ nextDomain j) ≤
          injectsIntoValue (V B) (predecessors (nextDomain i) (relation i.succ j.succ) y) bSet.omega := by
      let part := context ⊓ (y ∈ᴮ nextDomain j)
      have hy : part ≤ y ∈ᴮ domain j.succ :=
        bSet.mem_of_mem_subset'
          (le_top.trans (neighborhood_subset (domain j.succ) (relation 0 j.succ) first)) inf_le_right
      have hcount : part ≤ injectsIntoValue (V B)
          (predecessors (domain i.succ) (relation i.succ j.succ) y) bSet.omega :=
        (le_inf inf_le_left hy).trans (hbackward i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij) y)
      exact subset_countable _ _
        (predecessors_mono part (relation i.succ j.succ) (nextDomain i) (domain i.succ) y
          (le_top.trans (neighborhood_subset (domain i.succ) (relation 0 i.succ) first))) hcount
    obtain ⟨later, hlater, hlaterEdges⟩ := ih context (fun i j => relation i.succ j.succ) nextDomain
      (fun j => label j.succ) (fun j => hdiscrete j.succ) hnextSubset hnextLarge hnextBad hnextBackward
    refine ⟨Fin.cases first later, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact hfirst
      | succ i =>
        have hi := hlater i
        rw [member_neighborhood] at hi
        exact hi.trans inf_le_left
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact False.elim ((lt_irrefl _) hij)
        | succ j =>
          have hj := hlater j
          rw [member_neighborhood] at hj
          exact hj.trans inf_le_right
      | succ i =>
        cases j using Fin.cases with
        | zero => exact False.elim (Fin.not_lt_zero _ hij)
        | succ j => exact hlaterEdges i j (Fin.succ_lt_succ_iff.mp hij)

theorem cliqueMap_of_bad_pairs (hB : Flypitch.BA_CCC B) (context : B) (n : ℕ)
    (ambient relation : bSet B) (domain : Fin n → bSet B) (label : Fin n → Erdos597.One → bSet B)
    (hdiscrete : ∀ i a b, a ≠ b → (label i a =ᴮ label i b) = ⊥)
    (hsubset : ∀ i, context ≤ domain i ⊆ᴮ weightedSet (label i) (fun _ => ⊤))
    (hambient : ∀ i, context ≤ domain i ⊆ᴮ ambient)
    (hlarge : ∀ i, context ≤ (injectsIntoValue (V B) (domain i) bSet.omega)ᶜ)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hbad : ∀ i j, i < j → context ≤ badPair relation (domain i) (domain j))
    (hbackward : ∀ i j, i < j → ∀ y, context ⊓ (y ∈ᴮ domain j) ≤
      injectsIntoValue (V B) (predecessors (domain i) relation y) bSet.omega) :
    context ≤ cliqueMapValue ambient relation n := by
  obtain ⟨names, hmembers, hedges⟩ := select hB n context (fun _ _ => relation) domain label
    hdiscrete hsubset hlarge hbad hbackward
  have hnames (i : Fin n) : context ≤ names i ∈ᴮ ambient :=
    bSet.mem_of_mem_subset' (hambient i) (hmembers i)
  apply le_iSup_of_le names
  apply le_inf (le_iInf hnames)
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hedges i j hij
  · exact (le_inf le_rfl (hedges j i hji)).trans
      (graph_symmetry context ambient relation (names j) (names i) hgraph (hnames j) (hnames i))

theorem blueCopy_of_bad_pairs (hB : Flypitch.BA_CCC B) (context : B) (n : ℕ)
    (ambient relation : bSet B) (domain : Fin n → bSet B) (label : Fin n → Erdos597.One → bSet B)
    (hdiscrete : ∀ i a b, a ≠ b → (label i a =ᴮ label i b) = ⊥)
    (hsubset : ∀ i, context ≤ domain i ⊆ᴮ weightedSet (label i) (fun _ => ⊤))
    (hambient : ∀ i, context ≤ domain i ⊆ᴮ ambient)
    (hlarge : ∀ i, context ≤ (injectsIntoValue (V B) (domain i) bSet.omega)ᶜ)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hbad : ∀ i j, i < j → context ≤ badPair relation (domain i) (domain j))
    (hbackward : ∀ i j, i < j → ∀ y, context ⊓ (y ∈ᴮ domain j) ≤
      injectsIntoValue (V B) (predecessors (domain i) relation y) bSet.omega) :
    context ≤ blueCopyValue (V B) (bSet.ofNat n) ambient
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation :=
  (le_inf le_rfl (cliqueMap_of_bad_pairs hB context n ambient relation domain label hdiscrete
    hsubset hambient hlarge hgraph hbad hbackward)).trans
    (cliqueMap_to_blueCopy context ambient ambient relation n bSet.subset_self hgraph)

end Erdos597Object.BooleanBadCliques
