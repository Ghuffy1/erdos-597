import Erdos597Object.BooleanGraphNeighborhoods

set_option backward.isDefEq.respectTransparency false

/-! The uncountable independent-set or finite-clique dichotomy in CCC models. -/

namespace Erdos597Object.BooleanUncountableRamsey

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanLocalGraphs BooleanGraphNeighborhoods

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def independentSubsetValue (domain relation : bSet B) : B :=
  ⨆ subset : bSet B, (subset ⊆ᴮ domain) ⊓
    ((injectsIntoValue (V B) subset bSet.omega)ᶜ ⊓ independentValue subset relation)

noncomputable def cliqueMapValue (domain relation : bSet B) (n : ℕ) : B :=
  ⨆ names : Fin n → bSet B, (⨅ i, names i ∈ᴮ domain) ⊓
    (⨅ i, ⨅ j, ⨅ (_ : i ≠ j), edgeValue (V B) relation (names i) (names j))

theorem subset_trans {context : B} {small middle large : bSet B}
    (hsmall : context ≤ small ⊆ᴮ middle) (hlarge : context ≤ middle ⊆ᴮ large) :
    context ≤ small ⊆ᴮ large := by
  apply bSet.subset_unfold'.mpr
  apply le_iInf
  intro x
  apply lattice.le_imp_iff.mpr
  exact bSet.mem_of_mem_subset' (inf_le_left.trans hlarge)
    (bSet.mem_of_mem_subset' (inf_le_left.trans hsmall) inf_le_right)

theorem independentSubset_mono (context : B) (small large relation : bSet B)
    (hsubset : context ≤ small ⊆ᴮ large) :
    context ⊓ independentSubsetValue small relation ≤ independentSubsetValue large relation := by
  unfold independentSubsetValue
  rw [inf_iSup_eq]
  apply iSup_le
  intro independent
  apply le_iSup_of_le independent
  exact le_inf (subset_trans (inf_le_right.trans inf_le_left) (inf_le_left.trans hsubset))
    (inf_le_right.trans inf_le_right)

theorem cliqueMap_zero (domain relation : bSet B) : ⊤ ≤ cliqueMapValue domain relation 0 := by
  apply le_iSup_of_le (Fin.elim0 : Fin 0 → bSet B)
  apply le_inf
  · apply le_iInf
    intro i
    exact Fin.elim0 i
  · apply le_iInf
    intro i
    exact Fin.elim0 i

theorem cliqueMap_extend (context : B) (ambient domain relation vertex : bSet B) (n : ℕ)
    (hsubset : context ≤ domain ⊆ᴮ ambient)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hvertex : context ≤ vertex ∈ᴮ domain) :
    context ⊓ cliqueMapValue (neighborhood domain relation vertex) relation n ≤
      cliqueMapValue domain relation (n + 1) := by
  unfold cliqueMapValue
  rw [inf_iSup_eq]
  apply iSup_le
  intro names
  let part : B := context ⊓ ((⨅ i, names i ∈ᴮ neighborhood domain relation vertex) ⊓
    (⨅ i, ⨅ j, ⨅ (_ : i ≠ j), edgeValue (V B) relation (names i) (names j)))
  change part ≤ _
  have hmember (i : Fin n) : part ≤ names i ∈ᴮ neighborhood domain relation vertex :=
    (inf_le_right.trans inf_le_left).trans (iInf_le _ i)
  have hdomain (i : Fin n) : part ≤ names i ∈ᴮ domain := by
    have h := hmember i
    rw [member_neighborhood] at h
    exact h.trans inf_le_left
  have hedge (i : Fin n) : part ≤ edgeValue (V B) relation vertex (names i) := by
    have h := hmember i
    rw [member_neighborhood] at h
    exact h.trans inf_le_right
  apply le_iSup_of_le (Fin.cases vertex names)
  apply le_inf
  · apply le_iInf
    intro i
    cases i using Fin.cases with
    | zero => exact inf_le_left.trans hvertex
    | succ i => exact hdomain i
  · apply le_iInf
    intro i
    apply le_iInf
    intro j
    apply le_iInf
    intro hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact False.elim (hij rfl)
      | succ j => exact hedge j
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        have hx : part ≤ vertex ∈ᴮ ambient :=
          bSet.mem_of_mem_subset' (inf_le_left.trans hsubset) (inf_le_left.trans hvertex)
        have hi : part ≤ names i ∈ᴮ ambient :=
          bSet.mem_of_mem_subset' (inf_le_left.trans hsubset) (hdomain i)
        exact (le_inf le_rfl (hedge i)).trans
          (graph_symmetry part ambient relation vertex (names i) (inf_le_left.trans hgraph) hx hi)
      | succ j =>
        exact (inf_le_right.trans inf_le_right).trans
          ((iInf_le _ i).trans ((iInf_le _ j).trans
            (iInf_le _ (fun h => hij (congrArg Fin.succ h)))))

theorem uncountable_independent_or_clique_in_ambient (hB : Flypitch.BA_CCC B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥) (ambient relation : bSet B) :
    ∀ n : ℕ, ∀ (context : B) (domain : bSet B),
      context ≤ domain ⊆ᴮ weightedSet label (fun _ => ⊤) →
      context ≤ domain ⊆ᴮ ambient →
      context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ →
      context ≤ graphValue (V B) ambient relation →
      context ≤ independentSubsetValue domain relation ⊔ cliqueMapValue domain relation n := by
  intro n
  induction n with
  | zero =>
    intro context domain _ _ _ _
    exact le_top.trans ((cliqueMap_zero domain relation).trans le_sup_right)
  | succ n ih =>
    intro context domain hsubset hambientSubset hlarge hgraph
    let high : B := ⨆ x : bSet B, (x ∈ᴮ domain) ⊓
      (injectsIntoValue (V B) (neighborhood domain relation x) bSet.omega)ᶜ
    have hhigh : context ⊓ high ≤
        independentSubsetValue domain relation ⊔ cliqueMapValue domain relation (n + 1) := by
      change context ⊓ (⨆ x : bSet B, (x ∈ᴮ domain) ⊓
        (injectsIntoValue (V B) (neighborhood domain relation x) bSet.omega)ᶜ) ≤ _
      rw [inf_iSup_eq]
      apply iSup_le
      intro x
      let part : B := context ⊓ ((x ∈ᴮ domain) ⊓
        (injectsIntoValue (V B) (neighborhood domain relation x) bSet.omega)ᶜ)
      have hneighborSubset : part ≤ neighborhood domain relation x ⊆ᴮ domain :=
        le_top.trans (neighborhood_subset domain relation x)
      have hpartSubset := subset_trans hneighborSubset (inf_le_left.trans hsubset)
      have hpartAmbient := subset_trans hneighborSubset (inf_le_left.trans hambientSubset)
      have hcase := ih part (neighborhood domain relation x) hpartSubset hpartAmbient
        (inf_le_right.trans inf_le_right) (inf_le_left.trans hgraph)
      apply lattice.context_or_elim' hcase
      · intro smaller hsmaller hindependent
        exact ((le_inf hsmaller hindependent).trans
          (independentSubset_mono part _ _ relation hneighborSubset)).trans le_sup_left
      · intro smaller hsmaller hclique
        exact ((le_inf hsmaller hclique).trans
          (cliqueMap_extend part _ domain relation x n (inf_le_left.trans hambientSubset)
            (inf_le_left.trans hgraph) (inf_le_right.trans inf_le_left))).trans le_sup_right
    have hlow : context ⊓ highᶜ ≤
        independentSubsetValue domain relation ⊔ cliqueMapValue domain relation (n + 1) := by
      let part : B := context ⊓ highᶜ
      have hcountable (x : bSet B) (hx : part ≤ x ∈ᴮ domain) :
          part ≤ injectsIntoValue (V B) (neighborhood domain relation x) bSet.omega := by
        have hnot : part ≤ ((x ∈ᴮ domain) ⊓
            (injectsIntoValue (V B) (neighborhood domain relation x) bSet.omega)ᶜ)ᶜ :=
          inf_le_right.trans (compl_le_compl (le_iSup
            (fun y : bSet B => (y ∈ᴮ domain) ⊓
              (injectsIntoValue (V B) (neighborhood domain relation y) bSet.omega)ᶜ) x))
        have himp : part ≤ lattice.imp (x ∈ᴮ domain)
            (injectsIntoValue (V B) (neighborhood domain relation x) bSet.omega) := by
          simpa only [compl_inf, compl_compl, lattice.imp] using hnot
        exact lattice.bv_context_apply himp hx
      obtain ⟨independent, hsub, huncountable, hindependent⟩ :=
        uncountable_independent_subname_in_ambient hB part label hdiscrete domain ambient relation
          (inf_le_left.trans hsubset) (inf_le_left.trans hambientSubset)
          (inf_le_left.trans hlarge) (inf_le_left.trans hgraph) hcountable
      apply le_sup_of_le_left
      apply le_iSup_of_le independent
      exact le_inf hsub (le_inf huncountable hindependent)
    apply lattice.context_or_elim' (a := high) (b := highᶜ)
      (by rw [sup_compl_eq_top]; exact le_top)
    · intro smaller hsmaller hbranch
      exact (le_inf hsmaller hbranch).trans hhigh
    · intro smaller hsmaller hbranch
      exact (le_inf hsmaller hbranch).trans hlow

theorem uncountable_independent_or_clique (hB : Flypitch.BA_CCC B)
    (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥) (relation : bSet B)
    (n : ℕ) (context : B) (domain : bSet B)
    (hsubset : context ≤ domain ⊆ᴮ weightedSet label (fun _ => ⊤))
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ)
    (hgraph : context ≤ graphValue (V B) (weightedSet label (fun _ => ⊤)) relation) :
    context ≤ independentSubsetValue domain relation ⊔ cliqueMapValue domain relation n :=
  uncountable_independent_or_clique_in_ambient hB label hdiscrete
    (weightedSet label (fun _ => ⊤)) relation n context domain hsubset hsubset hlarge hgraph

end Erdos597Object.BooleanUncountableRamsey
