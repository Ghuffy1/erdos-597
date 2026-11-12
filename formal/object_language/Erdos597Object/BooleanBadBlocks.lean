import Erdos597Object.BooleanGoodBlocks
import Erdos597Object.BooleanReversedCliques
import Erdos597Object.BooleanTupleExtensions

set_option backward.isDefEq.respectTransparency false

/-! Uniformly bad finite blocks produce a weak finite clique in the Boolean model. -/

namespace Erdos597Object.BooleanBadBlocks

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanInfiniteSets BooleanFiniteSelections BooleanTupleExtensions BooleanGoodBlocks
open BooleanWeakFamilies BooleanBadCliques BooleanGoodPairs BooleanUncountableRamsey
open BooleanBadFibres BooleanCountableNames BooleanCountableRectangles BooleanFiniteGraphs
open BooleanGraphNeighborhoods BooleanSymmetricPairs BooleanReversedCliques
open Erdos597.WeakFamilies (intervalIndex first_interval)

variable {B : Type} [CompleteBooleanAlgebra B]

theorem adjacentBlocks_weight_le (weight : ℕ → B) (n : ℕ) (frame : Fin (n + n) → ℕ)
    (i j : Fin n) (hij : i < j) :
    tupleWeight weight frame ≤ tupleWeight weight (adjacentBlocks (extend frame) i.val j.val) := by
  apply Finset.le_inf
  intro a _
  change tupleWeight weight frame ≤ weight (Erdos597.WeakFamilies.appendTuple
    (fun b : Fin (j.val - i.val) => extend frame (i.val + b.val))
    (fun b : Fin (j.val - i.val) => extend frame (j.val + b.val)) a)
  unfold Erdos597.WeakFamilies.appendTuple
  split_ifs with ha
  · have hbound : i.val + a.val < n + n := by
      have hi := i.isLt
      have hj := j.isLt
      omega
    change tupleWeight weight frame ≤ weight (extend frame (i.val + a.val))
    rw [extend_at frame _ hbound]
    exact tupleWeight_le weight frame ⟨_, hbound⟩
  · have hbound : j.val + (a.val - (j.val - i.val)) < n + n := by
      have hi := i.isLt
      have hj := j.isLt
      have hsize := a.isLt
      omega
    change tupleWeight weight frame ≤ weight (extend frame (j.val + (a.val - (j.val - i.val))))
    rw [extend_at frame _ hbound]
    exact tupleWeight_le weight frame ⟨_, hbound⟩

theorem blueCopy_of_bad_halves_oriented_at (hB : Flypitch.BA_CCC B) (base context : B) (hcontext : context ≤ base) (n : ℕ)
    (ambient relation : bSet B) (domain : ℕ → bSet B) (label : ℕ → Erdos597.One → bSet B)
    (hdiscrete : ∀ r a b, a ≠ b → (label r a =ᴮ label r b) = ⊥)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ BooleanSets.weightedSet (label r) (fun _ => ⊤))
    (hambient : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (hgraph : base ≤ graphValue (V B) ambient relation)
    (hfibres :
      (∀ r s, r < s → ∀ y, base ⊓ (y ∈ᴮ domain s) ≤
        injectsIntoValue (V B) (predecessors (domain r) relation y) bSet.omega) ∨
      (∀ r s, r < s → ∀ x, base ⊓ (x ∈ᴮ domain r) ≤
        injectsIntoValue (V B) (neighborhood (domain s) relation x) bSet.omega))
    (selected : ℕ → B) (hinfinite : context ≤ infiniteValue selected)
    (hbad : ∀ k : ℕ, ∀ hk : 0 < k, k ≤ n → ∀ tuple : Fin (k + k) → ℕ,
      StrictMono tuple → context ⊓ tupleWeight selected tuple ≤
        (goodHalves base domain (fun _ _ => relation) hlarge k hk tuple)ᶜ) :
    context ≤ blueCopyValue (V B) (bSet.ofNat n) ambient
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation := by
  classical
  have hcover := hinfinite.trans (increasing_tuples_cover selected (n + n))
  apply (le_inf le_rfl hcover).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro frame
  by_cases hframe : StrictMono frame
  · simp only [hframe, ↓reduceIte]
    let part := context ⊓ tupleWeight selected frame
    let f := extend frame
    have hf : StrictMono f := extend_strict frame hframe
    let rows : Fin n → bSet B := fun i =>
      sets base domain (fun _ _ => relation) hlarge (intervalIndex f i.val n i.isLt)
    have hrowSubset (i : Fin n) : base ≤ rows i ⊆ᴮ domain (f i.val) := by
      simpa only [rows, first_interval f hf i.val n i.isLt] using
        sets_subset base domain (fun _ _ => relation) hlarge (intervalIndex f i.val n i.isLt)
    have hrowLarge (i : Fin n) : part ≤ (injectsIntoValue (V B) (rows i) bSet.omega)ᶜ :=
      (inf_le_left.trans hcontext).trans (sets_uncountable base domain (fun _ _ => relation) hlarge _)
    have hrowBad (i j : Fin n) (hij : i < j) : part ≤ badPair relation (rows i) (rows j) := by
      have hk : 0 < j.val - i.val := Nat.sub_pos_of_lt hij
      have hkn : j.val - i.val ≤ n := (Nat.sub_le _ _).trans j.isLt.le
      have hnot : part ≤ (goodHalves base domain (fun _ _ => relation) hlarge (j.val - i.val)
          hk (adjacentBlocks f i.val j.val))ᶜ :=
        (le_inf inf_le_left (inf_le_right.trans (adjacentBlocks_weight_le selected n frame i j hij))).trans
          (hbad _ hk hkn _ (adjacentBlocks_strict f hf i.val j.val hij))
      exact bad_interval_pair base part (inf_le_left.trans hcontext) domain (fun _ _ => relation) hlarge
        f hf i.val j.val n hij j.isLt hnot
    rcases hfibres with hbackward | hforward
    · have hrowBackward (i j : Fin n) (hij : i < j) (y : bSet B) :
          part ⊓ (y ∈ᴮ rows j) ≤ injectsIntoValue (V B) (predecessors (rows i) relation y) bSet.omega := by
        let piece := part ⊓ (y ∈ᴮ rows j)
        have hy : piece ≤ y ∈ᴮ domain (f j.val) :=
          bSet.mem_of_mem_subset' (((inf_le_left.trans inf_le_left).trans hcontext).trans (hrowSubset j)) inf_le_right
        have hcount : piece ≤ injectsIntoValue (V B) (predecessors (domain (f i.val)) relation y) bSet.omega :=
          (le_inf ((inf_le_left.trans inf_le_left).trans hcontext) hy).trans (hbackward _ _ (hf hij) y)
        exact subset_countable _ _
          (predecessors_mono piece relation (rows i) (domain (f i.val)) y
            (((inf_le_left.trans inf_le_left).trans hcontext).trans (hrowSubset i))) hcount
      exact blueCopy_of_bad_pairs hB part n ambient relation rows (fun i => label (f i.val))
        (fun i => hdiscrete (f i.val))
        (fun i => subset_trans ((inf_le_left.trans hcontext).trans (hrowSubset i)) ((inf_le_left.trans hcontext).trans (hsubset (f i.val))))
        (fun i => subset_trans ((inf_le_left.trans hcontext).trans (hrowSubset i)) ((inf_le_left.trans hcontext).trans (hambient (f i.val))))
        hrowLarge ((inf_le_left.trans hcontext).trans hgraph) hrowBad hrowBackward
    · have hrowForward (i j : Fin n) (hij : i < j) (x : bSet B) :
          part ⊓ (x ∈ᴮ rows i) ≤ injectsIntoValue (V B) (neighborhood (rows j) relation x) bSet.omega := by
        let piece := part ⊓ (x ∈ᴮ rows i)
        have hx : piece ≤ x ∈ᴮ domain (f i.val) :=
          bSet.mem_of_mem_subset' (((inf_le_left.trans inf_le_left).trans hcontext).trans (hrowSubset i)) inf_le_right
        have hcount : piece ≤ injectsIntoValue (V B) (neighborhood (domain (f j.val)) relation x) bSet.omega :=
          (le_inf ((inf_le_left.trans inf_le_left).trans hcontext) hx).trans (hforward _ _ (hf hij) x)
        exact subset_countable _ _
          (neighborhood_mono piece relation (rows j) (domain (f j.val)) x
            (((inf_le_left.trans inf_le_left).trans hcontext).trans (hrowSubset j))) hcount
      exact blueCopy_of_forward_pairs hB part n ambient relation rows (fun i => label (f i.val))
        (fun i => hdiscrete (f i.val))
        (fun i => subset_trans ((inf_le_left.trans hcontext).trans (hrowSubset i)) ((inf_le_left.trans hcontext).trans (hsubset (f i.val))))
        (fun i => subset_trans ((inf_le_left.trans hcontext).trans (hrowSubset i)) ((inf_le_left.trans hcontext).trans (hambient (f i.val))))
        hrowLarge ((inf_le_left.trans hcontext).trans hgraph) hrowBad hrowForward
  · simp only [hframe, ↓reduceIte, inf_bot_eq, bot_le]

theorem blueCopy_of_bad_halves_at (hB : Flypitch.BA_CCC B) (base context : B) (hcontext : context ≤ base) (n : ℕ)
    (ambient relation : bSet B) (domain : ℕ → bSet B) (label : ℕ → Erdos597.One → bSet B)
    (hdiscrete : ∀ r a b, a ≠ b → (label r a =ᴮ label r b) = ⊥)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ BooleanSets.weightedSet (label r) (fun _ => ⊤))
    (hambient : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (hgraph : base ≤ graphValue (V B) ambient relation)
    (hbackward : ∀ r s, r < s → ∀ y, base ⊓ (y ∈ᴮ domain s) ≤
      injectsIntoValue (V B) (predecessors (domain r) relation y) bSet.omega)
    (selected : ℕ → B) (hinfinite : context ≤ infiniteValue selected)
    (hbad : ∀ k : ℕ, ∀ hk : 0 < k, k ≤ n → ∀ tuple : Fin (k + k) → ℕ,
      StrictMono tuple → context ⊓ tupleWeight selected tuple ≤
        (goodHalves base domain (fun _ _ => relation) hlarge k hk tuple)ᶜ) :
    context ≤ blueCopyValue (V B) (bSet.ofNat n) ambient
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation := by
  exact blueCopy_of_bad_halves_oriented_at hB base context hcontext n ambient relation domain label
    hdiscrete hsubset hambient hlarge hgraph (Or.inl hbackward) selected hinfinite hbad

theorem blueCopy_of_forward_halves_at (hB : Flypitch.BA_CCC B) (base context : B) (hcontext : context ≤ base) (n : ℕ)
    (ambient relation : bSet B) (domain : ℕ → bSet B) (label : ℕ → Erdos597.One → bSet B)
    (hdiscrete : ∀ r a b, a ≠ b → (label r a =ᴮ label r b) = ⊥)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ BooleanSets.weightedSet (label r) (fun _ => ⊤))
    (hambient : ∀ r, base ≤ domain r ⊆ᴮ ambient)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (hgraph : base ≤ graphValue (V B) ambient relation)
    (hforward : ∀ r s, r < s → ∀ x, base ⊓ (x ∈ᴮ domain r) ≤
      injectsIntoValue (V B) (neighborhood (domain s) relation x) bSet.omega)
    (selected : ℕ → B) (hinfinite : context ≤ infiniteValue selected)
    (hbad : ∀ k : ℕ, ∀ hk : 0 < k, k ≤ n → ∀ tuple : Fin (k + k) → ℕ,
      StrictMono tuple → context ⊓ tupleWeight selected tuple ≤
        (goodHalves base domain (fun _ _ => relation) hlarge k hk tuple)ᶜ) :
    context ≤ blueCopyValue (V B) (bSet.ofNat n) ambient
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation := by
  exact blueCopy_of_bad_halves_oriented_at hB base context hcontext n ambient relation domain label
    hdiscrete hsubset hambient hlarge hgraph (Or.inr hforward) selected hinfinite hbad

theorem blueCopy_of_bad_halves (hB : Flypitch.BA_CCC B) (context : B) (n : ℕ)
    (ambient relation : bSet B) (domain : ℕ → bSet B) (label : ℕ → Erdos597.One → bSet B)
    (hdiscrete : ∀ r a b, a ≠ b → (label r a =ᴮ label r b) = ⊥)
    (hsubset : ∀ r, context ≤ domain r ⊆ᴮ BooleanSets.weightedSet (label r) (fun _ => ⊤))
    (hambient : ∀ r, context ≤ domain r ⊆ᴮ ambient)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hbackward : ∀ r s, r < s → ∀ y, context ⊓ (y ∈ᴮ domain s) ≤
      injectsIntoValue (V B) (predecessors (domain r) relation y) bSet.omega)
    (selected : ℕ → B) (hinfinite : context ≤ infiniteValue selected)
    (hbad : ∀ k : ℕ, ∀ hk : 0 < k, k ≤ n → ∀ tuple : Fin (k + k) → ℕ,
      StrictMono tuple → context ⊓ tupleWeight selected tuple ≤
        (goodHalves context domain (fun _ _ => relation) hlarge k hk tuple)ᶜ) :
    context ≤ blueCopyValue (V B) (bSet.ofNat n) ambient
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation := by
  exact blueCopy_of_bad_halves_at hB context context le_rfl n ambient relation domain label
    hdiscrete hsubset hambient hlarge hgraph hbackward selected hinfinite hbad

end Erdos597Object.BooleanBadBlocks
