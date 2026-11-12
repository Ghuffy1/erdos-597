import Erdos597Object.BooleanWeakFamilyContexts
import Erdos597Object.BooleanTupleRamsey

set_option backward.isDefEq.respectTransparency false

/-! Good colours on separated equal-size blocks and their bad-interval consequence. -/

namespace Erdos597Object.BooleanGoodBlocks

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanGoodPairs BooleanWeakFamilies BooleanWeakFamilyContexts BooleanFiniteSelections BooleanInfiniteSets
open Erdos597.WeakFamilies (Index first last singleton priorIndex erasePrior tupleIndex first_tuple
  appendTuple appendTuple_left appendTuple_right appendTuple_strictMono intervalIndex first_interval
  last_interval_succ erase_last_interval shifted_tuple_index)

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def goodHalves (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (k : ℕ) (hk : 0 < k) (tuple : Fin (k + k) → ℕ) : B :=
  let left := tupleIndex hk (fun i => tuple (Fin.castAdd k i))
  let right := tupleIndex hk (fun i => tuple (Fin.natAdd k i))
  goodPair (relation (first left) (first right))
    (sets context domain relation hlarge left) (sets context domain relation hlarge right)

def adjacentBlocks (f : ℕ → ℕ) (i j : ℕ) : Fin ((j - i) + (j - i)) → ℕ :=
  appendTuple (fun a : Fin (j - i) => f (i + a.val)) (fun a : Fin (j - i) => f (j + a.val))

theorem adjacentBlocks_strict (f : ℕ → ℕ) (hf : StrictMono f) (i j : ℕ) (hij : i < j) :
    StrictMono (adjacentBlocks f i j) := by
  apply appendTuple_strictMono
  · intro a b hab
    exact hf (Nat.add_lt_add_left hab i)
  · intro a b hab
    exact hf (Nat.add_lt_add_left hab j)
  · intro a b
    apply hf
    have ha := a.isLt
    omega

theorem bad_interval_pair (context part : B) (hpart : part ≤ context)
    (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (f : ℕ → ℕ) (hf : StrictMono f) (i j n : ℕ) (hij : i < j) (hjn : j < n)
    (hnotGood : part ≤ (goodHalves context domain relation hlarge (j - i)
      (Nat.sub_pos_of_lt hij) (adjacentBlocks f i j))ᶜ) :
    part ≤ badPair (relation (f i) (f j))
      (sets context domain relation hlarge (intervalIndex f i n (hij.trans hjn)))
      (sets context domain relation hlarge (intervalIndex f j n hjn)) := by
  classical
  let k := j - i
  have hk : 0 < k := Nat.sub_pos_of_lt hij
  let left : Fin k → ℕ := fun a => f (i + a.val)
  let right : Fin k → ℕ := fun a => f (j + a.val)
  have hright : StrictMono right := fun a b hab => hf (Nat.add_lt_add_left hab j)
  have htLeft : (fun a : Fin k => adjacentBlocks f i j (Fin.castAdd k a)) = left := by
    funext a
    exact appendTuple_left _ _ a
  have htRight : (fun a : Fin k => adjacentBlocks f i j (Fin.natAdd k a)) = right := by
    funext a
    exact appendTuple_right _ _ a
  let leftIndex := intervalIndex f i j hij
  let rightIndex := tupleIndex hk right
  have hleftIndex : tupleIndex hk left = leftIndex := shifted_tuple_index f i j hij
  have hfirstLeft : first leftIndex = f i := first_interval f hf i j hij
  have hfirstRight : first rightIndex = f j := by
    rw [first_tuple hk right hright]
    rfl
  have hnot : part ≤ (goodPair (relation (f i) (f j))
      (sets context domain relation hlarge leftIndex) (sets context domain relation hlarge rightIndex))ᶜ := by
    have h := hnotGood
    change part ≤ (goodHalves context domain relation hlarge k hk (adjacentBlocks f i j))ᶜ at h
    dsimp only [goodHalves] at h
    rw [htLeft, htRight, hleftIndex] at h
    change part ≤ (goodPair (relation (first leftIndex) (first rightIndex))
      (sets context domain relation hlarge leftIndex) (sets context domain relation hlarge rightIndex))ᶜ at h
    rwa [hfirstLeft, hfirstRight] at h
  have hrightSubset : part ≤ sets context domain relation hlarge rightIndex ⊆ᴮ
      sets context domain relation hlarge (singleton (f j)) := by
    simpa only [hfirstRight] using hpart.trans (sets_to_first context domain relation hlarge rightIndex)
  have hnotSingleton := goodPair_forbidden_on_larger part (relation (f i) (f j))
    (sets context domain relation hlarge leftIndex) (sets context domain relation hlarge rightIndex)
    (sets context domain relation hlarge (singleton (f j))) hrightSubset hnot
  let chain := intervalIndex f i (j + 1) (hij.trans (Nat.lt_succ_self j))
  have hlast : last chain = f j := last_interval_succ f hf i j hij.le
  have herase : chain.val.erase (last chain) = leftIndex.val := by
    rw [hlast]
    exact erase_last_interval f hf i j hij
  have he : (chain.val.erase (last chain)).Nonempty := by
    rw [herase]
    exact leftIndex.property
  have hprior : priorIndex (erasePrior chain rfl he) = leftIndex := Subtype.ext herase
  have hbad : part ≤ badPair (relation (f i) (f j)) (sets context domain relation hlarge chain)
      (sets context domain relation hlarge (singleton (f j))) := by
    have hin : part ≤ (goodPair (relation (first (priorIndex (erasePrior chain rfl he))) (last chain))
        (sets context domain relation hlarge (priorIndex (erasePrior chain rfl he)))
        (sets context domain relation hlarge (singleton (last chain))))ᶜ := by
      simpa only [hprior, hlast, hfirstLeft] using hnotSingleton
    have h := sets_bad_extension_at context part hpart domain relation hlarge chain he hin
    simpa only [hprior, hlast, hfirstLeft] using h
  apply badPair_restrict part (relation (f i) (f j))
    (sets context domain relation hlarge chain) (sets context domain relation hlarge (singleton (f j)))
    (sets context domain relation hlarge (intervalIndex f i n (hij.trans hjn)))
    (sets context domain relation hlarge (intervalIndex f j n hjn))
  · exact hpart.trans (sets_interval_prefix context domain relation hlarge f hf i (j + 1) n
      (hij.trans (Nat.lt_succ_self j)) (Nat.succ_le_of_lt hjn))
  · simpa only [first_interval f hf j n hjn] using
      hpart.trans (sets_to_first context domain relation hlarge (intervalIndex f j n hjn))
  · exact hbad

theorem homogeneous_halves (context : ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (relation : ℕ → ℕ → bSet ScheduledIteration.finalAlgebra)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra) (domain r) bSet.omega)ᶜ)
    (k : ℕ) (hk : 0 < k) (initial : ℕ → ScheduledIteration.finalAlgebra)
    (hinfinite : context ≤ infiniteValue initial) :
    ∃ selected : ℕ → ScheduledIteration.finalAlgebra, ∃ side : ScheduledIteration.finalAlgebra,
      (∀ i, selected i ≤ initial i) ∧ context ≤ infiniteValue selected ∧
      BooleanTupleRamsey.Homogeneous context (k + k) (goodHalves context domain relation hlarge k hk)
        selected side :=
  BooleanTupleRamsey.exists_homogeneous context (k + k)
    (goodHalves context domain relation hlarge k hk) initial hinfinite

theorem bad_interval_of_homogeneous (context part : B)
    (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (f : ℕ → ℕ) (hf : StrictMono f) (i j n : ℕ) (hij : i < j) (hjn : j < n)
    (selected : ℕ → B) (side : B)
    (hhomogeneous : BooleanTupleRamsey.Homogeneous context ((j - i) + (j - i))
      (goodHalves context domain relation hlarge (j - i) (Nat.sub_pos_of_lt hij)) selected side)
    (hweight : part ≤ context ⊓ (tupleWeight selected (adjacentBlocks f i j) ⊓ sideᶜ)) :
    part ≤ badPair (relation (f i) (f j))
      (sets context domain relation hlarge (intervalIndex f i n (hij.trans hjn)))
      (sets context domain relation hlarge (intervalIndex f j n hjn)) :=
  bad_interval_pair context part (hweight.trans inf_le_left) domain relation hlarge f hf i j n hij hjn
    (hweight.trans ((hhomogeneous _ (adjacentBlocks_strict f hf i j hij)).2))

end Erdos597Object.BooleanGoodBlocks
