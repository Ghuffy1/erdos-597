import Erdos597Object.BooleanPairDecisions

set_option backward.isDefEq.respectTransparency false

/-! The finite-chain row family in the Boolean-valued weak-independence argument. -/

namespace Erdos597Object.BooleanWeakFamilies

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanRectangles BooleanGoodPairs BooleanPairDecisions BooleanUncountableRamsey
open Erdos597.WeakFamilies (Index first last singleton Prior priorIndex prior_last_lt
  erasePrior first_erase first_of_erase_empty)

variable {B : Type} [CompleteBooleanAlgebra B]

structure RowName (context : B) (domain : ℕ → bSet B) (row : ℕ) where
  name : bSet B
  uncountable : context ≤ (injectsIntoValue (V B) name bSet.omega)ᶜ
  subset : context ≤ name ⊆ᴮ domain row

abbrev At (context : B) (domain : ℕ → bSet B) (r : ℕ) :=
  ∀ s : Index, last s = r → RowName context domain (first s)

abbrev Before (context : B) (domain : ℕ → bSet B) (r : ℕ) :=
  ∀ t : ℕ, t < r → At context domain t

def previous {context : B} {domain : ℕ → bSet B} {r : ℕ}
    (old : Before context domain r) (s : Prior r) : RowName context domain (first (priorIndex s)) :=
  old (last (priorIndex s)) (prior_last_lt s) (priorIndex s) rfl

structure Decision (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (r : ℕ) (old : Before context domain r) where
  right : RowName context domain r
  left : ∀ s : Prior r, RowName context domain (first (priorIndex s))
  contained : ∀ s, context ≤ (left s).name ⊆ᴮ (previous old s).name
  status : ∀ s, context ≤
    goodPair (relation (first (priorIndex s)) r) (previous old s).name right.name ⊔
      badPair (relation (first (priorIndex s)) r) (left s).name right.name

theorem exists_decision (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (r : ℕ) (old : Before context domain r) : Nonempty (Decision context domain relation r old) := by
  classical
  let : Fintype (Prior r) := Fintype.ofFinite _
  obtain ⟨right, hright, hleft⟩ := all_finite_decisions context
    (fun s : Prior r => relation (first (priorIndex s)) r)
    (fun s => (previous old s).name) (domain r)
    (fun s => (previous old s).uncountable) (hlarge r)
  choose left hleftLarge hstatus using hleft
  exact ⟨{
    right := ⟨right, hright.trans inf_le_right, hright.trans inf_le_left⟩
    left := fun s => ⟨left s, (hleftLarge s).trans inf_le_right,
      subset_trans ((hleftLarge s).trans inf_le_left) (previous old s).subset⟩
    contained := fun s => (hleftLarge s).trans inf_le_left
    status := hstatus
  }⟩

noncomputable def decision (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (r : ℕ) (old : Before context domain r) : Decision context domain relation r old :=
  Classical.choice (exists_decision context domain relation hlarge r old)

noncomputable def step (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (r : ℕ) (old : Before context domain r) : At context domain r := by
  classical
  intro s hs
  let d := decision context domain relation hlarge r old
  by_cases he : (s.val.erase r).Nonempty
  · let p := erasePrior s hs he
    refine ⟨(d.left p).name, (d.left p).uncountable, ?_⟩
    have hfirst := first_erase s hs he
    rw [← hfirst]
    exact (d.left p).subset
  · refine ⟨d.right.name, d.right.uncountable, ?_⟩
    have heq : s.val.erase r = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    rw [first_of_erase_empty s heq]
    exact d.right.subset

theorem step_name_nonempty (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (r : ℕ) (old : Before context domain r) (s : Index) (hs : last s = r)
    (he : (s.val.erase r).Nonempty) :
    (step context domain relation hlarge r old s hs).name =
      ((decision context domain relation hlarge r old).left (erasePrior s hs he)).name := by
  simp [step, he]

theorem step_name_empty (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ)
    (r : ℕ) (old : Before context domain r) (s : Index) (hs : last s = r)
    (he : s.val.erase r = ∅) :
    (step context domain relation hlarge r old s hs).name =
      (decision context domain relation hlarge r old).right.name := by
  simp [step, he]

noncomputable def family (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ) : ∀ r, At context domain r :=
  wellFounded_lt.fix (step context domain relation hlarge)

theorem family_eq (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ) (r : ℕ) :
    family context domain relation hlarge r =
      step context domain relation hlarge r (fun t _ => family context domain relation hlarge t) := by
  rw [family, WellFounded.fix_eq]

noncomputable def sets (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ) (s : Index) : bSet B :=
  (family context domain relation hlarge (last s) s rfl).name

theorem sets_uncountable (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ) (s : Index) :
    context ≤ (injectsIntoValue (V B) (sets context domain relation hlarge s) bSet.omega)ᶜ :=
  (family context domain relation hlarge (last s) s rfl).uncountable

theorem sets_subset (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ) (s : Index) :
    context ≤ sets context domain relation hlarge s ⊆ᴮ domain (first s) :=
  (family context domain relation hlarge (last s) s rfl).subset

theorem sets_singleton (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ) (r : ℕ) :
    sets context domain relation hlarge (singleton r) =
      (decision context domain relation hlarge r (fun t _ => family context domain relation hlarge t)).right.name := by
  unfold sets
  simp only [Erdos597.WeakFamilies.last_singleton]
  rw [family_eq]
  exact step_name_empty context domain relation hlarge r _ _ _
    (by simp [Erdos597.WeakFamilies.singleton])

theorem sets_shrink (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ) (s : Index)
    (he : (s.val.erase (last s)).Nonempty) :
    context ≤ sets context domain relation hlarge s ⊆ᴮ
      sets context domain relation hlarge (priorIndex (erasePrior s rfl he)) := by
  unfold sets
  rw [family_eq, step_name_nonempty context domain relation hlarge (last s) _ s rfl he]
  exact (decision context domain relation hlarge (last s)
    (fun t _ => family context domain relation hlarge t)).contained _

theorem sets_bad_extension (context : B) (domain : ℕ → bSet B) (relation : ℕ → ℕ → bSet B)
    (hlarge : ∀ r, context ≤ (injectsIntoValue (V B) (domain r) bSet.omega)ᶜ) (s : Index)
    (he : (s.val.erase (last s)).Nonempty)
    (hnotGood : context ≤ (goodPair (relation (first (priorIndex (erasePrior s rfl he))) (last s))
      (sets context domain relation hlarge (priorIndex (erasePrior s rfl he)))
      (sets context domain relation hlarge (singleton (last s))))ᶜ) :
    context ≤ badPair (relation (first (priorIndex (erasePrior s rfl he))) (last s))
      (sets context domain relation hlarge s) (sets context domain relation hlarge (singleton (last s))) := by
  have hstatus := (decision context domain relation hlarge (last s)
    (fun t _ => family context domain relation hlarge t)).status (erasePrior s rfl he)
  have hset : sets context domain relation hlarge s =
      ((decision context domain relation hlarge (last s) (fun t _ => family context domain relation hlarge t)).left
        (erasePrior s rfl he)).name := by
    unfold sets
    rw [family_eq, step_name_nonempty context domain relation hlarge (last s) _ s rfl he]
  rw [sets_singleton] at hnotGood ⊢
  rw [hset]
  apply lattice.context_or_elim' hstatus
  · intro part hpart hgood
    exact ((le_inf hgood (hpart.trans hnotGood)).trans_eq inf_compl_eq_bot).trans bot_le
  · intro part hpart hbad
    exact hbad

end Erdos597Object.BooleanWeakFamilies
