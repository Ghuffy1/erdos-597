import Erdos597Object.BooleanFiniteRamsey
import Erdos597Object.BooleanFiniteSelections

set_option backward.isDefEq.respectTransparency false

/-! Ramsey homogeneity for increasing tuples, with their full Boolean weights. -/

namespace Erdos597Object.BooleanTupleRamsey

open BooleanInfiniteSets BooleanFiniteSelections

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def setColor (n : ℕ) (color : (Fin n → ℕ) → B) (subset : Finset ℕ) : B := by
  classical
  exact if h : subset.card = n then color (subset.orderEmbOfFin h) else ⊥

def Homogeneous (context : B) (n : ℕ) (color : (Fin n → ℕ) → B) (selected : ℕ → B) (side : B) : Prop :=
  ∀ tuple : Fin n → ℕ, StrictMono tuple →
    (context ⊓ (tupleWeight selected tuple ⊓ side) ≤ color tuple) ∧
    (context ⊓ (tupleWeight selected tuple ⊓ sideᶜ) ≤ (color tuple)ᶜ)

theorem setColor_tuple (n : ℕ) (color : (Fin n → ℕ) → B) (tuple : Fin n → ℕ)
    (hmono : StrictMono tuple) : setColor n color (Finset.univ.image tuple) = color tuple := by
  classical
  have hcard : (Finset.univ.image tuple).card = n := by
    rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
  have hmembers (i : Fin n) : tuple i ∈ Finset.univ.image tuple :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hcanonical : tuple = (Finset.univ.image tuple).orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard hmembers hmono
  simp only [setColor, dite_eq_left hcard, ← hcanonical]

theorem of_set_homogeneous (context : B) (n : ℕ) (color : (Fin n → ℕ) → B)
    (selected : ℕ → B) (side : B)
    (h : BooleanFiniteRamsey.Homogeneous context n (setColor n color) selected side) :
    Homogeneous context n color selected side := by
  intro tuple hmono
  have hcard : (Finset.univ.image tuple).card = n := by
    rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
  have htuple := h (Finset.univ.image tuple) hcard
  rwa [tupleWeight_image, setColor_tuple n color tuple hmono] at htuple

theorem restrict (context : B) (n : ℕ) (color : (Fin n → ℕ) → B) (large small : ℕ → B)
    (side : B) (hsmall : ∀ i, small i ≤ large i)
    (h : Homogeneous context n color large side) : Homogeneous context n color small side := by
  intro tuple hmono
  obtain ⟨htrue, hfalse⟩ := h tuple hmono
  have hweight := tupleWeight_mono small large tuple hsmall
  exact ⟨(inf_le_inf le_rfl (inf_le_inf hweight le_rfl)).trans htrue,
    (inf_le_inf le_rfl (inf_le_inf hweight le_rfl)).trans hfalse⟩

theorem subcontext (context smaller : B) (n : ℕ) (color : (Fin n → ℕ) → B)
    (selected : ℕ → B) (side : B) (hsmall : smaller ≤ context)
    (h : Homogeneous context n color selected side) : Homogeneous smaller n color selected side := by
  intro tuple hmono
  obtain ⟨htrue, hfalse⟩ := h tuple hmono
  exact ⟨(inf_le_inf hsmall le_rfl).trans htrue, (inf_le_inf hsmall le_rfl).trans hfalse⟩

theorem exists_homogeneous (context : ScheduledIteration.finalAlgebra) (n : ℕ)
    (color : (Fin n → ℕ) → ScheduledIteration.finalAlgebra)
    (initial : ℕ → ScheduledIteration.finalAlgebra) (hinfinite : context ≤ infiniteValue initial) :
    ∃ selected : ℕ → ScheduledIteration.finalAlgebra, ∃ side : ScheduledIteration.finalAlgebra,
      (∀ i, selected i ≤ initial i) ∧ context ≤ infiniteValue selected ∧
      Homogeneous context n color selected side := by
  obtain ⟨selected, side, hsub, hinfiniteSelected, hhomogeneous⟩ :=
    BooleanFiniteRamsey.exists_homogeneous context n (setColor n color) initial hinfinite
  exact ⟨selected, side, hsub, hinfiniteSelected,
    of_set_homogeneous context n color selected side hhomogeneous⟩

end Erdos597Object.BooleanTupleRamsey
