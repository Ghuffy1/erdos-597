import Erdos597Object.BooleanWeightedRectangles

set_option backward.isDefEq.respectTransparency false

/-! Uniform finite families on the row-tagged canonical block vertices. -/

namespace Erdos597Object.BooleanIndependentFamilies

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanIndependentConditions BooleanIndependentRows CanonicalDomains

noncomputable def groundEquiv : Vertex ≃ ℕ × Erdos597.One where
  toFun v := (Nat.pair v.1 v.2.1, oneLabelsEquiv.symm v.2.2)
  invFun v := (v.1.unpair.1, (v.1.unpair.2, oneLabelsEquiv v.2))
  left_inv := by
    rintro ⟨r, s, label⟩
    simp only [Nat.unpair_pair, Equiv.apply_symm_apply]
  right_inv := by
    rintro ⟨r, col⟩
    simp only [Nat.pair_unpair, Equiv.symm_apply_apply]

noncomputable def point (row : ℕ) (col : Erdos597.One) : Vertex :=
  groundEquiv.symm (row, col)

theorem point_row (row : ℕ) (col : Erdos597.One) : (point row col).1 = row.unpair.1 := rfl

theorem point_label (row : ℕ) (col : Erdos597.One) :
    (point row col).2 = (row.unpair.2, oneLabelsEquiv col) := rfl

theorem uniform_family (points : Erdos597.One → Finset Vertex) :
    ∃ index : Erdos597.One ↪ Erdos597.One, ∃ n : ℕ, ∃ root : Finset Vertex,
      ∃ row : Fin n → ℕ, ∃ col : Fin n → Erdos597.One ↪ Erdos597.One,
        (∀ i, root ⊆ points (index i)) ∧
        (∀ i k, point (row k) (col k i) ∈ points (index i)) ∧
        (∀ i x, x ∈ points (index i) → x ∈ root ∨ ∃ k, x = point (row k) (col k i)) := by
  classical
  let coded := fun i => (points i).map groundEquiv.toEmbedding
  obtain ⟨index, n, root, row, col, hroot, hmem, hcover⟩ := Erdos597.uniform_finite_family coded
  refine ⟨index, n, root.map groundEquiv.symm.toEmbedding, row, col, ?_, ?_, ?_⟩
  · intro i x hx
    have hcode : groundEquiv x ∈ root := by simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using hx
    have h := hroot i hcode
    simpa only [coded, Finset.mem_map_equiv, Equiv.symm_apply_apply] using h
  · intro i k
    simpa only [coded, Finset.mem_map_equiv, point] using hmem i k
  · intro i x hx
    have hcode : groundEquiv x ∈ coded (index i) := by
      simpa only [coded, Finset.mem_map_equiv, Equiv.symm_apply_apply] using hx
    rcases hcover i (groundEquiv x) hcode with hr | ⟨k, hk⟩
    · left
      simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using hr
    · right
      exact ⟨k, by simpa only [point, Equiv.symm_apply_apply] using congrArg groundEquiv.symm hk⟩

variable {B : Type} [CompleteBooleanAlgebra B]

theorem point_labels_discrete {row : ℕ} (col : Erdos597.One ↪ Erdos597.One)
    (i j : Erdos597.One) (hij : i ≠ j) :
    (blockLabel (point row (col i)).2 =ᴮ blockLabel (point row (col j)).2 : B) = ⊥ := by
  apply blockLabel_discrete
  intro h
  have hcol : oneLabelsEquiv (col i) = oneLabelsEquiv (col j) := congrArg Prod.snd h
  exact hij (col.injective (oneLabelsEquiv.injective hcol))

end Erdos597Object.BooleanIndependentFamilies
