import Erdos597Object.BooleanCopyExtensions

set_option backward.isDefEq.respectTransparency false

/-! The canonical omega-one times omega block sits in the canonical ordinal square. -/

namespace Erdos597Object.CanonicalBlockInclusion

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet Ordinal
open BooleanSets BooleanUncountableRamsey CanonicalDomains

variable {B : Type} [CompleteBooleanAlgebra B]

theorem omega_subset_omegaOne : (⊤ : B) ≤ bSet.omega ⊆ᴮ omegaOneName := by
  have hsets : ZFSet.mk PSet.omega ⊆ ZFSet.mk (ω₁ : Ordinal.{0}).toPSet := by
    change ZFSet.omega ⊆ (ω₁ : Ordinal.{0}).toZFSet
    rw [← OrdinalPresentation.omega_toZFSet]
    exact Ordinal.toZFSet_monotone (Ordinal.omega0_le_omega 1)
  apply bSet.check_subset
  apply Flypitch.pSet.subset_iff_all_mem.mpr
  intro x hx
  exact Flypitch.pSet.mem_iff.mpr (hsets (Flypitch.pSet.mem_iff.mp hx))

theorem block_subset_square : (⊤ : B) ≤ blockDomain ⊆ᴮ squareDomain :=
  subset_trans (bSet.subset_of_eq blockDomain_eq_product)
    (subset_trans (bSet.prod_subset_left omega_subset_omegaOne)
      (bSet.subset_of_eq (bSet.bv_symm squareDomain_eq_product)))

theorem orders_agree (context : B) (x y : bSet B) :
    context ⊓ ((x ∈ᴮ blockDomain) ⊓ (y ∈ᴮ blockDomain)) ≤
      lattice.biimp (edgeValue (V B) blockOrder x y) (edgeValue (V B) squareOrder x y) := by
  let part := context ⊓ ((x ∈ᴮ blockDomain) ⊓ (y ∈ᴮ blockDomain))
  have hx : part ≤ x ∈ᴮ blockDomain := inf_le_right.trans inf_le_left
  have hy : part ≤ y ∈ᴮ blockDomain := inf_le_right.trans inf_le_right
  have hxSquare : part ≤ x ∈ᴮ squareDomain :=
    bSet.mem_of_mem_subset' (le_top.trans block_subset_square) hx
  have hySquare : part ≤ y ∈ᴮ squareDomain :=
    bSet.mem_of_mem_subset' (le_top.trans block_subset_square) hy
  have hblock := lattice.bv_context_apply
    ((lattice.bv_context_apply
      ((le_top.trans block_order_spec).trans (inf_le_right.trans (iInf_le _ x))) hx).trans
        (iInf_le _ y)) hy
  have hsquare := lattice.bv_context_apply
    ((lattice.bv_context_apply
      ((le_top.trans square_order_spec).trans (inf_le_right.trans (iInf_le _ x))) hxSquare).trans
        (iInf_le _ y)) hySquare
  apply lattice.bv_biimp_iff.mpr
  intro smaller hsmaller
  exact ((lattice.bv_biimp_iff.mp hblock) hsmaller).trans
    (((lattice.bv_biimp_iff.mp hsquare) hsmaller).symm)

end Erdos597Object.CanonicalBlockInclusion
