import Erdos597Object.FilterCoefficients
import Erdos597Object.PosetRelabeling

set_option backward.isDefEq.respectTransparency false

/-! Transfer coefficient witnesses back across a relabeling equivalence. -/

namespace Erdos597Object.RelabeledFilters

open BooleanIteration PosetRelabeling

variable {B I J D : Type} [CompleteBooleanAlgebra B]

theorem pull_coefficients (e : J ≃ I) (P : BooleanPoset B I) (dense : D → I → B)
    (weight : J → B)
    (hvalid : ∀ j, weight j ≤ (relabel e P).member j)
    (hcover : (⨆ j, weight j) = ⊤)
    (hup : ∀ j k, weight j ⊓ (relabel e P).leValue j k ≤ weight k)
    (hdir : ∀ j k, weight j ⊓ weight k ≤ ⨆ l, weight l ⊓
      ((relabel e P).leValue l j ⊓ (relabel e P).leValue l k))
    (hmeets : ∀ d, (⨆ j, weight j ⊓ dense d (e j)) = ⊤) :
    ∃ value : I → B,
      (∀ i, value i ≤ P.member i) ∧
      (⨆ i, value i) = ⊤ ∧
      (∀ i j, value i ⊓ P.leValue i j ≤ value j) ∧
      (∀ i j, value i ⊓ value j ≤ ⨆ k, value k ⊓ (P.leValue k i ⊓ P.leValue k j)) ∧
      (∀ d, (⨆ i, value i ⊓ dense d i) = ⊤) := by
  refine ⟨fun i => weight (e.symm i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [relabel, e.apply_symm_apply] using hvalid (e.symm i)
  · exact (e.symm.surjective.iSup_comp weight).trans hcover
  · intro i j
    simpa only [relabel, e.apply_symm_apply] using hup (e.symm i) (e.symm j)
  · intro i j
    have h := hdir (e.symm i) (e.symm j)
    simp only [relabel, e.apply_symm_apply] at h
    have heq : (⨆ k : J, weight k ⊓ (P.leValue (e k) i ⊓ P.leValue (e k) j)) =
        ⨆ k : I, weight (e.symm k) ⊓ (P.leValue k i ⊓ P.leValue k j) := by
      simpa only [e.symm_apply_apply] using
        e.surjective.iSup_comp (fun k => weight (e.symm k) ⊓ (P.leValue k i ⊓ P.leValue k j))
    exact h.trans_eq heq
  · intro d
    have heq := e.symm.surjective.iSup_comp (fun j => weight j ⊓ dense d (e j))
    simpa only [e.apply_symm_apply] using heq.trans (hmeets d)

end Erdos597Object.RelabeledFilters
