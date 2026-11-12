import Erdos597Object.BooleanRedImages

set_option backward.isDefEq.respectTransparency false

/-! Ordered uncountable image families extracted from the exact red-copy predicate. -/

namespace Erdos597Object.BooleanRedCopyFamilies

open Erdos597 Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections CanonicalDomains BooleanRowSlices

variable {B : Type} [CompleteBooleanAlgebra B] {context : B} {blue : bSet B}

structure Family (context : B) (blue : bSet B) where
  values : Nat → One → bSet B
  members : ∀ (row : Nat) (i : One), context ≤ values row i ∈ᴮ squareDomain
  separate : ∀ (row : Nat) (i j : One), i ≠ j → context ⊓ (values row i =ᴮ values row j) = ⊥
  before : ∀ (m n : Nat) (i j : One), m < n →
    context ≤ edgeValue (V B) squareOrder (values m i) (values n j)
  red : ∀ (m n : Nat) (i j : One), m ≠ n →
    context ≤ (edgeValue (V B) blue (values m i) (values n j))ᶜ

theorem Family.image_uncountable (F : Family (B := B) context blue)
    (hB : has_dense_omega_closed_subset B) (row : Nat) :
    context ≤ (injectsIntoValue (V B) (BooleanRedImages.imageName (F.values row)) bSet.omega)ᶜ :=
  BooleanRedImages.image_uncountable hB context (F.values row) (F.members row) (F.separate row)

theorem Family.images_before (F : Family (B := B) context blue) (m n : Nat) (hmn : m < n)
    (u v : Vertex) :
    (context ⊓ BooleanRedImages.imageWeight (F.values m) u) ⊓
      BooleanRedImages.imageWeight (F.values n) v ≤
      edgeValue (V B) squareOrder (BooleanRedImages.vertexLabel u) (BooleanRedImages.vertexLabel v) :=
  BooleanRedImages.image_pair_transfer context (F.values m) (F.values n)
    (fun x y => edgeValue (V B) squareOrder x y)
    (edge_left_ext squareOrder) (edge_right_ext squareOrder)
    (fun i j => F.before m n i j hmn) u v

theorem Family.images_red (F : Family (B := B) context blue) (m n : Nat) (hmn : m ≠ n)
    (u v : Vertex) :
    (context ⊓ BooleanRedImages.imageWeight (F.values m) u) ⊓
      BooleanRedImages.imageWeight (F.values n) v ≤
      (edgeValue (V B) blue (BooleanRedImages.vertexLabel u) (BooleanRedImages.vertexLabel v))ᶜ :=
  BooleanRedImages.image_pair_transfer context (F.values m) (F.values n)
    (fun x y => (edgeValue (V B) blue x y)ᶜ)
    (fun y => bSet.B_ext_compl (edge_left_ext blue y))
    (fun x => bSet.B_ext_compl (edge_right_ext blue x))
    (fun i j => F.red m n i j hmn) u v

theorem family_of_mapping (context : B) (blue mapping : bSet B)
    (hfunction : context ≤ functionFromValue (V B) blockDomain squareDomain mapping)
    (hinjective : context ≤ injectiveValue (V B) mapping)
    (horder : context ≤ respectsOrderValue (V B) blockOrder squareOrder mapping)
    (hred : context ≤ avoidsEdgesValue (V B) blue mapping) :
    Nonempty (Family context blue) := by
  classical
  have hexists : ∀ key : Nat × One, ∃ value : bSet B,
      context ≤ value ∈ᴮ squareDomain ∧
      context ≤ edgeValue (V B) mapping (orderedLabel key.1 key.2) value := by
    intro key
    have htotal := hfunction.trans (inf_le_right.trans inf_le_right)
    have himp := htotal.trans (iInf_le _ (orderedLabel key.1 key.2))
    have hcover := lattice.bv_context_apply himp (le_top.trans (orderedLabel_member key.1 key.2))
    obtain ⟨value, hvalue⟩ := bSet.exists_convert hcover
      (bSet.B_ext_inf (bSet.B_ext_mem_left squareDomain)
        (edge_right_ext mapping (orderedLabel key.1 key.2)))
    exact ⟨value, hvalue.trans inf_le_left, hvalue.trans inf_le_right⟩
  choose values hmembers hpairs using hexists
  refine ⟨⟨(fun row i => values (row, i)), (fun row i => hmembers (row, i)), ?_, ?_, ?_⟩⟩
  · intro row i j hij
    let part := context ⊓ (values (row, i) =ᴮ values (row, j))
    have hleft : part ≤ edgeValue (V B) mapping (orderedLabel row i) (values (row, i)) :=
      inf_le_left.trans (hpairs (row, i))
    have hright : part ≤ edgeValue (V B) mapping (orderedLabel row j) (values (row, i)) :=
      (le_inf (bSet.bv_symm inf_le_right) (inf_le_left.trans (hpairs (row, j)))).trans
        (edge_right_ext mapping (orderedLabel row j) (values (row, j)) (values (row, i)))
    have hsource := (le_inf inf_le_left (le_inf hleft hright)).trans
      (injective_outputs mapping hinjective (orderedLabel row i) (orderedLabel row j) (values (row, i)))
    exact bot_unique (hsource.trans_eq (orderedLabel_discrete row i j hij))
  · intro m n i j hmn
    have hsource : context ≤ edgeValue (V B) blockOrder (orderedLabel m i) (orderedLabel n j) := by
      rw [orderedLabel, orderedLabel, BooleanBlockOrder.blockOrder_edge]
      have hkey : BooleanBlockOrder.keyLess (m, BooleanColumns.columnEquiv.symm i)
          (n, BooleanColumns.columnEquiv.symm j) := Or.inl hmn
      simp only [ite_eq_left hkey, le_top]
    have himp := horder.trans ((iInf_le _ (orderedLabel m i)).trans
      ((iInf_le _ (orderedLabel n j)).trans ((iInf_le _ (values (m, i))).trans
        (iInf_le _ (values (n, j))))))
    have hbiimp := lattice.bv_context_apply himp (le_inf (hpairs (m, i)) (hpairs (n, j)))
    exact lattice.bv_context_apply (hbiimp.trans inf_le_left) hsource
  · intro m n i j hmn
    have hsource : (orderedLabel (B := B) m i =ᴮ orderedLabel n j) = ⊥ :=
      blockLabel_discrete _ _ (fun heq => hmn (congrArg Prod.fst heq))
    have himp := hred.trans ((iInf_le _ (orderedLabel m i)).trans
      ((iInf_le _ (orderedLabel n j)).trans ((iInf_le _ (values (m, i))).trans
        (iInf_le _ (values (n, j))))))
    have h := lattice.bv_context_apply himp (le_inf (hpairs (m, i)) (hpairs (n, j)))
    simpa only [eqValue_bSet, hsource, bot_sup_eq] using h

end Erdos597Object.BooleanRedCopyFamilies
