import Erdos597Object.CHInterpretation

set_option backward.isDefEq.respectTransparency false

/-!
Boolean semantics of universal closure and the collection schema.
The substitution lemmas generalize the collection lemmas in Flypitch.ZFC
to arbitrary Boolean-valued structures.
-/

namespace Erdos597Object

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC

universe u

variable {B : Type u} [CompleteBooleanAlgebra B]
variable (S : bStructure L_ZFC B)

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

local instance : Nonempty S := ⟨S.fun_map ZFCFunc.emptyset []⟩

def unionValue (x : S) : S := S.fun_map ZFCFunc.union (x :: [])

@[simp] theorem realize_union {n : ℕ} (v : dvector S n) (x : Term n) :
    boolean_realize_bounded_term v (union x) [] =
      unionValue S (boolean_realize_bounded_term v x []) := by
  simp only [union, unionValue, bd_app, bd_func, boolean_realize_bounded_term,
    boolean_realize_bounded_term_mk_fst]
  rfl

theorem iInf_vector_cons {n : ℕ} (f : dvector S (n + 1) → B) :
    (⨅ v, f v) = ⨅ xs : dvector S n, ⨅ x : S, f (x :: xs) := by
  apply le_antisymm
  · apply le_iInf
    intro xs
    apply le_iInf
    intro x
    exact iInf_le f (x :: xs)
  · apply le_iInf
    intro v
    cases v with
    | cons x xs => exact (iInf_le _ xs).trans (iInf_le _ x)

theorem realize_universalClosure {n : ℕ} (f : bounded_formula L_ZFC n) :
    boolean_realize_sentence S (bdAllsFrom n f) =
      ⨅ xs : dvector S n, boolean_realize_bounded_formula (S := S) xs f [] := by
  induction n with
  | zero =>
    simp only [bdAllsFrom, boolean_realize_sentence]
    apply le_antisymm
    · apply le_iInf
      intro xs
      cases xs
      exact le_rfl
    · exact iInf_le _ []
  | succ n ih =>
    rw [bdAllsFrom, ih, iInf_vector_cons]
    simp only [boolean_realize_bounded_formula_all]

@[simp] theorem collection_lift_one {n : ℕ}
    (f : bounded_formula L_ZFC (n + 2)) (xs : dvector S n) (x y domain : S) :
    boolean_realize_bounded_formula (S := S) (y :: x :: domain :: xs) (f.liftAt 1 2) [] =
      boolean_realize_bounded_formula (S := S) (y :: x :: xs) f [] := by
  simpa [dvector.insertAt] using
    boolean_realize_bounded_formula_liftAt_insert (S := S)
      (h := (by omega : 2 ≤ n + 2)) (f := f) (v := y :: x :: xs) domain []

@[simp] theorem collection_lift_two {n : ℕ}
    (f : bounded_formula L_ZFC (n + 2)) (xs : dvector S n) (x y image domain : S) :
    boolean_realize_bounded_formula (S := S) (y :: x :: image :: domain :: xs) (f.liftAt 2 2) [] =
      boolean_realize_bounded_formula (S := S) (y :: x :: xs) f [] := by
  simpa [dvector.insertAt] using
    boolean_realize_bounded_formula_liftAt_insert₂ (S := S)
      (h := (by omega : 2 ≤ n + 2)) (f := f) (v := y :: x :: xs) image domain []

@[simp] theorem collection_lift_three {n : ℕ}
    (f : bounded_formula L_ZFC (n + 2)) (xs : dvector S n) (x y z image domain : S) :
    boolean_realize_bounded_formula (S := S) (y :: x :: z :: image :: domain :: xs)
        (f.liftAt 3 2) [] =
      boolean_realize_bounded_formula (S := S) (y :: x :: xs) f [] := by
  simpa [dvector.insertAt] using
    boolean_realize_bounded_formula_liftAt_insert₃ (S := S)
      (h := (by omega : 2 ≤ n + 2)) (f := f) (v := y :: x :: xs) z image domain []

@[simp] theorem collection_substitute_three {n : ℕ}
    (f : bounded_formula L_ZFC (n + 2)) (xs : dvector S n) (x y image domain : S) :
    boolean_realize_bounded_formula (S := S) (x :: y :: image :: domain :: xs)
        (subst_bounded_formula_open (f.liftAt 3 2) var1) [] =
      boolean_realize_bounded_formula (S := S) (y :: x :: xs) f [] := by
  rw [boolean_realize_bounded_formula_subst_open]
  simp [var1, var, bd_var]

@[simp] theorem collection_substitute_raw {n m : ℕ}
    (f : bounded_formula L_ZFC (n + 2)) (xs : dvector S n) (x y image domain : S)
    (hBound : bounded_formula_at
      (subst_formula (f.liftAt 3 2).fst (var1 (n := m)).fst 0) (n + 4)) :
    boolean_realize_bounded_formula (S := S) (x :: y :: image :: domain :: xs)
        (⟨subst_formula (f.liftAt 3 2).fst (var1 (n := m)).fst 0, hBound⟩ :
          bounded_formula L_ZFC (n + 4)) [] =
      boolean_realize_bounded_formula (S := S) (y :: x :: xs) f [] := by
  have hterm : (↑(var1 (n := m)) : preterm L_ZFC 0) =
      (↑(var1 : bounded_term L_ZFC (n + 4)) : preterm L_ZFC 0) := by
    simp [var1, var, bd_var, bounded_preterm.fst]
  have hfst : bounded_preformula.fst
      (⟨subst_formula (f.liftAt 3 2).fst (var1 (n := m)).fst 0, hBound⟩ :
        bounded_formula L_ZFC (n + 4)) =
      (subst_bounded_formula_open (f.liftAt 3 2)
        (var1 : bounded_term L_ZFC (n + 4))).fst := by
    simpa [bounded_preformula.fst, subst_bounded_formula_open_fst] using
      congrArg (fun t => subst_formula (f.liftAt 3 2).fst t 0) hterm
  rw [boolean_realize_bounded_formula_fst_eq hfst []]
  exact collection_substitute_three S f xs x y image domain

@[simp] theorem collection_substitute_coe {n : ℕ}
    (f : bounded_formula L_ZFC (n + 2)) (xs : dvector S n) (x y image domain : S)
    (hBound : bounded_formula_at
      (subst_formula (↑(bounded_preformula.liftAt f 3 2) : preformula L_ZFC 0)
        (↑(var1 (n := n + 2) : bounded_term L_ZFC (n + 4)) : term L_ZFC) 0) (n + 4)) :
    boolean_realize_bounded_formula (S := S) (x :: y :: image :: domain :: xs)
        (⟨_, hBound⟩ : bounded_formula L_ZFC (n + 4)) [] =
      boolean_realize_bounded_formula (S := S) (y :: x :: xs) f [] := by
  simpa [bounded_preformula.fst, bounded_preterm.fst] using
    collection_substitute_raw S (m := n + 2) f xs x y image domain hBound

def collectionValue (relation : S → S → B) (domain : S) : B :=
  (⨅ x : S, (memberValue S x domain)ᶜ ⊔ ⨆ y : S, relation x y)ᶜ ⊔
    ⨆ image : S,
      (⨅ x : S, (memberValue S x domain)ᶜ ⊔
        ⨆ y : S, memberValue S y image ⊓ relation x y) ⊓
      (⨅ y : S, (memberValue S y image)ᶜ ⊔
        ⨆ x : S, memberValue S x domain ⊓ relation x y)

theorem realize_collection {n : ℕ} (f : bounded_formula L_ZFC (n + 2)) :
    boolean_realize_sentence S (axiomOfCollection f) =
      ⨅ xs : dvector S n, ⨅ domain : S,
        collectionValue S
          (fun x y => boolean_realize_bounded_formula (S := S) (y :: x :: xs) f []) domain := by
  unfold axiomOfCollection
  rw [realize_universalClosure, iInf_vector_cons]
  apply iInf_congr
  intro xs
  apply iInf_congr
  intro domain
  simp [collectionValue, lattice.imp, var0, var1, var2, var3,
    boolean_realize_bounded_formula_liftAt_insert,
    boolean_realize_bounded_formula_liftAt_insert₂,
    boolean_realize_bounded_formula_liftAt_insert₃,
    collectionSubstFormula, bounded_preformula.fst, bounded_preterm.fst]
  congr 1
  apply iSup_congr
  intro image
  congr 1
  apply iInf_congr
  intro y
  congr 1
  apply iSup_congr
  intro x
  congr 1
  exact collection_substitute_coe S f xs x y image domain _

end Erdos597Object
