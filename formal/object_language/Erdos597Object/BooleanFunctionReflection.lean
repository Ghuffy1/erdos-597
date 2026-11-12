import Erdos597Object.BooleanCountableDecision

set_option backward.isDefEq.respectTransparency false

/-! Ground countable functions in Boolean algebras with a dense omega-closed basis. -/

namespace Erdos597Object.BooleanFunctionReflection

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanFunctionBridge

variable {B : Type} [CompleteBooleanAlgebra B]

theorem checked_exists (domain : pSet) (predicate : bSet B → B)
    (hext : bSet.B_ext predicate) :
    (⨆ i : domain.Type, predicate (bSet.check (domain.Func i))) =
      ⨆ name : bSet B, (name ∈ᴮ bSet.check domain) ⊓ predicate name := by
  cases domain with
  | mk index element =>
    have h := bSet.bounded_exists (bSet.check (PSet.mk index element)) predicate hext
    change (⨆ i : index, (⊤ : B) ⊓ predicate (bSet.check (element i))) = _ at h
    simpa only [top_inf_eq] using h

theorem checked_total_cover (domain codomain : pSet) (f : bSet B) (context : B)
    (hfunction : context ≤ bSet.is_function (bSet.check domain) (bSet.check codomain) f)
    (i : domain.Type) :
    context ≤ ⨆ j : codomain.Type,
      bSet.pair (bSet.check (domain.Func i)) (bSet.check (codomain.Func j)) ∈ᴮ f := by
  have htotal := (bSet.is_total_of_is_function hfunction).trans
    (iInf_le _ (bSet.check (domain.Func i)))
  have hmember : context ≤ bSet.check (domain.Func i) ∈ᴮ bSet.check domain :=
    bSet.check_mem Flypitch.pSet.mem_mk'
  have h := lattice.bv_context_apply htotal hmember
  rw [← checked_exists codomain _
    (bSet.B_ext_pair_right (bSet.B_ext_mem_left f) (bSet.check (domain.Func i)))] at h
  exact h

/-- A total subrelation of a function on the same domain equals that function. -/
theorem function_eq_of_total_subset (domain codomain f g : bSet B) (context : B)
    (hfunction : context ≤ bSet.is_function domain codomain f)
    (htotal : context ≤ bSet.is_total domain codomain g)
    (hsubset : context ≤ g ⊆ᴮ f) : context ≤ g =ᴮ f := by
  apply bSet.subset_ext hsubset
  apply bSet.subset_intro
  intro i
  let base := context ⊓ f.bval i
  have hbase : base ≤ context := inf_le_left
  have hmem : base ≤ f.func i ∈ᴮ f := inf_le_right.trans (bSet.mem.mk' f i)
  have hprod := bSet.mem_of_mem_subset'
    (hbase.trans (bSet.subset_prod_of_is_function hfunction)) hmem
  rw [BooleanFunctionBridge.product_membership] at hprod
  apply (le_inf le_rfl hprod).trans
  apply lattice.bv_cases_right
  intro x
  simp only [inf_iSup_eq]
  apply iSup_le
  intro y
  let part := base ⊓ ((x ∈ᴮ domain) ⊓ ((y ∈ᴮ codomain) ⊓
    (f.func i =ᴮ bSet.pair x y)))
  change part ≤ f.func i ∈ᴮ g
  have hpart : part ≤ context := inf_le_left.trans hbase
  have hx : part ≤ x ∈ᴮ domain := inf_le_right.trans inf_le_left
  have heq : part ≤ f.func i =ᴮ bSet.pair x y :=
    inf_le_right.trans (inf_le_right.trans inf_le_right)
  have hpairF : part ≤ bSet.pair x y ∈ᴮ f :=
    bSet.subst_congr_mem_left' heq (inf_le_left.trans hmem)
  have hcover := lattice.bv_context_apply
    ((hpart.trans htotal).trans (iInf_le _ x)) hx
  apply (le_inf le_rfl hcover).trans
  apply lattice.bv_cases_right
  intro output
  let piece := part ⊓ ((output ∈ᴮ codomain) ⊓ (bSet.pair x output ∈ᴮ g))
  change piece ≤ f.func i ∈ᴮ g
  have hpiece : piece ≤ context := inf_le_left.trans hpart
  have hpairG : piece ≤ bSet.pair x output ∈ᴮ g := inf_le_right.trans inf_le_right
  have hpairF' := bSet.mem_of_mem_subset' (hpiece.trans hsubset) hpairG
  have houtput : piece ≤ y =ᴮ output := bSet.eq_of_is_func_of_eq
    (bSet.is_func_of_is_func' (bSet.is_func'_of_is_function (hpiece.trans hfunction)))
    bSet.bv_refl (inf_le_left.trans hpairF) hpairF'
  have hpairEq : piece ≤ bSet.pair x y =ᴮ bSet.pair x output :=
    bSet.pair_congr bSet.bv_refl houtput
  have hzEq : piece ≤ f.func i =ᴮ bSet.pair x output :=
    bSet.bv_trans (inf_le_left.trans heq) hpairEq
  exact bSet.subst_congr_mem_left' (bSet.bv_symm hzEq) hpairG

/-- A countable function into a checked set is locally a checked ground function. -/
theorem reflect_function (hB : has_dense_omega_closed_subset B) (codomain : pSet)
    (f : bSet B) (context : B) (hne : context ≠ ⊥)
    (hfunction : context ≤ bSet.is_function (bSet.check PSet.omega) (bSet.check codomain) f) :
    ∃ (ground : pSet) (lower : B), lower ≠ ⊥ ∧ lower ≤ context ∧
      lower ≤ bSet.check ground =ᴮ f ∧ Flypitch.pSet.is_func PSet.omega codomain ground := by
  classical
  let weight : Nat → codomain.Type → B := fun n j =>
    bSet.pair (bSet.check (PSet.omega.Func (ULift.up n)))
      (bSet.check (codomain.Func j)) ∈ᴮ f
  have hcover : ∀ n, context ≤ ⨆ j, weight n j :=
    fun n => checked_total_cover PSet.omega codomain f context hfunction (ULift.up n)
  obtain ⟨lower, hlower, hbase, choice, hchoice⟩ :=
    BooleanCountableDecision.decide_countably hB context weight hne hcover
  let ground : pSet := Flypitch.pSet.function.mk
    (fun i : PSet.omega.Type => codomain.Func (choice i.down))
  have hground : Flypitch.pSet.is_func PSet.omega codomain ground := by
    apply Flypitch.pSet.function.mk_is_func
    · intro i
      exact Flypitch.pSet.mem_mk'
    · intro i j hij
      have heq : i = j := Flypitch.pSet.omega_inj hij
      subst j
      exact PSet.Equiv.rfl
  have hsubset : lower ≤ bSet.check ground ⊆ᴮ f := by
    apply bSet.subset_intro
    intro i
    let i' : ground.Type := cast (bSet.check_type (𝔹 := B) (x := ground)) i
    change lower ⊓ (bSet.check ground : bSet B).bval i ≤
      (bSet.check ground : bSet B).func i ∈ᴮ f
    rw [bSet.check_bval, inf_top_eq, bSet.check_func]
    change lower ≤ bSet.check (ground.Func i') ∈ᴮ f
    cases i' with
    | up n =>
      exact bSet.subst_congr_mem_left' (bSet.bv_symm bSet.check_pair) (hchoice n)
  refine ⟨ground, lower, hlower, hbase, ?_, hground⟩
  exact function_eq_of_total_subset _ _ f (bSet.check ground) lower
    (hbase.trans hfunction) (bSet.is_total_of_is_function (bSet.check_is_func hground)) hsubset

theorem functions_subset_ground (hB : has_dense_omega_closed_subset B)
    (codomain : pSet) (context : B) :
    context ≤ bSet.functions (bSet.check PSet.omega) (bSet.check codomain) ⊆ᴮ
      bSet.check (Flypitch.pSet.functions PSet.omega codomain) := by
  apply bSet.subset_intro
  intro i
  let domain := bSet.functions (bSet.check PSet.omega : bSet B) (bSet.check codomain)
  let f := domain.func i
  let part := context ⊓ domain.bval i
  let membership := f ∈ᴮ bSet.check (Flypitch.pSet.functions PSet.omega codomain)
  change part ≤ membership
  by_contra hnot
  have hne : part ⊓ membershipᶜ ≠ ⊥ := by
    intro hzero
    apply hnot
    have hle : part ≤ membershipᶜᶜ :=
      (le_compl_iff_disjoint_right).mpr (disjoint_iff.mpr hzero)
    simpa only [compl_compl] using hle
  have hfunction : part ⊓ membershipᶜ ≤
      bSet.is_function (bSet.check PSet.omega) (bSet.check codomain) f := by
    dsimp [part, domain, f]
    simpa only [bSet.functions_bval] using (inf_le_left.trans inf_le_right)
  obtain ⟨ground, lower, hlower, hbase, heq, hground⟩ :=
    reflect_function hB codomain f (part ⊓ membershipᶜ) hne hfunction
  have hmember : lower ≤ bSet.check ground ∈ᴮ
      bSet.check (Flypitch.pSet.functions PSet.omega codomain) :=
    bSet.check_mem ((Flypitch.pSet.mem_functions_iff).mpr hground)
  have hin : lower ≤ membership := bSet.subst_congr_mem_left' heq hmember
  exact hlower (bot_unique ((le_inf hin (hbase.trans inf_le_right)).trans_eq inf_compl_eq_bot))

theorem functions_eq_ground (hB : has_dense_omega_closed_subset B)
    (codomain : pSet) (context : B) :
    context ≤ bSet.functions (bSet.check PSet.omega) (bSet.check codomain) =ᴮ
      bSet.check (Flypitch.pSet.functions PSet.omega codomain) :=
  bSet.subset_ext (functions_subset_ground hB codomain context) bSet.check_functions_subset_functions

end Erdos597Object.BooleanFunctionReflection
