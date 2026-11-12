import Erdos597Object.FinitePresentation

set_option backward.isDefEq.respectTransparency false

/-! Set-coded functions and their ordinary functional interpretation. -/

namespace Erdos597Object.SetFunctions

open Erdos597Object.SetInterpretation

noncomputable section

abbrev Members (x : ZFSet.{0}) := {a : ZFSet.{0} // a ∈ x}

theorem singleValuedValue_set (relation : ZFSet.{0}) :
    singleValuedValue setStructure relation ↔
      ∀ x y z, ZFSet.pair x y ∈ relation → ZFSet.pair x z ∈ relation → y = z := by
  simp [singleValuedValue, or_iff_not_imp_left]
  rfl

theorem totalOnValue_set (domain codomain relation : ZFSet.{0}) :
    totalOnValue setStructure domain codomain relation ↔
      ∀ x ∈ domain, ∃ y ∈ codomain, ZFSet.pair x y ∈ relation := by
  simp [totalOnValue, or_iff_not_imp_left]
  rfl

theorem injectiveValue_set (relation : ZFSet.{0}) :
    injectiveValue setStructure relation ↔
      ∀ x y z, ZFSet.pair x z ∈ relation → ZFSet.pair y z ∈ relation → x = y := by
  simp [injectiveValue, or_iff_not_imp_left]
  rfl

theorem functionFromValue_iff_isFunc (domain codomain relation : ZFSet.{0}) :
    functionFromValue setStructure domain codomain relation ↔
      ZFSet.IsFunc domain codomain relation := by
  change (relationBetweenValue setStructure domain codomain relation ∧
    singleValuedValue setStructure relation ∧
    totalOnValue setStructure domain codomain relation) ↔ _
  rw [relationBetweenValue_set, singleValuedValue_set, totalOnValue_set]
  constructor
  · rintro ⟨hbetween, hsingle, htotal⟩
    refine ⟨?_, ?_⟩
    · intro entry hentry
      exact ZFSet.mem_prod.mpr (hbetween entry hentry)
    · intro x hx
      obtain ⟨y, _, hy⟩ := htotal x hx
      exact ⟨y, hy, fun z hz => hsingle x z y hz hy⟩
  · rintro ⟨hsubset, hfunc⟩
    refine ⟨?_, ?_, ?_⟩
    · intro entry hentry
      exact ZFSet.mem_prod.mp (hsubset hentry)
    · intro x y z hxy hxz
      have hx := (ZFSet.pair_mem_prod.mp (hsubset hxy)).1
      obtain ⟨w, _, hw⟩ := hfunc x hx
      exact (hw y hxy).trans (hw z hxz).symm
    · intro x hx
      obtain ⟨y, hy, _⟩ := hfunc x hx
      exact ⟨y, (ZFSet.pair_mem_prod.mp (hsubset hy)).2, hy⟩

def functionGraph {domain codomain : ZFSet.{0}}
    (f : Members domain → Members codomain) : ZFSet.{0} :=
  ZFSet.range fun x : Members domain => ZFSet.pair x.val (f x).val

theorem pair_mem_functionGraph {domain codomain : ZFSet.{0}}
    (f : Members domain → Members codomain) (x y : ZFSet.{0}) :
    ZFSet.pair x y ∈ functionGraph f ↔
      ∃ hx : x ∈ domain, (f ⟨x, hx⟩).val = y := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := ZFSet.mem_range.mp h
    obtain ⟨hx, hy⟩ := ZFSet.pair_inj.mp hz
    subst x
    exact ⟨z.property, hy⟩
  · rintro ⟨hx, hy⟩
    exact ZFSet.mem_range.mpr ⟨⟨x, hx⟩, congrArg (ZFSet.pair x) hy⟩

theorem members_pair_mem_functionGraph {domain codomain : ZFSet.{0}}
    (f : Members domain → Members codomain) (x : Members domain) (y : Members codomain) :
    ZFSet.pair x.val y.val ∈ functionGraph f ↔ f x = y := by
  rw [pair_mem_functionGraph]
  constructor
  · rintro ⟨_, h⟩
    exact Subtype.ext h
  · intro h
    exact ⟨x.property, congrArg Subtype.val h⟩

theorem functionGraph_functionFrom {domain codomain : ZFSet.{0}}
    (f : Members domain → Members codomain) :
    functionFromValue setStructure domain codomain (functionGraph f) := by
  change relationBetweenValue setStructure domain codomain (functionGraph f) ∧
    singleValuedValue setStructure (functionGraph f) ∧
    totalOnValue setStructure domain codomain (functionGraph f)
  rw [relationBetweenValue_set, singleValuedValue_set, totalOnValue_set]
  refine ⟨?_, ?_, ?_⟩
  · intro entry hentry
    obtain ⟨x, rfl⟩ := ZFSet.mem_range.mp hentry
    exact ⟨x.val, x.property, (f x).val, (f x).property, rfl⟩
  · intro x y z hxy hxz
    obtain ⟨hx, hy⟩ := (pair_mem_functionGraph f x y).mp hxy
    obtain ⟨_, hz⟩ := (pair_mem_functionGraph f x z).mp hxz
    exact hy.symm.trans hz
  · intro x hx
    exact ⟨(f ⟨x, hx⟩).val, (f ⟨x, hx⟩).property,
      (pair_mem_functionGraph f _ _).mpr ⟨hx, rfl⟩⟩

theorem functionGraph_injective_iff {domain codomain : ZFSet.{0}}
    (f : Members domain → Members codomain) :
    injectiveValue setStructure (functionGraph f) ↔ Function.Injective f := by
  rw [injectiveValue_set]
  constructor
  · intro h x y hxy
    apply Subtype.ext
    exact h x.val y.val (f x).val
      ((members_pair_mem_functionGraph f x (f x)).mpr rfl)
      ((members_pair_mem_functionGraph f y (f x)).mpr hxy.symm)
  · intro h x y z hxz hyz
    obtain ⟨hx, hfx⟩ := (pair_mem_functionGraph f x z).mp hxz
    obtain ⟨hy, hfy⟩ := (pair_mem_functionGraph f y z).mp hyz
    exact congrArg Subtype.val (h (Subtype.ext (hfx.trans hfy.symm)))

theorem exists_image {domain codomain relation : ZFSet.{0}}
    (h : functionFromValue setStructure domain codomain relation) (x : Members domain) :
    ∃ y : Members codomain, ZFSet.pair x.val y.val ∈ relation := by
  have htotal : totalOnValue setStructure domain codomain relation := h.2.2
  obtain ⟨y, hy, hxy⟩ := (totalOnValue_set _ _ _).mp htotal x.val x.property
  exact ⟨⟨y, hy⟩, hxy⟩

def evaluate {domain codomain relation : ZFSet.{0}}
    (h : functionFromValue setStructure domain codomain relation) :
    Members domain → Members codomain :=
  fun x => (exists_image h x).choose

theorem evaluate_spec {domain codomain relation : ZFSet.{0}}
    (h : functionFromValue setStructure domain codomain relation) (x : Members domain) :
    ZFSet.pair x.val (evaluate h x).val ∈ relation :=
  (exists_image h x).choose_spec

theorem members_pair_mem_iff_evaluate {domain codomain relation : ZFSet.{0}}
    (h : functionFromValue setStructure domain codomain relation)
    (x : Members domain) (y : Members codomain) :
    ZFSet.pair x.val y.val ∈ relation ↔ evaluate h x = y := by
  constructor
  · intro hxy
    apply Subtype.ext
    exact (singleValuedValue_set _).mp h.2.1 _ _ _ (evaluate_spec h x) hxy
  · intro hxy
    rw [← hxy]
    exact evaluate_spec h x

theorem functionGraph_evaluate {domain codomain relation : ZFSet.{0}}
    (h : functionFromValue setStructure domain codomain relation) :
    functionGraph (evaluate h) = relation := by
  apply ZFSet.ext
  intro entry
  constructor
  · intro hentry
    obtain ⟨x, rfl⟩ := ZFSet.mem_range.mp hentry
    exact evaluate_spec h x
  · intro hentry
    obtain ⟨x, hx, y, hy, rfl⟩ := (relationBetweenValue_set _ _ _).mp h.1 entry hentry
    have hxy := (members_pair_mem_iff_evaluate h ⟨x, hx⟩ ⟨y, hy⟩).mp hentry
    exact (members_pair_mem_functionGraph (evaluate h) ⟨x, hx⟩ ⟨y, hy⟩).mpr hxy

theorem evaluate_functionGraph {domain codomain : ZFSet.{0}}
    (f : Members domain → Members codomain) :
    evaluate (functionGraph_functionFrom f) = f := by
  funext x
  exact (members_pair_mem_functionGraph f x _).mp
    (evaluate_spec (functionGraph_functionFrom f) x) |>.symm

theorem preservesRelationValue_set (source target mapping : ZFSet.{0}) :
    preservesRelationValue setStructure source target mapping ↔
      ∀ x y a b, ZFSet.pair x a ∈ mapping → ZFSet.pair y b ∈ mapping →
        ZFSet.pair x y ∈ source → ZFSet.pair a b ∈ target := by
  simp [preservesRelationValue, or_iff_not_imp_left]
  rfl

theorem preservesRelation_functionGraph_iff {domain codomain : ZFSet.{0}}
    (f : Members domain → Members codomain) (source target : ZFSet.{0}) :
    preservesRelationValue setStructure source target (functionGraph f) ↔
      ∀ x y : Members domain, ZFSet.pair x.val y.val ∈ source →
        ZFSet.pair (f x).val (f y).val ∈ target := by
  rw [preservesRelationValue_set]
  constructor
  · intro h x y hxy
    exact h _ _ _ _ ((members_pair_mem_functionGraph f x (f x)).mpr rfl)
      ((members_pair_mem_functionGraph f y (f y)).mpr rfl) hxy
  · intro h x y a b hxa hyb hxy
    obtain ⟨hx, hfa⟩ := (pair_mem_functionGraph f x a).mp hxa
    obtain ⟨hy, hfb⟩ := (pair_mem_functionGraph f y b).mp hyb
    simpa only [hfa, hfb] using h ⟨x, hx⟩ ⟨y, hy⟩ hxy

theorem blueCopyValue_iff (domain codomain source target : ZFSet.{0}) :
    blueCopyValue setStructure domain codomain source target ↔
      ∃ f : Members domain → Members codomain, Function.Injective f ∧
        ∀ x y : Members domain, ZFSet.pair x.val y.val ∈ source →
          ZFSet.pair (f x).val (f y).val ∈ target := by
  rw [blueCopyValue, iSup_Prop_eq]
  constructor
  · rintro ⟨mapping, hfunc, hinj, hpres⟩
    refine ⟨evaluate hfunc, ?_, ?_⟩
    · apply (functionGraph_injective_iff _).mp
      simpa only [functionGraph_evaluate] using hinj
    · apply (preservesRelation_functionGraph_iff _ _ _).mp
      simpa only [functionGraph_evaluate] using hpres
  · rintro ⟨f, hinj, hpres⟩
    exact ⟨functionGraph f, functionGraph_functionFrom f,
      (functionGraph_injective_iff f).mpr hinj,
      (preservesRelation_functionGraph_iff f source target).mpr hpres⟩

end

end Erdos597Object.SetFunctions
