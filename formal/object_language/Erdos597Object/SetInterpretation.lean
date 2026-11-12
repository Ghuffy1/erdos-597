import Erdos597Object.Semantics
import Erdos597Object.SetCodes

set_option backward.isDefEq.respectTransparency false

/-! The ordinary set interpretation of the graph formulas. -/

namespace Erdos597Object.SetInterpretation

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open Erdos597Object.SetCodes

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

noncomputable section

def setFunction : {n : ℕ} → ZFCFunc n → dvector ZFSet.{0} n → ZFSet.{0}
  | _, .emptyset, [] => ∅
  | _, .pair, x :: y :: [] => ZFSet.pair x y
  | _, .omega, [] => ZFSet.omega
  | _, .powerset, x :: [] => ZFSet.powerset x
  | _, .union, x :: [] => ZFSet.sUnion x

def setRelation : {n : ℕ} → ZFCRel n → dvector ZFSet.{0} n → Prop
  | _, .epsilon, x :: y :: [] => x ∈ y

theorem vector_eq_of_pointwise {α : Type*} {n : ℕ} (x y : dvector α n)
    (h : (x.map2 Eq y).fInf) : x = y := by
  induction x with
  | nil => cases y; rfl
  | cons a xs ih =>
    cases y with
    | cons b ys =>
      simp only [dvector.map2, dvector.fInf] at h
      cases h.1
      exact congrArg (dvector.cons a) (ih ys h.2)

def setStructure : bStructure L_ZFC Prop where
  carrier := ZFSet.{0}
  fun_map := setFunction
  rel_map := setRelation
  eq := Eq
  eq_refl := by intro x; simp
  eq_symm := by intro x y; exact propext eq_comm
  eq_trans := by intro x y z h; exact h.1.trans h.2
  fun_congr := by
    intro n f x y h
    exact congrArg (setFunction f) (vector_eq_of_pointwise x y h)
  rel_congr := by
    intro n r x y h
    have heq := vector_eq_of_pointwise x y h.1
    simpa only [heq] using h.2

@[simp] theorem memberValue_set (x y : ZFSet.{0}) :
    memberValue setStructure x y = (x ∈ y) := rfl

@[simp] theorem pairValue_set (x y : ZFSet.{0}) :
    pairValue setStructure x y = ZFSet.pair x y := rfl

@[simp] theorem edgeValue_set (r x y : ZFSet.{0}) :
    edgeValue setStructure r x y = (ZFSet.pair x y ∈ r) := rfl

@[simp] theorem eqValue_set (x y : ZFSet.{0}) :
    setStructure.eq x y = (x = y) := rfl

theorem relationBetweenValue_set (domain codomain relation : ZFSet.{0}) :
    relationBetweenValue setStructure domain codomain relation ↔
      ∀ entry ∈ relation, ∃ x ∈ domain, ∃ y ∈ codomain,
        entry = ZFSet.pair x y := by
  simp [relationBetweenValue, or_iff_not_imp_left]
  rfl

theorem edgeSet_relationBetween {n : ℕ} (G : SimpleGraph (Fin n)) :
    relationBetweenValue setStructure (naturalSet n) (naturalSet n) (edgeSet G) := by
  rw [relationBetweenValue_set]
  intro entry hentry
  obtain ⟨⟨⟨i, j⟩, hij⟩, rfl⟩ := ZFSet.mem_range.mp hentry
  exact ⟨naturalSet i.val, (mem_naturalSet _ _).mpr ⟨i.val, i.isLt, rfl⟩,
    naturalSet j.val, (mem_naturalSet _ _).mpr ⟨j.val, j.isLt, rfl⟩, rfl⟩

theorem edgeSet_irreflexive {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ x ∈ naturalSet n, ¬ ZFSet.pair x x ∈ edgeSet G := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := (mem_naturalSet x n).mp hx
  rw [pair_mem_edgeSet G (⟨i, hi⟩ : Fin n) ⟨i, hi⟩]
  exact G.loopless.irrefl _

theorem edgeSet_symmetric {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ x ∈ naturalSet n, ∀ y ∈ naturalSet n,
      ZFSet.pair x y ∈ edgeSet G ↔ ZFSet.pair y x ∈ edgeSet G := by
  intro x hx y hy
  obtain ⟨i, hi, rfl⟩ := (mem_naturalSet x n).mp hx
  obtain ⟨j, hj, rfl⟩ := (mem_naturalSet y n).mp hy
  simpa only [pair_mem_edgeSet G (⟨i, hi⟩ : Fin n) ⟨j, hj⟩,
    pair_mem_edgeSet G (⟨j, hj⟩ : Fin n) ⟨i, hi⟩] using
      G.adj_comm ⟨i, hi⟩ ⟨j, hj⟩

theorem graphValue_set (vertices edges : ZFSet.{0}) :
    graphValue setStructure vertices edges ↔
      (∀ entry ∈ edges, ∃ x ∈ vertices, ∃ y ∈ vertices,
        entry = ZFSet.pair x y) ∧
      (∀ x ∈ vertices, ¬ ZFSet.pair x x ∈ edges) ∧
      (∀ x ∈ vertices, ∀ y ∈ vertices,
        ZFSet.pair x y ∈ edges ↔ ZFSet.pair y x ∈ edges) := by
  simp [graphValue, relationBetweenValue_set, or_iff_not_imp_left,
    iff_def, and_assoc]
  tauto

theorem edgeSet_graph {n : ℕ} (G : SimpleGraph (Fin n)) :
    graphValue setStructure (naturalSet n) (edgeSet G) := by
  rw [graphValue_set]
  exact ⟨(relationBetweenValue_set _ _ _).mp (edgeSet_relationBetween G),
    edgeSet_irreflexive G, edgeSet_symmetric G⟩

theorem cliqueFree_four_iff {V : Type*} (G : SimpleGraph V) :
    G.CliqueFree 4 ↔ ∀ a b c d : V,
      ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧
        G.Adj b c ∧ G.Adj b d ∧ G.Adj c d) := by
  classical
  constructor
  · intro hG a b c d h
    let f : Fin 4 → V := ![a, b, c, d]
    have hadj : ∀ i j : Fin 4, i ≠ j → G.Adj (f i) (f j) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [f, G.adj_comm]
    let hom : (⊤ : SimpleGraph (Fin 4)) →g G :=
      ⟨f, fun hij => hadj _ _ hij⟩
    have hinj : Function.Injective f := by
      intro i j heq
      by_contra hne
      exact (hadj i j hne).ne heq
    exact (hom.toCopy hinj).isContained.not_cliqueFree hG
  · intro h
    by_contra hG
    let f := G.topEmbeddingOfNotCliqueFree hG
    have hadj (i j : Fin 4) (hij : i ≠ j) : G.Adj (f i) (f j) :=
      f.map_rel_iff.mpr hij
    exact h (f 0) (f 1) (f 2) (f 3)
      ⟨hadj 0 1 (by decide), hadj 0 2 (by decide), hadj 0 3 (by decide),
        hadj 1 2 (by decide), hadj 1 3 (by decide), hadj 2 3 (by decide)⟩

theorem cliqueFreeFourValue_set (vertices edges : ZFSet.{0}) :
    cliqueFreeFourValue setStructure vertices edges ↔
      ∀ a ∈ vertices, ∀ b ∈ vertices, ∀ c ∈ vertices, ∀ d ∈ vertices,
        ¬ (ZFSet.pair a b ∈ edges ∧ ZFSet.pair a c ∈ edges ∧
          ZFSet.pair a d ∈ edges ∧ ZFSet.pair b c ∈ edges ∧
          ZFSet.pair b d ∈ edges ∧ ZFSet.pair c d ∈ edges) := by
  simp [cliqueFreeFourValue, fourCliqueValue, or_iff_not_imp_left]
  rfl

theorem edgeSet_cliqueFree_iff {n : ℕ} (G : SimpleGraph (Fin n)) :
    cliqueFreeFourValue setStructure (naturalSet n) (edgeSet G) ↔ G.CliqueFree 4 := by
  rw [cliqueFreeFourValue_set, cliqueFree_four_iff]
  constructor
  · intro h a b c d
    have hv (i : Fin n) : naturalSet i.val ∈ naturalSet n :=
      (mem_naturalSet _ _).mpr ⟨i.val, i.isLt, rfl⟩
    simpa only [pair_mem_edgeSet] using
      h _ (hv a) _ (hv b) _ (hv c) _ (hv d)
  · intro h a ha b hb c hc d hd
    obtain ⟨i, hi, rfl⟩ := (mem_naturalSet a n).mp ha
    obtain ⟨j, hj, rfl⟩ := (mem_naturalSet b n).mp hb
    obtain ⟨k, hk, rfl⟩ := (mem_naturalSet c n).mp hc
    obtain ⟨l, hl, rfl⟩ := (mem_naturalSet d n).mp hd
    simpa only [pair_mem_edgeSet G (⟨i, hi⟩ : Fin n) ⟨j, hj⟩,
      pair_mem_edgeSet G (⟨i, hi⟩ : Fin n) ⟨k, hk⟩,
      pair_mem_edgeSet G (⟨i, hi⟩ : Fin n) ⟨l, hl⟩,
      pair_mem_edgeSet G (⟨j, hj⟩ : Fin n) ⟨k, hk⟩,
      pair_mem_edgeSet G (⟨j, hj⟩ : Fin n) ⟨l, hl⟩,
      pair_mem_edgeSet G (⟨k, hk⟩ : Fin n) ⟨l, hl⟩] using
      h ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ ⟨l, hl⟩

end

end Erdos597Object.SetInterpretation
