import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Push
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Order.Prod.Lex.Basic
import PartiteConstruction.Relational.FreeAmalgamationClass
import PartiteConstruction.Ramsey.FreeAmalgamation
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finset.Sort
import Mathlib.Order.PFilter
import Mathlib.Order.Zorn
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős 597, ambient graph-partition theorems

This file proves the unrestricted graph assertion false in ZFC-style ambient
mathematics, constructs a fixed finite K₄-free counterexample under CH, and
proves the finite-target assertion under Martin's axiom at aleph-one.

The companion object-language project constructs positive and negative models
and proves the ZFC independence conclusion. Its final endpoints are exported
by `Erdos597Object.Solution`.

The original graph-target partition definition follows Formal Conjectures,
commit dc3e07b902f6b2df333e2f90674c73232108d5dc, under Apache 2.0.
The construction credits Baumgartner–Hajnal and Chen–Garti–Weinert.
The ordering-property argument credits Nešetřil–Rödl and uses Jan Hubička's
relational Ramsey formalization, pinned in the project dependency records.
The positive theorem follows Baumgartner's 1989 proof of weak independence
and the finite-condition forcing argument. The infinite Ramsey proof uses
the recursive reservoir approach, also used in Ching-Tsun Chou's pair proof.
-/

/-!
# Definitions and the unrestricted nested-interval coloring

The carrier `One` is the standard first uncountable ordinal. The pair carrier
uses its row-first lexicographic order. A later module transports this carrier
to the ordinal square used in the original problem.

The nested-interval support follows Baumgartner--Hajnal and
Chen--Garti--Weinert. The unrestricted counterexample uses every nested pair.
-/

open Cardinal Ordinal Set Function
open scoped Cardinal Ordinal

namespace Erdos597

abbrev One := (ω₁ : Ordinal.{0}).ToType
abbrev Vertex := One × One

noncomputable def zeroOne : One :=
  Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩

instance : Uncountable One := by
  apply Cardinal.aleph0_lt_mk_iff.mp
  simp [One]

theorem one_card : #One = ℵ₁ := by
  simp [One]

def RowLt (x y : Vertex) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

def BlockLt (x y : ℕ × One) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

def Nested (x y : Vertex) : Prop :=
  x.1 < y.1 ∧ y.1 < y.2 ∧ y.2 < x.2

def nestedGraph : SimpleGraph Vertex where
  Adj x y := Nested x y ∨ Nested y x
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h
    · exact (lt_irrefl x.1) h.1
    · exact (lt_irrefl x.1) h.1⟩

def HasWeakCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Injective f ∧ ∀ a b, G.Adj a b → H.Adj (f a) (f b)

def HasInfiniteBiclique {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ A B : Set V, Disjoint A B ∧ A.Infinite ∧ B.Infinite ∧
    ∀ a ∈ A, ∀ b ∈ B, G.Adj a b

theorem countable_initial_segment (b : One) : (Iic b).Countable := by
  have hcard : #(Iio b) < ℵ₁ := by
    have h := Cardinal.mk_Iio_lt b (by simp [One])
    simpa [One] using h
  have hc : (Iio b).Countable :=
    Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.lt_aleph_one_iff.mp hcard)
  have heq : Iic b = insert b (Iio b) := by
    ext x
    simp only [mem_Iic, mem_insert_iff, mem_Iio]
    exact le_iff_eq_or_lt
  rw [heq]
  exact hc.insert b

theorem no_injection_bounded_rectangle (f : One → Vertex) (hf : Injective f)
    (a b : One) (hbound : ∀ x, (f x).1 ≤ a ∧ (f x).2 ≤ b) : False := by
  classical
  have : Countable (Iic a) := (countable_initial_segment a).to_subtype
  have : Countable (Iic b) := (countable_initial_segment b).to_subtype
  let g : One → (Iic a) × (Iic b) :=
    fun x => (⟨(f x).1, (hbound x).1⟩, ⟨(f x).2, (hbound x).2⟩)
  have hg : Injective g := by
    intro x y hxy
    apply hf
    apply Prod.ext
    · exact congrArg (fun z : (Iic a) × (Iic b) => z.1.val) hxy
    · exact congrArg (fun z : (Iic a) × (Iic b) => z.2.val) hxy
  have : Countable One := hg.countable
  exact not_countable (α := One) inferInstance

theorem row_le_of_rowLt {x y : Vertex} (h : RowLt x y) : x.1 ≤ y.1 := by
  rcases h with h | h
  · exact h.le
  · exact h.1.le

theorem no_red_block_embedding (f : (ℕ × One) → Vertex)
    (hf : Injective f)
    (horder : ∀ x y, BlockLt x y → RowLt (f x) (f y))
    (hred : ∀ x y, ¬ nestedGraph.Adj (f x) (f y)) : False := by
  have hfirst (x : One) : (f (1, x)).1 ≤ (f (2, zeroOne)).1 :=
    row_le_of_rowLt (horder _ _ (Or.inl (by change (1 : ℕ) < 2; decide)))
  have hactive : ∃ x : One, (f (1, x)).1 < (f (1, x)).2 := by
    by_contra h
    push Not at h
    apply no_injection_bounded_rectangle (fun x => f (1, x))
      (fun x y hxy => by simpa using hf hxy)
      (f (2, zeroOne)).1 (f (2, zeroOne)).1
    intro x
    exact ⟨hfirst x, (h x).trans (hfirst x)⟩
  obtain ⟨y, hy⟩ := hactive
  apply no_injection_bounded_rectangle (fun x => f (0, x))
    (fun x y hxy => by simpa using hf hxy)
    (f (1, y)).1 (f (1, y)).2
  intro x
  have hxy := horder (0, x) (1, y) (Or.inl (by change (0 : ℕ) < 1; decide))
  refine ⟨row_le_of_rowLt hxy, ?_⟩
  by_contra hcolumn
  have hlarge : (f (1, y)).2 < (f (0, x)).2 := lt_of_not_ge hcolumn
  rcases hxy with hrow | ⟨hrow, hcol⟩
  · exact hred (0, x) (1, y) (Or.inl ⟨hrow, hy, hlarge⟩)
  · exact (not_lt_of_ge hlarge.le) hcol

end Erdos597

/-! # The uncountably branching tree used as an omitted target -/

open Cardinal Ordinal Set Function
open scoped Cardinal Ordinal

namespace Erdos597

abbrev TreeVertex := List One

def branchingTree : SimpleGraph TreeVertex where
  Adj x y := (∃ a : One, y = x ++ [a]) ∨ (∃ a : One, x = y ++ [a])
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨a, h⟩ | ⟨a, h⟩ <;>
      have hlen := congrArg List.length h <;> simp at hlen⟩

theorem branchingTree_card : #TreeVertex = ℵ₁ := by
  rw [TreeVertex, Cardinal.mk_list_eq_mk, one_card]

def treeColoring : branchingTree.Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk (fun x => ⟨x.length % 2, Nat.mod_lt _ (by decide)⟩) (by
    intro x y h hcolors
    have hmod := congrArg Fin.val hcolors
    rcases h with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
      simp only [List.length_append, List.length_singleton] at hmod <;> omega)

theorem branchingTree_cliqueFree : branchingTree.CliqueFree 4 :=
  (show branchingTree.Colorable 2 from ⟨treeColoring⟩).cliqueFree (by decide)

theorem parent_of_adj_of_length_le {x y : TreeVertex}
    (h : branchingTree.Adj x y) (hlen : x.length ≤ y.length) : x = y.dropLast := by
  rcases h with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · simp
  · simp only [List.length_append, List.length_singleton] at hlen
    omega

theorem common_neighbor_unique {x y z w : TreeVertex} (hne : x ≠ y)
    (hxz : branchingTree.Adj x z) (hyz : branchingTree.Adj y z)
    (hxw : branchingTree.Adj x w) (hyw : branchingTree.Adj y w) : z = w := by
  wlog hxy : x.length ≤ y.length
  · exact this hne.symm hyz hxz hyw hxw (le_of_not_ge hxy)
  have hz : z.length ≤ y.length := by
    by_contra h
    have hy : y.length ≤ z.length := le_of_lt (lt_of_not_ge h)
    exact hne ((parent_of_adj_of_length_le hxz (hxy.trans hy)).trans
      (parent_of_adj_of_length_le hyz hy).symm)
  have hw : w.length ≤ y.length := by
    by_contra h
    have hy : y.length ≤ w.length := le_of_lt (lt_of_not_ge h)
    exact hne ((parent_of_adj_of_length_le hxw (hxy.trans hy)).trans
      (parent_of_adj_of_length_le hyw hy).symm)
  exact (parent_of_adj_of_length_le hyz.symm hz).trans
    (parent_of_adj_of_length_le hyw.symm hw).symm

theorem branchingTree_no_biclique : ¬ HasInfiniteBiclique branchingTree := by
  rintro ⟨A, B, _, hA, hB, hedge⟩
  obtain ⟨x, hx, y, hy, hne⟩ := hA.nontrivial
  have hsub : B.Subsingleton := by
    intro z hz w hw
    exact common_neighbor_unique hne (hedge x hx z hz) (hedge y hy z hz)
      (hedge x hx w hw) (hedge y hy w hw)
  exact hB hsub.finite

theorem branchingTree_no_weakCopy : ¬ HasWeakCopy branchingTree nestedGraph := by
  rintro ⟨f, hf, hedge⟩
  let rows : Set One := Set.range (fun t : TreeVertex => (f t).1)
  have hrows : rows.Nonempty := ⟨(f []).1, [], rfl⟩
  obtain ⟨a, ⟨t, rfl⟩, hmin⟩ := wellFounded_lt.has_min rows hrows
  apply no_injection_bounded_rectangle (fun x => f (t ++ [x]))
    (by
      intro x y h
      have hlist := List.append_cancel_left (hf h)
      simpa using hlist)
    (f t).2 (f t).2
  intro x
  have hx := hedge t (t ++ [x]) (Or.inl ⟨x, rfl⟩)
  rcases hx with hx | hx
  · exact ⟨hx.2.1.le.trans hx.2.2.le, hx.2.2.le⟩
  · exact False.elim (hmin (f (t ++ [x])).1 ⟨t ++ [x], rfl⟩ hx.1)

end Erdos597

/-!
# The unrestricted clause of Erdős problem 597

The definition of `OrdinalGraphRamsey` is the literal graph-target definition in
the Formal Conjectures statement of problem 597. The blue copy is injective and
edge-preserving. The map is allowed to ignore the order and to create extra edges.

The nested-interval edge relation comes from the classical ordinal partition
constructions. The omitted target here is the tree of finite sequences in ω₁.
-/

open Cardinal Ordinal Set Function
open scoped Cardinal Ordinal

namespace Erdos597

def OrdinalGraphRamsey {W : Type*} (α β : Ordinal.{0}) (G : SimpleGraph W) : Prop :=
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    (∃ s, red.IsClique s ∧ typeLT s = β) ∨
    (∃ f : W → α.ToType, Function.Injective f ∧
      ∀ a b, G.Adj a b → blue.Adj (f a) (f b))

abbrev Square := ((ω₁ : Ordinal.{0}) ^ (2 : ℕ)).ToType

private theorem row_relation {x y : Vertex} :
    Prod.Lex (· < ·) (· < ·) x y ↔ RowLt x y := by
  exact Prod.lex_def

private theorem block_relation {x y : ℕ × One} :
    Prod.Lex (· < ·) (· < ·) x y ↔ BlockLt x y := by
  exact Prod.lex_def

private theorem square_type :
    type (Prod.Lex (· < ·) (· < ·) : Vertex → Vertex → Prop) =
      (ω₁ : Ordinal.{0}) ^ (2 : ℕ) := by
  rw [type_prod_lex, type_toType, pow_two]

private theorem block_type :
    type (Prod.Lex (· < ·) (· < ·) : (ℕ × One) → (ℕ × One) → Prop) =
      (ω₁ : Ordinal.{0}) * ω := by
  rw [type_prod_lex, type_toType, type_nat_lt]

noncomputable def squareIso :
    ((· < ·) : Square → Square → Prop) ≃r
      (Prod.Lex (· < ·) (· < ·) : Vertex → Vertex → Prop) :=
  Classical.choice (type_eq.mp (by rw [type_toType, square_type]))

def blueSquare : SimpleGraph Square where
  Adj x y := nestedGraph.Adj (squareIso x) (squareIso y)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => nestedGraph.loopless.irrefl _ h⟩

theorem blueSquare_no_red_block :
    ¬ ∃ s, blueSquareᶜ.IsClique s ∧ typeLT s = (ω₁ : Ordinal.{0}) * ω := by
  rintro ⟨s, hs, htype⟩
  obtain ⟨e⟩ : Nonempty
      ((Prod.Lex (· < ·) (· < ·) : (ℕ × One) → (ℕ × One) → Prop) ≃r
        ((· < ·) : s → s → Prop)) :=
    type_eq.mp (block_type.trans htype.symm)
  let f : (ℕ × One) → Vertex := fun x => squareIso (e x).val
  have hf : Injective f :=
    squareIso.injective.comp (Subtype.val_injective.comp e.injective)
  apply no_red_block_embedding f hf
  · intro x y hxy
    exact row_relation.mp (squareIso.map_rel_iff.mpr
      (e.map_rel_iff.mpr (block_relation.mpr hxy)))
  · intro x y hblue
    have hne : (e x).val ≠ (e y).val := by
      intro h
      have heq : x = y := e.injective (Subtype.ext h)
      subst y
      exact nestedGraph.loopless.irrefl _ hblue
    exact (SimpleGraph.compl_adj _ _ _).mp
      (hs (e x).property (e y).property hne) |>.2 hblue

theorem blueSquare_no_tree : ¬ HasWeakCopy branchingTree blueSquare := by
  rintro ⟨f, hf, hedge⟩
  apply branchingTree_no_weakCopy
  exact ⟨fun x => squareIso (f x), squareIso.injective.comp hf, hedge⟩

theorem tree_partition_failure :
    ¬ OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ))
      ((ω₁ : Ordinal.{0}) * ω) branchingTree := by
  intro h
  rcases h blueSquareᶜ blueSquare isCompl_compl.symm with hred | hblue
  · exact blueSquare_no_red_block hred
  · exact blueSquare_no_tree hblue

/-- A concrete admissible counterexample to the unrestricted assertion. -/
theorem unrestricted_counterexample :
    ∃ (W : Type) (G : SimpleGraph W), #W ≤ ℵ₁ ∧ G.CliqueFree 4 ∧
      (¬ ∃ A B : Set W, Disjoint A B ∧ A.Infinite ∧ B.Infinite ∧
        ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) ∧
      ¬ OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ))
        ((ω₁ : Ordinal.{0}) * ω) G := by
  exact ⟨TreeVertex, branchingTree, branchingTree_card.le,
    branchingTree_cliqueFree, branchingTree_no_biclique, tree_partition_failure⟩

/-- The negation of the exact universal assertion in the original first clause. -/
theorem erdos_597_disproved :
    ¬ ∀ (W : Type) (G : SimpleGraph W), #W ≤ ℵ₁ → G.CliqueFree 4 →
      (¬ ∃ A B : Set W, Disjoint A B ∧ A.Infinite ∧ B.Infinite ∧
        ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) →
      OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ))
        ((ω₁ : Ordinal.{0}) * ω) G := by
  intro h
  exact tree_partition_failure
    (h TreeVertex branchingTree branchingTree_card.le branchingTree_cliqueFree
      branchingTree_no_biclique)

end Erdos597

/-!
# The six-vertex obstruction in the finite-target argument

This file checks the finite combinatorial implication from the three selection
rules in the proposed CH construction. `SelectionRules` explicitly records
those rules. Existence of a construction satisfying them, and existence of a
finite graph with the ordering property, are separate obligations.

The ordering-property method is due to Nešetřil and Rödl (1978). The application
here uses the specified order on the complete tripartite graph K₂,₂,₂.
-/

open Cardinal Ordinal Set Function
open scoped Cardinal Ordinal

namespace Erdos597

/-- The vertices, in order, are x, y, p, q, z, w. -/
def obstructionPart (i : Fin 6) : Fin 3 :=
  if i = 0 ∨ i = 2 then 0 else if i = 1 ∨ i = 4 then 1 else 2

def obstructionGraph : SimpleGraph (Fin 6) where
  Adj i j := obstructionPart i ≠ obstructionPart j
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

instance : DecidableRel obstructionGraph.Adj := fun i j =>
  inferInstanceAs (Decidable (obstructionPart i ≠ obstructionPart j))

def obstructionColoring : obstructionGraph.Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk obstructionPart (fun h => h)

theorem obstructionGraph_cliqueFree : obstructionGraph.CliqueFree 4 :=
  (show obstructionGraph.Colorable 3 from ⟨obstructionColoring⟩).cliqueFree (by decide)

theorem obstructionGraph_consecutive (i : Fin 5) :
    obstructionGraph.Adj i.castSucc i.succ := by
  revert i
  decide

/-- The local rules used by the six-vertex contradiction. -/
structure SelectionRules where
  out : Vertex → Vertex → Prop
  stage : Vertex → Vertex → ℕ
  weight : One → One → ℕ
  nested : ∀ {x y}, out x y → Nested x y
  reversal : ∀ {x u v}, out x u → out x v → out u v →
    stage x v < stage x u
  sourceWeight : ∀ {x u v}, out x u → out x v →
    stage x v < stage x u → u.1 < v.1 → weight v.1 x.1 < weight v.1 u.1
  earlierWeight : ∀ {x u v w}, out x u → out x v → out x w →
    stage x w < stage x u → stage x v < stage x u →
    u.1 < w.1 → v.1 < w.1 → weight w.1 v.1 < weight w.1 u.1

def SelectionRules.graph (R : SelectionRules) : SimpleGraph Vertex where
  Adj x y := R.out x y ∨ R.out y x
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by
    rcases h with h | h
    · exact (lt_irrefl _) (R.nested h).1
    · exact (lt_irrefl _) (R.nested h).1⟩

theorem SelectionRules.forward (R : SelectionRules) {x y : Vertex}
    (hxy : R.graph.Adj x y) (hrow : x.1 < y.1) : R.out x y := by
  rcases hxy with hxy | hyx
  · exact hxy
  · exact False.elim (lt_asymm hrow (R.nested hyx).1)

theorem SelectionRules.triangle_weight (R : SelectionRules) {u v w : Vertex}
    (huv : R.graph.Adj u v) (huw : R.graph.Adj u w) (hvw : R.graph.Adj v w)
    (hr : u.1 < v.1) (hs : v.1 < w.1) :
    R.weight w.1 u.1 < R.weight w.1 v.1 := by
  have huv' := R.forward huv hr
  have huw' := R.forward huw (hr.trans hs)
  have hvw' := R.forward hvw hs
  exact R.sourceWeight huv' huw' (R.reversal huv' huw' hvw') hs

/-- No row-increasing, edge-preserving map of the ordered K₂,₂,₂ exists. -/
theorem SelectionRules.no_ordered_obstruction (R : SelectionRules)
    (f : Fin 6 → Vertex)
    (hrow : StrictMono (fun i => (f i).1))
    (hedge : ∀ i j, obstructionGraph.Adj i j → R.graph.Adj (f i) (f j)) : False := by
  have forward (i j : Fin 6) (hij : i < j)
      (hadj : obstructionGraph.Adj i j) : R.out (f i) (f j) :=
    R.forward (hedge i j hadj) (hrow hij)
  have out01 := forward 0 1 (by decide) (by decide)
  have out03 := forward 0 3 (by decide) (by decide)
  have out04 := forward 0 4 (by decide) (by decide)
  have out05 := forward 0 5 (by decide) (by decide)
  have out13 := forward 1 3 (by decide) (by decide)
  have out34 := forward 3 4 (by decide) (by decide)
  have out45 := forward 4 5 (by decide) (by decide)
  have stage54 := R.reversal out04 out05 out45
  have stage43 := R.reversal out03 out04 out34
  have stage31 := R.reversal out01 out03 out13
  have cycleEdge := R.earlierWeight out01 out04 out05
    (stage54.trans (stage43.trans stage31)) (stage43.trans stage31)
    (hrow (by decide : (1 : Fin 6) < 5)) (hrow (by decide : (4 : Fin 6) < 5))
  have triangle125 := R.triangle_weight
    (hedge 1 2 (by decide)) (hedge 1 5 (by decide)) (hedge 2 5 (by decide))
    (hrow (by decide : (1 : Fin 6) < 2)) (hrow (by decide : (2 : Fin 6) < 5))
  have triangle245 := R.triangle_weight
    (hedge 2 4 (by decide)) (hedge 2 5 (by decide)) (hedge 4 5 (by decide))
    (hrow (by decide : (2 : Fin 6) < 4)) (hrow (by decide : (4 : Fin 6) < 5))
  exact lt_asymm cycleEdge (triangle125.trans triangle245)

/-- Every linear order of H admits the specified ordered obstruction. -/
def HasObstructionOrderingProperty {W : Type} (H : SimpleGraph W) : Prop :=
  ∀ order : LinearOrder W, ∃ f : Fin 6 → W,
    @StrictMono (Fin 6) W _ order.toPreorder f ∧
    ∀ i j, obstructionGraph.Adj i j → H.Adj (f i) (f j)

/-- Ties in host rows can be broken in the target without changing host edges. -/
theorem SelectionRules.no_weakCopy_of_orderingProperty (R : SelectionRules)
    {W : Type} [LinearOrder W] (H : SimpleGraph W)
    (horder : HasObstructionOrderingProperty H) : ¬ HasWeakCopy H R.graph := by
  rintro ⟨g, _, hedge⟩
  let key : W → One ×ₗ W := fun x => toLex ((g x).1, x)
  have hkey : Injective key := by
    intro x y h
    exact congrArg (fun z : One ×ₗ W => (ofLex z).2) h
  obtain ⟨f, hf, hgraph⟩ := horder (LinearOrder.lift' key hkey)
  change StrictMono (fun i => key (f i)) at hf
  have hrows_le {i j : Fin 6} (hij : i < j) : (g (f i)).1 ≤ (g (f j)).1 := by
    have hkeylt := hf hij
    rcases Prod.Lex.toLex_lt_toLex.mp hkeylt with h | h
    · exact h.le
    · exact h.1.le
  have consecutive (i : Fin 5) : (g (f i.castSucc)).1 < (g (f i.succ)).1 := by
    have hle := hrows_le (Fin.castSucc_lt_succ (i := i))
    have hadj := hedge _ _ (hgraph _ _ (obstructionGraph_consecutive i))
    rcases hadj with hadj | hadj
    · exact (R.nested hadj).1
    · exact False.elim (not_lt_of_ge hle (R.nested hadj).1)
  apply R.no_ordered_obstruction (fun i => g (f i))
  · exact Fin.strictMono_iff_lt_succ.mpr consecutive
  · intro i j h
    exact hedge _ _ (hgraph i j h)

end Erdos597

/-!
# The class of relational structures whose mutual-edge graph omits K₄

The structural Ramsey input is the relational free-amalgamation theorem from
Jan Hubička's public partite-construction formalization. This file supplies
the graph interpretation needed for the Erdős 597 application.
-/

open Function Set
open StructuralRamsey

namespace Erdos597.FiniteTarget

abbrev edgeLanguage : RelLanguage where
  Symbol := Unit
  arity := fun _ => 2

def encodeGraph {V : Type} (G : SimpleGraph V) : RelStructure edgeLanguage V where
  rel _ x := G.Adj (x 0) (x 1)

def HasWeakK4 {V : Type} (C : RelStructure edgeLanguage V) : Prop :=
  ∃ f : Fin 4 → V, Injective f ∧ ∀ i j, i ≠ j → C.rel () ![f i, f j]

def noK4Class {V : Type} (C : RelStructure edgeLanguage V) : Prop := ¬ HasWeakK4 C

@[simp] theorem map_pair {U V : Type} (f : U → V) (x y : U) :
    f ∘ ![x, y] = ![f x, f y] := by
  funext i
  fin_cases i <;> rfl

theorem noK4_hereditary {U V : Type} {A : RelStructure edgeLanguage U}
    {B : RelStructure edgeLanguage V} (hB : noK4Class B)
    (e : RelStructure.Embedding A B) : noK4Class A := by
  rintro ⟨f, hf, hrel⟩
  apply hB
  refine ⟨fun i => e (f i), e.injective.comp hf, ?_⟩
  intro i j hij
  simpa only [map_pair] using (e.map_rel_iff () ![f i, f j]).mpr (hrel i j hij)

theorem noK4_free_amalgamation :
    RelStructure.FreeAmalgamationClass (fun C => noK4Class C) where
  hereditary := fun h e => noK4_hereditary h e
  free := by
    intro U V W X D A B C fA fB iA iB hA hB hfree
    rintro ⟨f, hf, hrel⟩
    let S : Set X := Set.range f
    have hS : (C.induce S).Irreducible := by
      intro x y hxy
      obtain ⟨i, hi⟩ := x.property
      obtain ⟨j, hj⟩ := y.property
      have hij : i ≠ j := by
        intro h
        subst j
        exact hxy (Subtype.ext (hi.symm.trans hj))
      refine ⟨(), ![x, y], 0, 1, ?_, rfl, rfl⟩
      change C.rel () (Subtype.val ∘ ![x, y])
      simpa only [map_pair, hi, hj] using hrel i j hij
    have hbad : HasWeakK4 (C.induce S) := by
      refine ⟨fun i => ⟨f i, ⟨i, rfl⟩⟩, ?_, ?_⟩
      · intro i j h
        exact hf (congrArg Subtype.val h)
      · intro i j hij
        simpa only [RelStructure.induce, map_pair] using hrel i j hij
    rcases hfree.irreducible_side S hS with hleft | hright
    · let e : RelStructure.Embedding (C.induce S) A :=
        (RelStructure.inclusion C S).factorThroughRange iA hleft
      exact (noK4_hereditary hA e) hbad
    · let e : RelStructure.Embedding (C.induce S) B :=
        (RelStructure.inclusion C S).factorThroughRange iB hright
      exact (noK4_hereditary hB e) hbad

def graphOfStructure {V : Type} (C : RelStructure edgeLanguage V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ C.rel () ![x, y] ∧ C.rel () ![y, x]
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem graphOfStructure_cliqueFree {V : Type} {C : RelStructure edgeLanguage V}
    (hC : noK4Class C) : (graphOfStructure C).CliqueFree 4 := by
  classical
  intro S hS
  let e : Fin 4 ≃ S := (Finset.equivFinOfCardEq hS.card_eq).symm
  apply hC
  refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
  intro i j hij
  have hne : (e i).val ≠ (e j).val := by
    intro h
    exact hij (e.injective (Subtype.ext h))
  exact (hS.isClique (e i).property (e j).property hne).2.1

theorem noK4_of_three_coloring {V : Type} {G : SimpleGraph V}
    (color : G.Coloring (Fin 3)) : noK4Class (encodeGraph G) := by
  rintro ⟨f, hf, hrel⟩
  have hcolor : Injective (fun i => color (f i)) := by
    intro i j h
    by_contra hij
    exact color.valid (hrel i j hij) h
  have hcard := Fintype.card_le_of_injective _ hcolor
  norm_num at hcard

end Erdos597.FiniteTarget

/-!
# A finite ordering-property target

The ordered K₂,₂,₂ used here is isomorphic to its reverse. A two-color edge
Ramsey witness for this graph therefore has the required ordering property.
The relational free-amalgamation theorem supplies a K₄-free witness.
-/

open Function Set
open StructuralRamsey

namespace Erdos597.FiniteTarget

theorem obstruction_rev_adj (i j : Fin 6) :
    obstructionGraph.Adj i.rev j.rev ↔ obstructionGraph.Adj i j := by
  revert i j
  decide

def edgeStructure : RelStructure edgeLanguage (Fin 2) := encodeGraph ⊤

def obstructionStructure : RelStructure edgeLanguage (Fin 6) := encodeGraph obstructionGraph

def consecutiveEmbedding (i : Fin 5) :
    RelStructure.Embedding edgeStructure.ordered obstructionStructure.ordered where
  toFun := ![i.castSucc, i.succ]
  injective := by
    revert i
    decide
  map_rel_iff := by
    intro R x
    rcases R with r | r
    · cases r
      change (Fin 2 → Fin 2) at x
      change obstructionGraph.Adj
        (![i.castSucc, i.succ] (x 0)) (![i.castSucc, i.succ] (x 1)) ↔ x 0 ≠ x 1
      revert x
      fin_cases i <;> decide
    · cases r
      change (Fin 2 → Fin 2) at x
      change (![i.castSucc, i.succ] (x 0)) < (![i.castSucc, i.succ] (x 1)) ↔ x 0 < x 1
      revert x
      fin_cases i <;> decide

theorem mapped_obstruction_edge {W : Type} [LinearOrder W]
    {C : RelStructure edgeLanguage W}
    (f : RelStructure.Embedding obstructionStructure.ordered C.ordered)
    {i j : Fin 6} (h : obstructionGraph.Adj i j) :
    (graphOfStructure C).Adj (f i) (f j) := by
  refine ⟨f.injective.ne (obstructionGraph.ne_of_adj h), ?_, ?_⟩
  · have hp := (f.map_rel_iff (.inl ()) ![i, j]).mpr h
    change C.rel () (f ∘ ![i, j]) at hp
    simpa only [map_pair] using hp
  · have hp := (f.map_rel_iff (.inl ()) ![j, i]).mpr h.symm
    change C.rel () (f ∘ ![j, i]) at hp
    simpa only [map_pair] using hp

theorem ordering_property_of_arrow {W : Type} [originalOrder : LinearOrder W]
    {C : RelStructure edgeLanguage W}
    (hArrow : StructuralRamsey.Arrow edgeStructure.ordered obstructionStructure.ordered
      C.ordered Bool) : HasObstructionOrderingProperty (graphOfStructure C) := by
  intro otherOrder
  letI : LinearOrder W := originalOrder
  let color : RelStructure.Embedding edgeStructure.ordered C.ordered → Bool := fun e => by
    classical
    exact decide (@LT.lt W otherOrder.toLT (e 0) (e 1))
  obtain ⟨f, hf⟩ := hArrow color
  have hedge : ∀ i j, obstructionGraph.Adj i j → (graphOfStructure C).Adj (f i) (f j) :=
    fun _ _ h => mapped_obstruction_edge f h
  let c := color (f.comp (consecutiveEmbedding 0))
  have hcolor (i : Fin 5) :
      color (f.comp (consecutiveEmbedding i)) = c :=
    hf (consecutiveEmbedding i) (consecutiveEmbedding 0)
  letI : LinearOrder W := otherOrder
  cases hc : c with
  | false =>
    have hdesc (i : Fin 5) : f i.succ < f i.castSucc := by
      have hnot : ¬ f i.castSucc < f i.succ := by
        simpa [color, RelStructure.Embedding.comp_apply, consecutiveEmbedding, hc] using hcolor i
      apply lt_of_le_of_ne (le_of_not_gt hnot)
      intro heq
      exact (Fin.castSucc_lt_succ (i := i)).ne (f.injective heq).symm
    have hanti : StrictAnti f := by
      change @StrictMono (Fin 6) (OrderDual W) _ _ f
      exact Fin.strictMono_iff_lt_succ.mpr hdesc
    refine ⟨fun i => f i.rev, ?_, ?_⟩
    · intro i j hij
      exact hanti (Fin.rev_strictAnti hij)
    · intro i j hij
      exact hedge _ _ ((obstruction_rev_adj i j).mpr hij)
  | true =>
    refine ⟨f, ?_, hedge⟩
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    simpa [color, RelStructure.Embedding.comp_apply, consecutiveEmbedding, hc] using hcolor i

theorem exists_finite_ordering_target :
    ∃ (W : Type) (_ : Finite W) (H : SimpleGraph W),
      H.CliqueFree 4 ∧ HasObstructionOrderingProperty H := by
  have hB : noK4Class obstructionStructure := noK4_of_three_coloring obstructionColoring
  obtain ⟨W, hW, order, C, hC, hArrow⟩ :=
    RelStructure.FreeAmalgamationClass.orderedRamsey_of_mem_target
      noK4_free_amalgamation edgeStructure obstructionStructure hB Bool
  letI : Finite W := hW
  letI : LinearOrder W := order
  exact ⟨W, hW, graphOfStructure C, graphOfStructure_cliqueFree hC,
    ordering_property_of_arrow hArrow⟩

end Erdos597.FiniteTarget

/-!
# Uncountable rows and countable patterns

These lemmas supply the order-theoretic part of the sparse CH construction.
-/

open Cardinal Ordinal Set Function
open scoped Cardinal Ordinal

namespace Erdos597

def Columns (S : Set Vertex) (a : One) : Set One := {b | (a, b) ∈ S}

theorem exists_gt_of_uncountable {S : Set One} (hS : ¬ S.Countable) (b : One) :
    ∃ x ∈ S, b < x := by
  by_contra h
  push Not at h
  apply hS
  exact (countable_initial_segment b).mono h

theorem countable_of_bounded_rows {S : Set Vertex} (a : One)
    (hrow : ∀ p ∈ S, p.1 ≤ a) (hcol : ∀ r, (Columns S r).Countable) : S.Countable := by
  have : Countable (Iic a) := (countable_initial_segment a).to_subtype
  have : ∀ r : Iic a, Countable (Columns S r.val) := fun r => (hcol r.val).to_subtype
  let f : S → (Σ r : Iic a, Columns S r.val) :=
    fun p => ⟨⟨p.val.1, hrow p.val p.property⟩, ⟨p.val.2, p.property⟩⟩
  have hf : Injective f := by
    intro x y h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun p : Σ r : Iic a, Columns S r.val => p.1.val) h
    · exact congrArg (fun p : Σ r : Iic a, Columns S r.val => p.2.val) h
  exact Set.countable_coe_iff.mp hf.countable

theorem uncountable_range (f : One → Vertex) (hf : Injective f) :
    ¬ (Set.range f).Countable := by
  intro h
  have : Countable (Set.range f) := h.to_subtype
  have : Countable One :=
    (show Injective (fun x => (⟨f x, ⟨x, rfl⟩⟩ : Set.range f)) from
      fun x y hxy => hf (congrArg Subtype.val hxy)).countable
  exact not_countable (α := One) inferInstance

theorem uncountable_row_in_bounded_range (f : One → Vertex) (hf : Injective f)
    (a : One) (hrow : ∀ x, (f x).1 ≤ a) :
    ∃ r, ¬ (Columns (Set.range f) r).Countable := by
  by_contra h
  push Not at h
  apply uncountable_range f hf
  apply countable_of_bounded_rows a
  · rintro p ⟨x, rfl⟩
    exact hrow x
  · exact h

theorem uncountable_row_of_block (f : (ℕ × One) → Vertex) (hf : Injective f)
    (horder : ∀ x y, BlockLt x y → RowLt (f x) (f y)) (n : ℕ) :
    ∃ r, ¬ (Columns (Set.range (fun x => f (n, x))) r).Countable := by
  apply uncountable_row_in_bounded_range (fun x => f (n, x))
    (fun x y h => by simpa using hf h) (f (n + 1, zeroOne)).1
  intro x
  exact row_le_of_rowLt (horder _ _ (Or.inl (Nat.lt_succ_self n)))

theorem row_after_uncountable_block (f : (ℕ × One) → Vertex)
    (horder : ∀ x y, BlockLt x y → RowLt (f x) (f y)) {n m : ℕ} (hnm : n < m)
    {a : One} (ha : ¬ (Columns (Set.range (fun x => f (n, x))) a).Countable)
    (y : One) : a < (f (m, y)).1 := by
  obtain ⟨b, hb, hlarge⟩ := exists_gt_of_uncountable ha (f (m, y)).2
  rcases hb with ⟨x, hx⟩
  change f (n, x) = (a, b) at hx
  have hxy := horder (n, x) (m, y) (Or.inl hnm)
  rw [hx] at hxy
  rcases hxy with hxy | ⟨hrow, hcol⟩
  · exact hxy
  · exact False.elim (lt_asymm hlarge hcol)

theorem exists_increasing_uncountable_rows (f : (ℕ × One) → Vertex) (hf : Injective f)
    (horder : ∀ x y, BlockLt x y → RowLt (f x) (f y)) :
    ∃ a : ℕ → One, StrictMono a ∧
      ∀ n, ¬ (Columns (Set.range (fun x => f (n, x))) (a n)).Countable := by
  choose a ha using uncountable_row_of_block f hf horder
  refine ⟨a, ?_, ha⟩
  intro n m hnm
  obtain ⟨b, hb, _⟩ := exists_gt_of_uncountable (ha m) zeroOne
  rcases hb with ⟨y, hy⟩
  change f (m, y) = (a m, b) at hy
  have h := row_after_uncountable_block f horder hnm (ha n) y
  simpa only [hy] using h

theorem countable_family_bounded {I : Type} [Countable I] (f : I → One) :
    ∃ b : One, ∀ i, f i < b := by
  let index : I → Ordinal := fun i => (f i).toOrd.val + 1
  have hindex : ∀ i, index i < ω₁ := fun i =>
    (Cardinal.isSuccLimit_omega 1).add_one_lt (f i).toOrd.property
  let b : One := Ordinal.ToType.mk ⟨⨆ i, index i, Ordinal.iSup_lt_omega_one hindex⟩
  refine ⟨b, fun i => ?_⟩
  apply Ordinal.ToType.mk.symm.lt_iff_lt.mp
  change (f i).toOrd.val < (Ordinal.ToType.mk.symm b).val
  simp only [b, OrderIso.symm_apply_apply]
  exact (lt_add_one _).trans_le (Ordinal.le_iSup index i)

theorem increasing_sequence_in_uncountable_set {S : Set One} (hS : ¬ S.Countable)
    (lower : One) :
    ∃ f : ℕ → One, StrictMono f ∧ ∀ n, f n ∈ S ∧ lower < f n := by
  let T : Set One := {x | x ∈ S ∧ lower < x}
  have hT : T.Nonempty := exists_gt_of_uncountable hS lower
  have : Nonempty T := hT.to_subtype
  have : NoMaxOrder T := ⟨by
    intro x
    obtain ⟨y, hy, hxy⟩ := exists_gt_of_uncountable hS x.val
    exact ⟨⟨y, hy, x.property.2.trans hxy⟩, hxy⟩⟩
  obtain ⟨f, hf⟩ := Nat.exists_strictMono T
  exact ⟨fun n => (f n).val, hf, fun n => (f n).property⟩

/-- A convenient countable presentation of the patterns used by the recursion. -/
structure Pattern where
  row : ℕ → One
  column : ℕ → ℕ → One
  rows_increasing : StrictMono row
  columns_increasing : ∀ n, StrictMono (column n)
  active : ∀ n m, row n < column n m

def Pattern.point (P : Pattern) (n m : ℕ) : Vertex := (P.row n, P.column n m)

theorem Pattern.bounded (P : Pattern) : ∃ b : One, ∀ n m, P.column n m < b := by
  obtain ⟨b, hb⟩ := countable_family_bounded (fun p : ℕ × ℕ => P.column p.1 p.2)
  exact ⟨b, fun n m => hb (n, m)⟩

theorem pattern_in_block_range (f : (ℕ × One) → Vertex) (hf : Injective f)
    (horder : ∀ x y, BlockLt x y → RowLt (f x) (f y)) :
    ∃ a : One, ¬ (Columns (Set.range (fun x => f (0, x))) a).Countable ∧
      ∃ P : Pattern, (∀ n, a < P.row n) ∧
        ∀ n m, P.point n m ∈ Set.range (fun x => f (n + 1, x)) := by
  obtain ⟨a, ha, hcol⟩ := exists_increasing_uncountable_rows f hf horder
  have hsequence : ∀ n, ∃ b : ℕ → One, StrictMono b ∧
      ∀ m, b m ∈ Columns (Set.range (fun x => f (n + 1, x))) (a (n + 1)) ∧
        a (n + 1) < b m := fun n =>
    increasing_sequence_in_uncountable_set (hcol (n + 1)) (a (n + 1))
  choose b hb hmem using hsequence
  let P : Pattern :=
    { row := fun n => a (n + 1)
      column := b
      rows_increasing := fun _ _ h => ha (Nat.add_lt_add_right h 1)
      columns_increasing := hb
      active := fun n m => (hmem n m).2 }
  refine ⟨a 0, hcol 0, P, fun n => ha (Nat.zero_lt_succ n), ?_⟩
  intro n m
  exact (hmem n m).1

/-- The cofinal hitting condition delivered by a successful pattern recursion. -/
def HitsPatterns (G : SimpleGraph Vertex) : Prop :=
  ∀ P : Pattern, ∃ index : One, ∀ a b : One,
    index < b → (∀ n, a < P.row n) → (∀ n m, P.column n m < b) →
      ∃ n m, G.Adj (a, b) (P.point n m)

theorem no_red_block_of_hits_patterns {G : SimpleGraph Vertex} (hG : HitsPatterns G)
    (f : (ℕ × One) → Vertex) (hf : Injective f)
    (horder : ∀ x y, BlockLt x y → RowLt (f x) (f y))
    (hred : ∀ x y, ¬ G.Adj (f x) (f y)) : False := by
  obtain ⟨a, ha, P, hrows, hpoints⟩ := pattern_in_block_range f hf horder
  obtain ⟨index, hhit⟩ := hG P
  obtain ⟨bound, hbound⟩ := P.bounded
  obtain ⟨b, hb, hbgt⟩ := exists_gt_of_uncountable ha (max index bound)
  obtain ⟨x, hx⟩ := hb
  change f (0, x) = (a, b) at hx
  obtain ⟨n, m, hedge⟩ := hhit a b ((le_max_left _ _).trans_lt hbgt) hrows
    (fun n m => (hbound n m).trans ((le_max_right _ _).trans_lt hbgt))
  obtain ⟨y, hy⟩ := hpoints n m
  change f (n + 1, y) = P.point n m at hy
  apply hred (0, x) (n + 1, y)
  rwa [hx, hy]

theorem pattern_card_under_CH (hCH : (2 : Cardinal.{0}) ^ ℵ₀ = ℵ₁) : #Pattern ≤ ℵ₁ := by
  let code : Pattern → (ℕ → One) × (ℕ → ℕ → One) := fun P => (P.row, P.column)
  have hinj : Injective code := by
    rintro ⟨r, c, hr, hc, ha⟩ ⟨s, d, hs, hd, hb⟩ h
    change (r, c) = (s, d) at h
    have hrs := congrArg Prod.fst h
    have hcd := congrArg Prod.snd h
    cases hrs
    cases hcd
    rfl
  have hpower : (ℵ₁ : Cardinal.{0}) ^ ℵ₀ = ℵ₁ := by
    rw [← hCH, ← Cardinal.power_mul, Cardinal.aleph0_mul_aleph0]
  have hone : #(ℕ → One) = ℵ₁ := by
    simpa only [Cardinal.mk_arrow, one_card, Cardinal.mk_nat, Cardinal.lift_id] using hpower
  have htwo : #(ℕ → ℕ → One) = ℵ₁ := by
    simpa only [Cardinal.mk_arrow, hone, Cardinal.mk_nat, Cardinal.lift_id] using hpower
  calc
    #Pattern ≤ #((ℕ → One) × (ℕ → ℕ → One)) := Cardinal.mk_le_of_injective hinj
    _ = ℵ₁ := by
      rw [Cardinal.mk_prod, hone, htwo]
      simpa only [Cardinal.lift_id] using
        Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)

theorem pattern_index_under_CH (hCH : (2 : Cardinal.{0}) ^ ℵ₀ = ℵ₁) :
    Nonempty (Pattern ↪ One) := by
  apply (Cardinal.le_def _ _).mp
  simpa only [one_card] using pattern_card_under_CH hCH

theorem countable_eligible_patterns (code : Pattern ↪ One) (b : One) :
    Countable {P : Pattern // code P < b} := by
  have hsub : Iio b ⊆ Iic b := by
    intro x hx
    change x ≤ b
    change x < b at hx
    exact hx.le
  have hcount : (Iio b).Countable :=
    (countable_initial_segment b).mono hsub
  have : Countable (Iio b) := hcount.to_subtype
  let f : {P : Pattern // code P < b} → Iio b := fun P => ⟨code P.val, P.property⟩
  apply (show Injective f from ?_).countable
  intro P Q h
  exact Subtype.ext (code.injective (congrArg Subtype.val h))

end Erdos597

/-! # Existence of each finite-predecessor selection step -/

open Cardinal Ordinal Set Function
open scoped Cardinal Ordinal

namespace Erdos597

abbrev RowCodes := ∀ t : One, Iio t ↪ ℕ

noncomputable def defaultRowCodes : RowCodes := by
  intro t
  have : Countable (Iic t) := (countable_initial_segment t).to_subtype
  let f : Iio t → Iic t := fun x => ⟨x.val, by
    change x.val ≤ t
    have hx : x.val < t := x.property
    exact hx.le⟩
  have : Countable (Iio t) :=
    (show Injective f from fun x y h =>
      Subtype.ext (congrArg (fun z : Iic t => z.val) h)).countable
  have hsmall : #(Iio t) ≤ #ℕ := by
    simpa only [Cardinal.mk_nat] using (Cardinal.mk_le_aleph0 (α := Iio t))
  exact Classical.choice ((Cardinal.le_def (Iio t) ℕ).mp hsmall)

noncomputable def rowWeight (code : RowCodes) (t r : One) : ℕ :=
  if h : r < t then code t ⟨r, h⟩ else 0

theorem bounded_weights_finite (code : RowCodes) (t : One) (k : ℕ) :
    {r : One | r < t ∧ rowWeight code t r ≤ k}.Finite := by
  classical
  let T : Set (Iio t) := (code t) ⁻¹' Iic k
  have hT : T.Finite := (Set.finite_Iic k).preimage_embedding (code t)
  apply (hT.image Subtype.val).subset
  intro r hr
  refine ⟨⟨r, hr.1⟩, ?_, rfl⟩
  change code t ⟨r, hr.1⟩ ≤ k
  simpa only [rowWeight, dite_eq_left hr.1] using hr.2

theorem exists_index_outside_finset {A B : Type} [Infinite A] (f : A → B)
    (hf : Injective f) (S : Finset B) : ∃ a, f a ∉ S := by
  classical
  by_contra h
  push Not at h
  have hsmall : (Set.range f).Finite := S.finite_toSet.subset (by
    rintro x ⟨a, rfl⟩
    exact h a)
  exact (Set.infinite_range_of_injective hf) hsmall

def GoodRow (code : RowCodes) (a : One) (S : Finset Vertex) (r : One) : Prop :=
  (∀ u ∈ S, r ≠ u.1) ∧
  ∀ v ∈ S, r < v.1 → rowWeight code v.1 a < rowWeight code v.1 r ∧
    ∀ u ∈ S, u.1 < v.1 → rowWeight code v.1 u.1 < rowWeight code v.1 r

theorem exists_good_row (code : RowCodes) (a : One) (S : Finset Vertex) (P : Pattern) :
    ∃ n, GoodRow code a S (P.row n) := by
  classical
  let bound (v : Vertex) : ℕ :=
    max (rowWeight code v.1 a) (S.sup (fun u => rowWeight code v.1 u.1))
  let bad (v : Vertex) : Finset One := (bounded_weights_finite code v.1 (bound v)).toFinset
  let forbidden : Finset One := S.image Prod.fst ∪ S.biUnion bad
  obtain ⟨n, hn⟩ := exists_index_outside_finset P.row P.rows_increasing.injective forbidden
  refine ⟨n, ?_, ?_⟩
  · intro u hu heq
    apply hn
    apply Finset.mem_union.mpr
    exact Or.inl (Finset.mem_image.mpr ⟨u, hu, heq.symm⟩)
  · intro v hv hrow
    have hbound : bound v < rowWeight code v.1 (P.row n) := by
      by_contra h
      apply hn
      apply Finset.mem_union.mpr
      apply Or.inr
      apply Finset.mem_biUnion.mpr
      refine ⟨v, hv, ?_⟩
      exact (bounded_weights_finite code v.1 (bound v)).mem_toFinset.mpr
        ⟨hrow, le_of_not_gt h⟩
    refine ⟨(le_max_left _ _).trans_lt hbound, ?_⟩
    intro u hu _
    exact (Finset.le_sup (f := fun u => rowWeight code v.1 u.1) hu).trans_lt
      ((le_max_right _ _).trans_lt hbound)

theorem exists_next_point (code : RowCodes) (a : One) (S : Finset Vertex) (P : Pattern)
    (old : Vertex → Vertex → Prop)
    (hone : ∀ x y z, old x y → old x z → y.1 = z.1 → y = z) :
    ∃ n m, GoodRow code a S (P.row n) ∧ ∀ u ∈ S, ¬ old u (P.point n m) := by
  classical
  obtain ⟨n, hn⟩ := exists_good_row code a S P
  have hbad (u : Vertex) : {m : ℕ | old u (P.point n m)}.Finite := by
    apply Set.Subsingleton.finite
    intro i hi j hj
    have hp := hone u (P.point n i) (P.point n j) hi hj rfl
    exact (P.columns_increasing n).injective (congrArg Prod.snd hp)
  let forbidden : Finset ℕ := S.biUnion (fun u => (hbad u).toFinset)
  obtain ⟨m, hm⟩ := exists_index_outside_finset (fun m : ℕ => m) Function.injective_id forbidden
  refine ⟨n, m, hn, ?_⟩
  intro u hu hold
  apply hm
  apply Finset.mem_biUnion.mpr
  refine ⟨u, hu, ?_⟩
  exact (hbad u).mem_toFinset.mpr hold

end Erdos597

/-! # A local neighborhood obtained by processing a sequence of requests -/

open Cardinal Ordinal Set Function
open scoped Cardinal Ordinal

namespace Erdos597

abbrev BelowPattern (a b : One) :=
  {P : Pattern // (∀ n, a < P.row n) ∧ ∀ n m, P.column n m < b}

namespace LocalNeighborhood

variable (code : RowCodes) (a b : One) (old : Vertex → Vertex → Prop)
  (hone : ∀ x y z, old x y → old x z → y.1 = z.1 → y = z)

def PointSpec (S : Finset Vertex) (P : BelowPattern a b) (p : Vertex) : Prop :=
  (∃ n m, p = P.val.point n m) ∧ GoodRow code a S p.1 ∧
    ∀ u ∈ S, ¬ old u p

include hone

theorem exists_point (S : Finset Vertex) (P : BelowPattern a b) :
    ∃ p, PointSpec code a b old S P p := by
  obtain ⟨n, m, hgood, havoid⟩ := exists_next_point code a S P.val old hone
  exact ⟨P.val.point n m, ⟨n, m, rfl⟩, hgood, havoid⟩

noncomputable def choosePoint (S : Finset Vertex) (P : BelowPattern a b) : Vertex :=
  Classical.choose (exists_point code a b old hone S P)

theorem choosePoint_spec (S : Finset Vertex) (P : BelowPattern a b) :
    PointSpec code a b old S P (choosePoint code a b old hone S P) :=
  Classical.choose_spec (exists_point code a b old hone S P)

noncomputable def nextPoint (S : Finset Vertex) (request : Option (BelowPattern a b)) :
    Option Vertex := request.map (choosePoint code a b old hone S)

theorem nextPoint_spec (S : Finset Vertex) (request : Option (BelowPattern a b))
    {p : Vertex} (hp : nextPoint code a b old hone S request = some p) :
    ∃ P, request = some P ∧ PointSpec code a b old S P p := by
  cases request with
  | none => simp [nextPoint] at hp
  | some P =>
    simp only [nextPoint, Option.map_some, Option.some.injEq] at hp
    exact ⟨P, rfl, hp ▸ choosePoint_spec code a b old hone S P⟩

variable (requests : ℕ → Option (BelowPattern a b))

noncomputable def history : ℕ → Finset Vertex :=
  Nat.rec ∅ (fun n S =>
    (nextPoint code a b old hone S (requests n)).elim S (fun p => insert p S))

noncomputable def pointAt (n : ℕ) : Option Vertex :=
  nextPoint code a b old hone (history code a b old hone requests n) (requests n)

theorem history_succ (n : ℕ) :
    history code a b old hone requests (n + 1) =
      (pointAt code a b old hone requests n).elim
        (history code a b old hone requests n)
        (fun p => insert p (history code a b old hone requests n)) := rfl

theorem history_subset_succ (n : ℕ) :
    history code a b old hone requests n ⊆ history code a b old hone requests (n + 1) := by
  classical
  rw [history_succ]
  cases pointAt code a b old hone requests n <;> simp

theorem history_monotone : Monotone (history code a b old hone requests) :=
  monotone_nat_of_le_succ (history_subset_succ code a b old hone requests)

theorem mem_history_of_lt {i j : ℕ} (hij : i < j) {p : Vertex}
    (hp : pointAt code a b old hone requests i = some p) :
    p ∈ history code a b old hone requests j := by
  classical
  have hi : p ∈ history code a b old hone requests (i + 1) := by
    rw [history_succ, hp]
    simp
  exact history_monotone code a b old hone requests (Nat.succ_le_of_lt hij) hi

theorem pointAt_spec {n : ℕ} {p : Vertex}
    (hp : pointAt code a b old hone requests n = some p) :
    ∃ P, requests n = some P ∧ PointSpec code a b old
      (history code a b old hone requests n) P p :=
  nextPoint_spec code a b old hone _ _ hp

theorem pointAt_nested {n : ℕ} {p : Vertex}
    (hp : pointAt code a b old hone requests n = some p) : Nested (a, b) p := by
  obtain ⟨P, _, ⟨⟨i, j, rfl⟩, _, _⟩⟩ := pointAt_spec code a b old hone requests hp
  exact ⟨P.property.1 i, P.val.active i j, P.property.2 i j⟩

theorem rows_ne_of_lt {i j : ℕ} (hij : i < j) {p q : Vertex}
    (hp : pointAt code a b old hone requests i = some p)
    (hq : pointAt code a b old hone requests j = some q) : p.1 ≠ q.1 := by
  obtain ⟨P, _, hspec⟩ := pointAt_spec code a b old hone requests hq
  exact (hspec.2.1.1 p (mem_history_of_lt code a b old hone requests hij hp)).symm

theorem avoids_of_lt {i j : ℕ} (hij : i < j) {p q : Vertex}
    (hp : pointAt code a b old hone requests i = some p)
    (hq : pointAt code a b old hone requests j = some q) : ¬ old p q := by
  obtain ⟨P, _, hspec⟩ := pointAt_spec code a b old hone requests hq
  exact hspec.2.2 p (mem_history_of_lt code a b old hone requests hij hp)

theorem source_weight_of_lt {i j : ℕ} (hij : i < j) {p q : Vertex}
    (hp : pointAt code a b old hone requests i = some p)
    (hq : pointAt code a b old hone requests j = some q) (hrow : q.1 < p.1) :
    rowWeight code p.1 a < rowWeight code p.1 q.1 := by
  obtain ⟨P, _, hspec⟩ := pointAt_spec code a b old hone requests hq
  exact (hspec.2.1.2 p (mem_history_of_lt code a b old hone requests hij hp) hrow).1

theorem earlier_weight_of_lt {i j k : ℕ} (hik : i < k) (hjk : j < k)
    {p q r : Vertex}
    (hp : pointAt code a b old hone requests i = some p)
    (hq : pointAt code a b old hone requests j = some q)
    (hr : pointAt code a b old hone requests k = some r)
    (hrp : r.1 < p.1) (hqp : q.1 < p.1) :
    rowWeight code p.1 q.1 < rowWeight code p.1 r.1 := by
  obtain ⟨P, _, hspec⟩ := pointAt_spec code a b old hone requests hr
  exact (hspec.2.1.2 p (mem_history_of_lt code a b old hone requests hik hp) hrp).2 q
    (mem_history_of_lt code a b old hone requests hjk hq) hqp

theorem hits_request {n : ℕ} {P : BelowPattern a b} (hP : requests n = some P) :
    ∃ i j, pointAt code a b old hone requests n = some (P.val.point i j) := by
  have hp : pointAt code a b old hone requests n =
      some (choosePoint code a b old hone (history code a b old hone requests n) P) := by
    simp only [pointAt, hP, nextPoint, Option.map_some]
  obtain ⟨i, j, heq⟩ := (choosePoint_spec code a b old hone
    (history code a b old hone requests n) P).1
  exact ⟨i, j, heq ▸ hp⟩

end LocalNeighborhood

end Erdos597

/-! # Countable requests and intrinsic neighborhood invariants -/

open Cardinal Ordinal Set Function
open scoped Cardinal Ordinal

namespace Erdos597

def EligiblePattern (indices : Pattern ↪ One) (a b : One) :=
  {P : Pattern // indices P < b ∧ (∀ n, a < P.row n) ∧ ∀ n m, P.column n m < b}

instance eligiblePattern_countable (indices : Pattern ↪ One) (a b : One) :
    Countable (EligiblePattern indices a b) := by
  have : Countable {P : Pattern // indices P < b} := countable_eligible_patterns indices b
  let f : EligiblePattern indices a b → {P : Pattern // indices P < b} :=
    fun P => ⟨P.val, P.property.1⟩
  apply (show Injective f from ?_).countable
  intro P Q h
  exact Subtype.ext (congrArg (fun R : {P : Pattern // indices P < b} => R.val) h)

noncomputable instance eligiblePattern_encodable (indices : Pattern ↪ One) (a b : One) :
    Encodable (EligiblePattern indices a b) := Encodable.ofCountable _

noncomputable def requests (indices : Pattern ↪ One) (a b : One) (n : ℕ) :
    Option (BelowPattern a b) :=
  (Encodable.decode (α := EligiblePattern indices a b) n).map
    (fun P => ⟨P.val, P.property.2⟩)

theorem requests_covers (indices : Pattern ↪ One) (a b : One)
    (P : EligiblePattern indices a b) :
    requests indices a b (Encodable.encode P) = some ⟨P.val, P.property.2⟩ := by
  simp only [requests, Encodable.encodek, Option.map_some]

structure Neighborhood (indices : Pattern ↪ One) (code : RowCodes) (a b : One) where
  seq : ℕ → Option Vertex
  nested : ∀ n p, seq n = some p → Nested (a, b) p
  rows_ne : ∀ i j p q, i < j → seq i = some p → seq j = some q → p.1 ≠ q.1
  source_weight : ∀ i j p q, i < j → seq i = some p → seq j = some q → q.1 < p.1 →
    rowWeight code p.1 a < rowWeight code p.1 q.1
  earlier_weight : ∀ i j k p q r, i < k → j < k →
    seq i = some p → seq j = some q → seq k = some r → r.1 < p.1 → q.1 < p.1 →
      rowWeight code p.1 q.1 < rowWeight code p.1 r.1
  hits : ∀ P : Pattern, indices P < b → (∀ n, a < P.row n) →
    (∀ n m, P.column n m < b) → ∃ n i j, seq n = some (P.point i j)

namespace Neighborhood

variable {indices : Pattern ↪ One} {code : RowCodes} {a b : One}

def out (N : Neighborhood indices code a b) (p : Vertex) : Prop :=
  ∃ n, N.seq n = some p

noncomputable def stage (N : Neighborhood indices code a b) (p : Vertex) : ℕ := by
  classical
  exact if h : N.out p then Nat.find h else 0

theorem stage_spec (N : Neighborhood indices code a b) {p : Vertex} (hp : N.out p) :
    N.seq (N.stage p) = some p := by
  classical
  simpa only [stage, dite_eq_left hp] using Nat.find_spec hp

theorem nested_of_out (N : Neighborhood indices code a b) {p : Vertex} (hp : N.out p) :
    Nested (a, b) p := N.nested _ _ (N.stage_spec hp)

theorem eq_of_stage_eq (N : Neighborhood indices code a b) {p q : Vertex}
    (hp : N.out p) (hq : N.out q) (h : N.stage p = N.stage q) : p = q := by
  have hseq : N.seq (N.stage p) = some q := by simpa only [h] using N.stage_spec hq
  exact Option.some.inj ((N.stage_spec hp).symm.trans hseq)

theorem one_per_row (N : Neighborhood indices code a b) {p q : Vertex}
    (hp : N.out p) (hq : N.out q) (hrow : p.1 = q.1) : p = q := by
  rcases lt_trichotomy (N.stage p) (N.stage q) with h | h | h
  · exact False.elim (N.rows_ne _ _ _ _ h (N.stage_spec hp) (N.stage_spec hq) hrow)
  · exact N.eq_of_stage_eq hp hq h
  · exact False.elim (N.rows_ne _ _ _ _ h (N.stage_spec hq) (N.stage_spec hp) hrow.symm)

end Neighborhood

noncomputable def localNeighborhood (indices : Pattern ↪ One) (code : RowCodes)
    (a b : One) (old : Vertex → Vertex → Prop)
    (hone : ∀ x y z, old x y → old x z → y.1 = z.1 → y = z) :
    Neighborhood indices code a b where
  seq := LocalNeighborhood.pointAt code a b old hone (requests indices a b)
  nested := fun _ _ h =>
    LocalNeighborhood.pointAt_nested code a b old hone (requests indices a b) h
  rows_ne := fun _ _ _ _ hij hp hq =>
    LocalNeighborhood.rows_ne_of_lt code a b old hone (requests indices a b) hij hp hq
  source_weight := fun _ _ _ _ hij hp hq hrow =>
    LocalNeighborhood.source_weight_of_lt code a b old hone (requests indices a b) hij hp hq hrow
  earlier_weight := fun _ _ _ _ _ _ hik hjk hp hq hr hrp hqp =>
    LocalNeighborhood.earlier_weight_of_lt code a b old hone (requests indices a b)
      hik hjk hp hq hr hrp hqp
  hits := by
    intro P hindex hrow hcol
    let Q : EligiblePattern indices a b := ⟨P, hindex, hrow, hcol⟩
    have hreq := requests_covers indices a b Q
    obtain ⟨i, j, hij⟩ := LocalNeighborhood.hits_request code a b old hone
      (requests indices a b) hreq
    exact ⟨Encodable.encode Q, i, j, hij⟩

theorem localNeighborhood_avoids (indices : Pattern ↪ One) (code : RowCodes)
    (a b : One) (old : Vertex → Vertex → Prop)
    (hone : ∀ x y z, old x y → old x z → y.1 = z.1 → y = z)
    {p q : Vertex}
    (hp : (localNeighborhood indices code a b old hone).out p)
    (hq : (localNeighborhood indices code a b old hone).out q)
    (hstage : (localNeighborhood indices code a b old hone).stage p <
      (localNeighborhood indices code a b old hone).stage q) : ¬ old p q := by
  exact LocalNeighborhood.avoids_of_lt code a b old hone (requests indices a b) hstage
    (Neighborhood.stage_spec _ hp) (Neighborhood.stage_spec _ hq)

end Erdos597

/-! # The CH sparse graph, constructed by recursion on the column -/

open Cardinal Ordinal Set Function
open scoped Cardinal Ordinal

namespace Erdos597.SparseConstruction

variable (indices : Pattern ↪ One) (code : RowCodes)

def previousRelation (b : One)
    (previous : ∀ c, c < b → ∀ a, Neighborhood indices code a c)
    (x y : Vertex) : Prop :=
  ∃ h : x.2 < b, (previous x.2 h x.1).out y

theorem previous_one_per_row (b : One)
    (previous : ∀ c, c < b → ∀ a, Neighborhood indices code a c)
    (x y z : Vertex) (hy : previousRelation indices code b previous x y)
    (hz : previousRelation indices code b previous x z) (hrow : y.1 = z.1) : y = z := by
  obtain ⟨h, hy⟩ := hy
  obtain ⟨_, hz⟩ := hz
  exact (previous x.2 h x.1).one_per_row hy hz hrow

noncomputable def family : ∀ b a : One, Neighborhood indices code a b :=
  wellFounded_lt.fix (fun b previous a =>
    localNeighborhood indices code a b (previousRelation indices code b previous)
      (previous_one_per_row indices code b previous))

theorem family_eq (b a : One) :
    family indices code b a =
      localNeighborhood indices code a b
        (previousRelation indices code b (fun c _ => family indices code c))
        (previous_one_per_row indices code b (fun c _ => family indices code c)) := by
  rw [family, WellFounded.fix_eq]

def out (x y : Vertex) : Prop := (family indices code x.2 x.1).out y

noncomputable def stage (x y : Vertex) : ℕ := (family indices code x.2 x.1).stage y

theorem nested {x y : Vertex} (h : out indices code x y) : Nested x y :=
  (family indices code x.2 x.1).nested_of_out h

theorem loopless (x : Vertex) : ¬ out indices code x x := by
  intro h
  exact (lt_irrefl x.1) (nested indices code h).1

theorem avoids {x u v : Vertex}
    (hu : out indices code x u) (hv : out indices code x v)
    (hstage : stage indices code x u < stage indices code x v) :
    ¬ previousRelation indices code x.2 (fun c _ => family indices code c) u v := by
  change (family indices code x.2 x.1).out u at hu
  change (family indices code x.2 x.1).out v at hv
  change (family indices code x.2 x.1).stage u <
    (family indices code x.2 x.1).stage v at hstage
  have heq := family_eq indices code x.2 x.1
  rw [heq] at hu hv hstage
  exact localNeighborhood_avoids indices code x.1 x.2 _ _ hu hv hstage

theorem reversal {x u v : Vertex}
    (hu : out indices code x u) (hv : out indices code x v)
    (huv : out indices code u v) : stage indices code x v < stage indices code x u := by
  by_contra h
  rcases lt_or_eq_of_le (le_of_not_gt h) with hlt | heq
  · apply avoids indices code hu hv hlt
    exact ⟨(nested indices code hu).2.2, huv⟩
  · have huvEq : u = v := (family indices code x.2 x.1).eq_of_stage_eq hu hv heq
    subst v
    exact loopless indices code u huv

noncomputable def rules : SelectionRules where
  out := out indices code
  stage := stage indices code
  weight := rowWeight code
  nested := nested indices code
  reversal := reversal indices code
  sourceWeight := by
    intro x u v hu hv hstage hrow
    exact (family indices code x.2 x.1).source_weight _ _ v u hstage
      (Neighborhood.stage_spec _ hv) (Neighborhood.stage_spec _ hu) hrow
  earlierWeight := by
    intro x u v w hu hv hw hwu hvu huw hvw
    exact (family indices code x.2 x.1).earlier_weight _ _ _ w v u hwu hvu
      (Neighborhood.stage_spec _ hw) (Neighborhood.stage_spec _ hv)
      (Neighborhood.stage_spec _ hu) huw hvw

theorem hits_patterns : HitsPatterns (rules indices code).graph := by
  intro P
  refine ⟨indices P, ?_⟩
  intro a b hindex hrows hcolumns
  obtain ⟨n, i, j, hpoint⟩ := (family indices code b a).hits P hindex hrows hcolumns
  exact ⟨i, j, Or.inl ⟨n, hpoint⟩⟩

end Erdos597.SparseConstruction

namespace Erdos597

theorem exists_sparse_graph_under_CH (hCH : (2 : Cardinal.{0}) ^ ℵ₀ = ℵ₁) :
    ∃ R : SelectionRules, HitsPatterns R.graph := by
  obtain ⟨indices⟩ := pattern_index_under_CH hCH
  exact ⟨SparseConstruction.rules indices defaultRowCodes,
    SparseConstruction.hits_patterns indices defaultRowCodes⟩

end Erdos597

/-! # Transfer of the CH sparse graph to the exact ordinal relation -/

open Cardinal Ordinal Set Function
open scoped Cardinal Ordinal

namespace Erdos597

def onSquare (G : SimpleGraph Vertex) : SimpleGraph Square where
  Adj x y := G.Adj (squareIso x) (squareIso y)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h⟩

theorem onSquare_no_red_block {G : SimpleGraph Vertex} (hG : HitsPatterns G) :
    ¬ ∃ s, (onSquare G)ᶜ.IsClique s ∧ typeLT s = (ω₁ : Ordinal.{0}) * ω := by
  rintro ⟨s, hs, htype⟩
  have hblocks : type (Prod.Lex (· < ·) (· < ·) :
      (ℕ × One) → (ℕ × One) → Prop) = (ω₁ : Ordinal.{0}) * ω := by
    rw [type_prod_lex, type_toType, type_nat_lt]
  obtain ⟨e⟩ : Nonempty
      ((Prod.Lex (· < ·) (· < ·) : (ℕ × One) → (ℕ × One) → Prop) ≃r
        ((· < ·) : s → s → Prop)) :=
    type_eq.mp (hblocks.trans htype.symm)
  let f : (ℕ × One) → Vertex := fun x => squareIso (e x).val
  have hf : Injective f :=
    squareIso.injective.comp (Subtype.val_injective.comp e.injective)
  apply no_red_block_of_hits_patterns hG f hf
  · intro x y hxy
    exact Prod.lex_def.mp (squareIso.map_rel_iff.mpr
      (e.map_rel_iff.mpr (Prod.lex_def.mpr hxy)))
  · intro x y hblue
    have hne : (e x).val ≠ (e y).val := by
      intro h
      have heq : x = y := e.injective (Subtype.ext h)
      subst y
      exact G.loopless.irrefl _ hblue
    exact (SimpleGraph.compl_adj _ _ _).mp
      (hs (e x).property (e y).property hne) |>.2 hblue

theorem onSquare_no_weakCopy {W : Type} {G : SimpleGraph Vertex} {H : SimpleGraph W}
    (hH : ¬ HasWeakCopy H G) : ¬ HasWeakCopy H (onSquare G) := by
  rintro ⟨f, hf, hedge⟩
  exact hH ⟨fun x => squareIso (f x), squareIso.injective.comp hf, hedge⟩

theorem partition_failure_of_hits_patterns {W : Type} {G : SimpleGraph Vertex}
    {H : SimpleGraph W} (hG : HitsPatterns G) (hH : ¬ HasWeakCopy H G) :
    ¬ OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ))
      ((ω₁ : Ordinal.{0}) * ω) H := by
  intro h
  rcases h (onSquare G)ᶜ (onSquare G) isCompl_compl.symm with hred | hblue
  · exact onSquare_no_red_block hG hred
  · exact onSquare_no_weakCopy hH hblue

theorem partition_failure_under_CH_of_ordering_property
    (hCH : (2 : Cardinal.{0}) ^ ℵ₀ = ℵ₁)
    {W : Type} [LinearOrder W] (H : SimpleGraph W)
    (hH : HasObstructionOrderingProperty H) :
    ¬ OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ))
      ((ω₁ : Ordinal.{0}) * ω) H := by
  obtain ⟨R, hR⟩ := exists_sparse_graph_under_CH hCH
  exact partition_failure_of_hits_patterns hR (R.no_weakCopy_of_orderingProperty H hH)

end Erdos597

/-! # A fixed finite target whose ordinal partition relation fails under CH -/

open Cardinal Ordinal
open scoped Cardinal Ordinal

namespace Erdos597

theorem exists_fixed_finite_CH_counterexample :
    ∃ (W : Type) (_ : Finite W) (H : SimpleGraph W), H.CliqueFree 4 ∧
      ((2 : Cardinal.{0}) ^ ℵ₀ = ℵ₁ →
        ¬ OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ))
          ((ω₁ : Ordinal.{0}) * ω) H) := by
  obtain ⟨W, hW, H, hK, horder⟩ := FiniteTarget.exists_finite_ordering_target
  letI : Finite W := hW
  letI : Fintype W := Fintype.ofFinite W
  letI : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  exact ⟨W, hW, H, hK, fun hCH =>
    partition_failure_under_CH_of_ordering_property hCH H horder⟩

theorem finite_universal_fails_under_CH (hCH : (2 : Cardinal.{0}) ^ ℵ₀ = ℵ₁) :
    ¬ ∀ (W : Type) [Fintype W] (H : SimpleGraph W), H.CliqueFree 4 →
      OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ))
        ((ω₁ : Ordinal.{0}) * ω) H := by
  intro h
  obtain ⟨W, hW, H, hK, hbad⟩ := exists_fixed_finite_CH_counterexample
  letI : Finite W := hW
  letI : Fintype W := Fintype.ofFinite W
  exact hbad hCH (h W H hK)

end Erdos597

/-!
# Uncountable good and bad pairs

These are the elementary rectangle lemmas used in the positive partition
argument of Baumgartner, Remarks on partition ordinals, Section 2.
-/

open Set Function

namespace Erdos597

theorem exists_mem_outside_countable {A B : Set One}
    (hA : ¬ A.Countable) (hB : B.Countable) : ∃ x ∈ A, x ∉ B := by
  by_contra h
  push Not at h
  exact hA (hB.mono h)

theorem uncountable_diff_countable {A B : Set One}
    (hA : ¬ A.Countable) (hB : B.Countable) : ¬ (A \ B).Countable := by
  intro h
  apply hA
  apply (h.union hB).mono
  intro a ha
  by_cases hb : a ∈ B
  · exact Or.inr hb
  · exact Or.inl ⟨ha, hb⟩

theorem uncountable_injective_range {X : Type} (f : One → X) (hf : Injective f) :
    ¬ (Set.range f).Countable := by
  intro h
  have : Countable (Set.range f) := h.to_subtype
  have : Countable One :=
    (show Injective (fun x => (⟨f x, ⟨x, rfl⟩⟩ : Set.range f)) from
      fun x y hxy => hf (congrArg Subtype.val hxy)).countable
  exact not_countable (α := One) inferInstance

theorem one_embeds_in_uncountable {X : Type} {S : Set X} (hS : ¬ S.Countable) :
    Nonempty (One ↪ S) := by
  apply (Cardinal.le_def One S).mp
  rw [one_card]
  exact le_of_not_gt (fun h => hS
    (Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.lt_aleph_one_iff.mp h)))

theorem exists_uncountable_fiber {X : Type} [Countable X] (f : One → X) :
    ∃ x, ¬ {i | f i = x}.Countable := by
  by_contra h
  push Not at h
  have hc : (⋃ x, {i | f i = x}).Countable := countable_iUnion h
  have heq : (⋃ x, {i | f i = x}) = (univ : Set One) := by
    ext i
    simp
  rw [heq] at hc
  have hOne : ¬ (univ : Set One).Countable := by
    simpa using uncountable_injective_range (id : One → One) injective_id
  exact hOne hc

namespace CountableRectangle

variable (E : One → One → Prop) (A B : Set One)
variable (hA : ¬ A.Countable) (hB : ¬ B.Countable)
variable (hleft : ∀ a ∈ A, {b | b ∈ B ∧ E a b}.Countable)
variable (hright : ∀ b ∈ B, {a | a ∈ A ∧ E a b}.Countable)

def StepProperty (t : One) (previous : ∀ s, s < t → A × B) (p : A × B) : Prop :=
  (∀ s (hs : s < t),
    p.1.val ≠ (previous s hs).1.val ∧
    p.2.val ≠ (previous s hs).2.val ∧
    ¬ E p.1.val (previous s hs).2.val ∧
    ¬ E (previous s hs).1.val p.2.val) ∧ ¬ E p.1.val p.2.val

include hA hB hleft hright

theorem exists_step (t : One) (previous : ∀ s, s < t → A × B) :
    ∃ p, StepProperty E A B t previous p := by
  classical
  have : Countable (Iio t) := ((countable_initial_segment t).mono Iio_subset_Iic_self).to_subtype
  let usedA : Set One := ⋃ s : Iio t,
    ({(previous s.val s.property).1.val} ∪
      {a | a ∈ A ∧ E a (previous s.val s.property).2.val})
  have husedA : usedA.Countable := by
    apply countable_iUnion
    intro s
    exact (countable_singleton _).union
      (hright _ (previous s.val s.property).2.property)
  obtain ⟨a, ha, hav⟩ := exists_mem_outside_countable hA husedA
  let usedB : Set One := (⋃ s : Iio t,
    ({(previous s.val s.property).2.val} ∪
      {b | b ∈ B ∧ E (previous s.val s.property).1.val b})) ∪
      {b | b ∈ B ∧ E a b}
  have husedB : usedB.Countable := by
    apply Countable.union
    · apply countable_iUnion
      intro s
      exact (countable_singleton _).union
        (hleft _ (previous s.val s.property).1.property)
    · exact hleft a ha
  obtain ⟨b, hb, hbv⟩ := exists_mem_outside_countable hB husedB
  refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_, ?_⟩
  · intro s hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro heq
      exact hav (mem_iUnion.mpr ⟨⟨s, hs⟩, Or.inl (mem_singleton_iff.mpr heq)⟩)
    · intro heq
      exact hbv (Or.inl (mem_iUnion.mpr ⟨⟨s, hs⟩, Or.inl (mem_singleton_iff.mpr heq)⟩))
    · intro hedge
      exact hav (mem_iUnion.mpr ⟨⟨s, hs⟩, Or.inr ⟨ha, hedge⟩⟩)
    · intro hedge
      exact hbv (Or.inl (mem_iUnion.mpr ⟨⟨s, hs⟩, Or.inr ⟨hb, hedge⟩⟩))
  · intro hedge
    exact hbv (Or.inr ⟨hb, hedge⟩)

noncomputable def chooseStep (t : One) (previous : ∀ s, s < t → A × B) : A × B :=
  Classical.choose (exists_step E A B hA hB hleft hright t previous)

theorem chooseStep_spec (t : One) (previous : ∀ s, s < t → A × B) :
    StepProperty E A B t previous (chooseStep E A B hA hB hleft hright t previous) :=
  Classical.choose_spec (exists_step E A B hA hB hleft hright t previous)

noncomputable def sequence : One → A × B :=
  wellFounded_lt.fix (chooseStep E A B hA hB hleft hright)

theorem sequence_spec (t : One) :
    StepProperty E A B t (fun s _ => sequence E A B hA hB hleft hright s)
      (sequence E A B hA hB hleft hright t) := by
  unfold sequence
  rw [WellFounded.fix_eq]
  exact chooseStep_spec E A B hA hB hleft hright t _

end CountableRectangle

theorem uncountable_empty_rectangle (E : One → One → Prop) (A B : Set One)
    (hA : ¬ A.Countable) (hB : ¬ B.Countable)
    (hleft : ∀ a ∈ A, {b | b ∈ B ∧ E a b}.Countable)
    (hright : ∀ b ∈ B, {a | a ∈ A ∧ E a b}.Countable) :
    ∃ A' ⊆ A, ¬ A'.Countable ∧
      ∃ B' ⊆ B, ¬ B'.Countable ∧ ∀ a ∈ A', ∀ b ∈ B', ¬ E a b := by
  let f := CountableRectangle.sequence E A B hA hB hleft hright
  have hs (t : One) := CountableRectangle.sequence_spec E A B hA hB hleft hright t
  have hinjA : Injective (fun t => (f t).1.val) := by
    intro s t heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hst | hts
    · exact ((hs t).1 s hst).1 heq.symm
    · exact ((hs s).1 t hts).1 heq
  have hinjB : Injective (fun t => (f t).2.val) := by
    intro s t heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hst | hts
    · exact ((hs t).1 s hst).2.1 heq.symm
    · exact ((hs s).1 t hts).2.1 heq
  refine ⟨range (fun t => (f t).1.val), ?_, uncountable_injective_range _ hinjA,
    range (fun t => (f t).2.val), ?_, uncountable_injective_range _ hinjB, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact (f t).1.property
  · rintro _ ⟨t, rfl⟩
    exact (f t).2.property
  · rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rcases lt_trichotomy s t with hst | rfl | hts
    · exact ((hs t).1 s hst).2.2.2
    · exact (hs s).2
    · exact ((hs s).1 t hts).2.2.1

def GoodPair (E : One → One → Prop) (A B : Set One) : Prop :=
  ∀ A' ⊆ A, ¬ A'.Countable → ∀ B' ⊆ B, ¬ B'.Countable →
    ∃ A'' ⊆ A', ¬ A''.Countable ∧
      ∃ B'' ⊆ B', ¬ B''.Countable ∧ ∀ a ∈ A'', ∀ b ∈ B'', ¬ E a b

def BadPair (E : One → One → Prop) (A B : Set One) : Prop :=
  ∀ A' ⊆ A, ¬ A'.Countable → ∀ B' ⊆ B, ¬ B'.Countable →
    ∃ a ∈ A', ∃ b ∈ B', E a b

theorem BadPair.mono {E : One → One → Prop} {A B A' B' : Set One}
    (h : BadPair E A B) (ha : A' ⊆ A) (hb : B' ⊆ B) : BadPair E A' B' := by
  intro C hC hCU D hD hDU
  exact h C (hC.trans ha) hCU D (hD.trans hb) hDU

theorem GoodPair.mono {E : One → One → Prop} {A B A' B' : Set One}
    (h : GoodPair E A B) (ha : A' ⊆ A) (hb : B' ⊆ B) : GoodPair E A' B' := by
  intro C hC hCU D hD hDU
  exact h C (hC.trans ha) hCU D (hD.trans hb) hDU

theorem not_goodPair {E : One → One → Prop} {A B : Set One}
    (h : ¬ GoodPair E A B) :
    ∃ A' ⊆ A, ¬ A'.Countable ∧ ∃ B' ⊆ B, ¬ B'.Countable ∧ BadPair E A' B' := by
  classical
  simp only [GoodPair] at h
  push Not at h
  obtain ⟨A', hA', hAU, B', hB', hBU, hnone⟩ := h
  refine ⟨A', hA', hAU, B', hB', hBU, ?_⟩
  exact hnone

theorem BadPair.countable_small_fibers {E : One → One → Prop} {A B : Set One}
    (hbad : BadPair E A B) (hB : ¬ B.Countable)
    (hright : ∀ b ∈ B, {a | a ∈ A ∧ E a b}.Countable) :
    {a | a ∈ A ∧ {b | b ∈ B ∧ E a b}.Countable}.Countable := by
  classical
  by_contra hsmall
  let S := {a | a ∈ A ∧ {b | b ∈ B ∧ E a b}.Countable}
  have hrightS : ∀ b ∈ B, {a | a ∈ S ∧ E a b}.Countable := by
    intro b hb
    apply (hright b hb).mono
    intro a ha
    exact ⟨ha.1.1, ha.2⟩
  obtain ⟨A', hA', hAU, B', hB', hBU, hnone⟩ :=
    uncountable_empty_rectangle E S B hsmall hB
      (fun _ ha => ha.2) hrightS
  obtain ⟨a, ha, b, hb, hedge⟩ := hbad A' (fun a ha => (hA' ha).1) hAU B' hB' hBU
  exact hnone a ha b hb hedge

theorem select_from_bad_pairs :
    ∀ (n : ℕ) (E : Fin n → Fin n → One → One → Prop) (A : Fin n → Set One),
      (∀ i, ¬ (A i).Countable) →
      (∀ i j, i < j → BadPair (E i j) (A i) (A j)) →
      (∀ i j, i < j → ∀ b ∈ A j, {a | a ∈ A i ∧ E i j a b}.Countable) →
      ∃ x : Fin n → One, (∀ i, x i ∈ A i) ∧ ∀ i j, i < j → E i j (x i) (x j) := by
  classical
  intro n
  induction n with
  | zero =>
    intro E A hA hbad hfibers
    exact ⟨Fin.elim0, (fun i => i.elim0), (fun i => i.elim0)⟩
  | succ n ih =>
    intro E A hA hbad hfibers
    let small (j : Fin n) : Set One :=
      {a | a ∈ A 0 ∧ {b | b ∈ A j.succ ∧ E 0 j.succ a b}.Countable}
    have hsmall (j : Fin n) : (small j).Countable :=
      (hbad 0 j.succ (Nat.zero_lt_succ j.val)).countable_small_fibers
        (hA j.succ) (hfibers 0 j.succ (Nat.zero_lt_succ j.val))
    obtain ⟨a, ha, havoid⟩ := exists_mem_outside_countable (hA 0) (countable_iUnion hsmall)
    let A' (j : Fin n) : Set One := {b | b ∈ A j.succ ∧ E 0 j.succ a b}
    have hA' (j : Fin n) : ¬ (A' j).Countable := by
      intro hc
      exact havoid (mem_iUnion.mpr ⟨j, ha, hc⟩)
    have hbad' (i j : Fin n) (hij : i < j) :
        BadPair (E i.succ j.succ) (A' i) (A' j) :=
      (hbad i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)).mono
        (fun _ h => h.1) (fun _ h => h.1)
    have hfibers' (i j : Fin n) (hij : i < j) (b : One) (hb : b ∈ A' j) :
        {a | a ∈ A' i ∧ E i.succ j.succ a b}.Countable := by
      apply (hfibers i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij) b hb.1).mono
      intro c hc
      exact ⟨hc.1.1, hc.2⟩
    obtain ⟨x, hx, he⟩ := ih (fun i j => E i.succ j.succ) A' hA' hbad' hfibers'
    refine ⟨Fin.cases a x, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact ha
      | succ i => exact (hx i).1
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact False.elim ((lt_irrefl _) hij)
        | succ j => exact (hx j).2
      | succ i =>
        cases j using Fin.cases with
        | zero => exact False.elim (Fin.not_lt_zero _ hij)
        | succ j => exact he i j (Fin.succ_lt_succ_iff.mp hij)

end Erdos597

/-! # Finite good-or-bad decisions used in the weak-independence construction -/

open Set Function

namespace Erdos597

theorem finite_pair_decisions {K : Type} [DecidableEq K]
    (A : K → Set One) (E : K → One → One → Prop) (hA : ∀ i, ¬ (A i).Countable) :
    ∀ s : Finset K, ∀ B : Set One, ¬ B.Countable →
      ∃ B' ⊆ B, ¬ B'.Countable ∧ ∀ i ∈ s,
        ∃ A' ⊆ A i, ¬ A'.Countable ∧
          (GoodPair (E i) (A i) B' ∨ BadPair (E i) A' B') := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro B hB
    exact ⟨B, Subset.rfl, hB, by simp⟩
  | @insert i s his ih =>
    intro B hB
    by_cases hi : GoodPair (E i) (A i) B
    · obtain ⟨B', hB', hBU, hrest⟩ := ih B hB
      refine ⟨B', hB', hBU, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨A j, Subset.rfl, hA j, Or.inl (hi.mono Subset.rfl hB')⟩
      · exact hrest j hj
    · obtain ⟨A₁, hA₁, hA₁U, B₁, hB₁, hB₁U, hbad⟩ := not_goodPair hi
      obtain ⟨B', hB', hBU, hrest⟩ := ih B₁ hB₁U
      refine ⟨B', hB'.trans hB₁, hBU, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨A₁, hA₁, hA₁U, Or.inr (hbad.mono Subset.rfl hB')⟩
      · exact hrest j hj

theorem all_finite_pair_decisions {K : Type} [Fintype K]
    (A : K → Set One) (E : K → One → One → Prop) (hA : ∀ i, ¬ (A i).Countable)
    (B : Set One) (hB : ¬ B.Countable) :
    ∃ B' ⊆ B, ¬ B'.Countable ∧ ∀ i,
      ∃ A' ⊆ A i, ¬ A'.Countable ∧
        (GoodPair (E i) (A i) B' ∨ BadPair (E i) A' B') := by
  classical
  obtain ⟨B', hB', hBU, h⟩ := finite_pair_decisions A E hA Finset.univ B hB
  exact ⟨B', hB', hBU, fun i => h i (Finset.mem_univ i)⟩

end Erdos597

/-! # The finite-chain family in Baumgartner's weak-independence argument -/

open Set Function

namespace Erdos597.WeakFamilies

abbrev Index := {s : Finset ℕ // s.Nonempty}

def first (s : Index) : ℕ := s.val.min' s.property
def last (s : Index) : ℕ := s.val.max' s.property

def singleton (r : ℕ) : Index := ⟨{r}, Finset.singleton_nonempty r⟩

@[simp] theorem first_singleton (r : ℕ) : first (singleton r) = r := by
  simp [first, singleton]

@[simp] theorem last_singleton (r : ℕ) : last (singleton r) = r := by
  simp [last, singleton]

abbrev Prior (r : ℕ) := {s : (Finset.range r).powerset // (s : Finset ℕ).Nonempty}

def priorIndex {r : ℕ} (s : Prior r) : Index := ⟨s.val.val, s.property⟩

theorem prior_last_lt {r : ℕ} (s : Prior r) : last (priorIndex s) < r := by
  apply Finset.mem_range.mp
  apply (Finset.mem_powerset.mp s.val.property)
  exact s.val.val.max'_mem s.property

structure Row (D : ℕ → Set One) (r : ℕ) where
  set : Set One
  uncountable : ¬ set.Countable
  subset : set ⊆ D r

abbrev At (D : ℕ → Set One) (r : ℕ) := ∀ s : Index, last s = r → Row D (first s)
abbrev Before (D : ℕ → Set One) (r : ℕ) := ∀ t : ℕ, t < r → At D t

def previous {D : ℕ → Set One} {r : ℕ} (old : Before D r) (s : Prior r) :
    Row D (first (priorIndex s)) :=
  old (last (priorIndex s)) (prior_last_lt s) (priorIndex s) rfl

structure Decision (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (r : ℕ) (old : Before D r) where
  right : Row D r
  left : ∀ s : Prior r, Row D (first (priorIndex s))
  contained : ∀ s, (left s).set ⊆ (previous old s).set
  status : ∀ s, GoodPair (E (first (priorIndex s)) r) (previous old s).set right.set ∨
    BadPair (E (first (priorIndex s)) r) (left s).set right.set

theorem exists_decision (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) (r : ℕ) (old : Before D r) :
    Nonempty (Decision D E r old) := by
  classical
  let : Fintype (Prior r) := Fintype.ofFinite _
  obtain ⟨B, hBD, hBU, hA⟩ := all_finite_pair_decisions
    (fun s : Prior r => (previous old s).set)
    (fun s => E (first (priorIndex s)) r)
    (fun s => (previous old s).uncountable) (D r) (hD r)
  choose A hAS hAU hAB using hA
  exact ⟨{
    right := ⟨B, hBU, hBD⟩
    left := fun s => ⟨A s, hAU s, (hAS s).trans (previous old s).subset⟩
    contained := hAS
    status := hAB
  }⟩

noncomputable def decision (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) (r : ℕ) (old : Before D r) : Decision D E r old :=
  Classical.choice (exists_decision D E hD r old)

def erasePrior (s : Index) {r : ℕ} (hs : last s = r)
    (he : (s.val.erase r).Nonempty) : Prior r := by
  refine ⟨⟨s.val.erase r, Finset.mem_powerset.mpr ?_⟩, he⟩
  intro x hx
  have hx' := Finset.mem_erase.mp hx
  apply Finset.mem_range.mpr
  apply lt_of_le_of_ne
  · rw [← hs]
    exact s.val.le_max' x hx'.2
  · exact hx'.1

theorem first_erase (s : Index) {r : ℕ} (hs : last s = r)
    (he : (s.val.erase r).Nonempty) : first (priorIndex (erasePrior s hs he)) = first s := by
  have hfirstmem : first s ∈ s.val.erase r := by
    refine Finset.mem_erase.mpr ⟨?_, s.val.min'_mem s.property⟩
    obtain ⟨x, hx⟩ := he
    have hx' := Finset.mem_erase.mp hx
    have hxlt : x < r := by
      apply lt_of_le_of_ne
      · rw [← hs]
        exact s.val.le_max' x hx'.2
      · exact hx'.1
    exact ((s.val.min'_le x hx'.2).trans_lt hxlt).ne
  apply le_antisymm
  · exact (s.val.erase r).min'_le (first s) hfirstmem
  · exact s.val.min'_le _ (Finset.mem_of_mem_erase ((s.val.erase r).min'_mem he))

theorem first_of_erase_empty (s : Index) {r : ℕ} (he : s.val.erase r = ∅) : first s = r := by
  by_contra hne
  have hm : first s ∈ s.val.erase r := Finset.mem_erase.mpr ⟨hne, s.val.min'_mem s.property⟩
  simp [he] at hm

noncomputable def step (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) (r : ℕ) (old : Before D r) : At D r := by
  classical
  intro s hs
  let d := decision D E hD r old
  by_cases he : (s.val.erase r).Nonempty
  · let p := erasePrior s hs he
    refine ⟨(d.left p).set, (d.left p).uncountable, ?_⟩
    have hfirst := first_erase s hs he
    rw [← hfirst]
    exact (d.left p).subset
  · refine ⟨d.right.set, d.right.uncountable, ?_⟩
    have heq : s.val.erase r = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    rw [first_of_erase_empty s heq]
    exact d.right.subset

theorem step_set_nonempty (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) (r : ℕ) (old : Before D r)
    (s : Index) (hs : last s = r) (he : (s.val.erase r).Nonempty) :
    (step D E hD r old s hs).set =
      ((decision D E hD r old).left (erasePrior s hs he)).set := by
  simp [step, he]

theorem step_set_empty (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) (r : ℕ) (old : Before D r)
    (s : Index) (hs : last s = r) (he : s.val.erase r = ∅) :
    (step D E hD r old s hs).set = (decision D E hD r old).right.set := by
  simp [step, he]

noncomputable def family (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) : ∀ r, At D r :=
  wellFounded_lt.fix (step D E hD)

theorem family_eq (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) (r : ℕ) :
    family D E hD r = step D E hD r (fun t _ => family D E hD t) := by
  rw [family, WellFounded.fix_eq]

noncomputable def sets (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) (s : Index) : Set One :=
  (family D E hD (last s) s rfl).set

theorem sets_uncountable (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) (s : Index) : ¬ (sets D E hD s).Countable :=
  (family D E hD (last s) s rfl).uncountable

theorem sets_subset (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) (s : Index) : sets D E hD s ⊆ D (first s) :=
  (family D E hD (last s) s rfl).subset

theorem sets_singleton (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) (r : ℕ) :
    sets D E hD (singleton r) =
      (decision D E hD r (fun t _ => family D E hD t)).right.set := by
  unfold sets
  simp only [last_singleton]
  rw [family_eq]
  exact step_set_empty D E hD r _ _ _ (by simp [singleton])

theorem sets_shrink (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) (s : Index)
    (he : (s.val.erase (last s)).Nonempty) :
    sets D E hD s ⊆ sets D E hD (priorIndex (erasePrior s rfl he)) := by
  unfold sets
  rw [family_eq, step_set_nonempty D E hD (last s) _ s rfl he]
  exact (decision D E hD (last s) (fun t _ => family D E hD t)).contained _

theorem sets_bad_extension (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) (s : Index)
    (he : (s.val.erase (last s)).Nonempty)
    (hbad : ¬ GoodPair (E (first (priorIndex (erasePrior s rfl he))) (last s))
      (sets D E hD (priorIndex (erasePrior s rfl he))) (sets D E hD (singleton (last s)))) :
    BadPair (E (first (priorIndex (erasePrior s rfl he))) (last s))
      (sets D E hD s) (sets D E hD (singleton (last s))) := by
  have h := (decision D E hD (last s) (fun t _ => family D E hD t)).status
    (erasePrior s rfl he)
  have hset : sets D E hD s =
      ((decision D E hD (last s) (fun t _ => family D E hD t)).left
        (erasePrior s rfl he)).set := by
    unfold sets
    rw [family_eq, step_set_nonempty D E hD (last s) _ s rfl he]
  rw [sets_singleton] at hbad ⊢
  rw [hset]
  exact h.resolve_left hbad

end Erdos597.WeakFamilies

/-! # Nesting along initial segments of a finite chain -/

open Set Function

namespace Erdos597.WeakFamilies

theorem sets_subset_of_prefix (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) (s t : Index) (ht : t.val ⊆ s.val)
    (hbefore : ∀ a ∈ t.val, ∀ b ∈ s.val, b ∉ t.val → a < b) :
    sets D E hD s ⊆ sets D E hD t := by
  classical
  have aux : ∀ m : ℕ, ∀ s : Index, s.val.card = m → ∀ t : Index,
      t.val ⊆ s.val → (∀ a ∈ t.val, ∀ b ∈ s.val, b ∉ t.val → a < b) →
      sets D E hD s ⊆ sets D E hD t := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro s hcard t ht hbefore
      by_cases heq : s.val = t.val
      · have hs : s = t := Subtype.ext heq
        rw [hs]
      · have hout : ∃ b ∈ s.val, b ∉ t.val := by
          by_contra hn
          push Not at hn
          exact heq (Finset.Subset.antisymm hn ht)
        obtain ⟨b, hb, hbt⟩ := hout
        have hlast : last s ∉ t.val := by
          intro hlast
          have hlt := hbefore (last s) hlast b hb hbt
          exact (not_lt_of_ge (s.val.le_max' b hb)) hlt
        have herase : (s.val.erase (last s)).Nonempty := by
          obtain ⟨a, ha⟩ := t.property
          exact ⟨a, Finset.mem_erase.mpr ⟨fun h => hlast (h ▸ ha), ht ha⟩⟩
        let p : Index := priorIndex (erasePrior s rfl herase)
        have hpcard : p.val.card < m := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem (s.val.max'_mem s.property)
        have htp : t.val ⊆ p.val := by
          intro a ha
          exact Finset.mem_erase.mpr ⟨fun h => hlast (h ▸ ha), ht ha⟩
        have hbefore' : ∀ a ∈ t.val, ∀ b ∈ p.val, b ∉ t.val → a < b := by
          intro a ha b hb hbt
          exact hbefore a ha b (Finset.mem_of_mem_erase hb) hbt
        exact (sets_shrink D E hD s herase).trans (ih p.val.card hpcard p rfl t htp hbefore')
  exact aux s.val.card s rfl t ht hbefore

end Erdos597.WeakFamilies

/-!
# Infinite Ramsey theorem for finite subsets of the natural numbers

The recursive reservoir proof extends the pair-selection approach in
Ching-Tsun Chou's InfGraphRamsey formalization to every fixed finite arity.
-/

open Set Function

namespace Erdos597

def InfiniteSetRamsey (k : ℕ) : Prop :=
  ∀ F : Finset ℕ → Bool, ∀ X : Set ℕ, X.Infinite →
    ∃ c : Bool, ∃ Y ⊆ X, Y.Infinite ∧
      ∀ T : Finset ℕ, T.card = k → (T : Set ℕ) ⊆ Y → F T = c

namespace InfiniteRamsey

structure Selection where
  set : Set ℕ
  infinite : set.Infinite
  vertex : ℕ
  color : Bool

def SelectionProperty (k : ℕ) (F : Finset ℕ → Bool) (X : Set ℕ) (S : Selection) : Prop :=
  S.vertex ∈ X ∧ S.set ⊆ X ∧ (∀ u ∈ S.set, S.vertex < u) ∧
    ∀ T : Finset ℕ, T.card = k → (T : Set ℕ) ⊆ S.set → F (insert S.vertex T) = S.color

theorem exists_selection {k : ℕ} (ih : InfiniteSetRamsey k)
    (F : Finset ℕ → Bool) (X : Set ℕ) (hX : X.Infinite) :
    ∃ S : Selection, SelectionProperty k F X S := by
  classical
  obtain ⟨v, hv⟩ := hX.nonempty
  obtain ⟨c, Y, hY, hYI, hcolor⟩ :=
    ih (fun T => F (insert v T)) (X \ Iic v) (hX.sdiff (Set.finite_Iic v))
  refine ⟨⟨Y, hYI, v, c⟩, hv, ?_, ?_, hcolor⟩
  · exact fun u hu => (hY hu).1
  · intro u hu
    exact lt_of_not_ge (hY hu).2

noncomputable def sequence {k : ℕ} (ih : InfiniteSetRamsey k)
    (F : Finset ℕ → Bool) (X : Set ℕ) (hX : X.Infinite) : ℕ → Selection
  | 0 => Classical.choose (exists_selection ih F X hX)
  | n + 1 => Classical.choose (exists_selection ih F
      (sequence ih F X hX n).set (sequence ih F X hX n).infinite)

theorem sequence_zero {k : ℕ} (ih : InfiniteSetRamsey k)
    (F : Finset ℕ → Bool) (X : Set ℕ) (hX : X.Infinite) :
    SelectionProperty k F X (sequence ih F X hX 0) :=
  Classical.choose_spec (exists_selection ih F X hX)

theorem sequence_succ {k : ℕ} (ih : InfiniteSetRamsey k)
    (F : Finset ℕ → Bool) (X : Set ℕ) (hX : X.Infinite) (n : ℕ) :
    SelectionProperty k F (sequence ih F X hX n).set (sequence ih F X hX (n + 1)) :=
  Classical.choose_spec (exists_selection ih F
    (sequence ih F X hX n).set (sequence ih F X hX n).infinite)

end InfiniteRamsey

theorem infinite_set_ramsey : ∀ k : ℕ, InfiniteSetRamsey k := by
  classical
  intro k
  induction k with
  | zero =>
    intro F X hX
    refine ⟨F ∅, X, Subset.rfl, hX, ?_⟩
    intro T hT hTX
    rw [Finset.card_eq_zero.mp hT]
  | succ k ih =>
    intro F X hX
    let S := InfiniteRamsey.sequence ih F X hX
    have hzero := InfiniteRamsey.sequence_zero ih F X hX
    have hsucc (n : ℕ) := InfiniteRamsey.sequence_succ ih F X hX n
    have hanti : Antitone (fun n => (S n).set) :=
      antitone_nat_of_succ_le (fun n => (hsucc n).2.1)
    have hsubset (n : ℕ) : (S n).set ⊆ X := (hanti (Nat.zero_le n)).trans hzero.2.1
    have hmem (n : ℕ) : (S n).vertex ∈ X := by
      cases n with
      | zero => exact hzero.1
      | succ n => exact hsubset n (hsucc n).1
    have hafter {m n : ℕ} (hmn : m < n) : (S n).vertex ∈ (S m).set := by
      cases n with
      | zero => exact False.elim (Nat.not_lt_zero m hmn)
      | succ n => exact hanti (Nat.le_of_lt_succ hmn) (hsucc n).1
    have hlt (n : ℕ) : ∀ u ∈ (S n).set, (S n).vertex < u := by
      cases n with
      | zero => exact hzero.2.2.1
      | succ n => exact (hsucc n).2.2.1
    have hcolors (n : ℕ) : ∀ T : Finset ℕ, T.card = k → (T : Set ℕ) ⊆ (S n).set →
        F (insert (S n).vertex T) = (S n).color := by
      cases n with
      | zero => exact hzero.2.2.2
      | succ n => exact (hsucc n).2.2.2
    have hmono : StrictMono (fun n => (S n).vertex) := fun m n hmn => hlt m _ (hafter hmn)
    obtain ⟨c, hI⟩ := Finite.exists_infinite_fiber (fun n => (S n).color)
    let I : Set ℕ := {n | (S n).color = c}
    have hII : I.Infinite := Set.infinite_coe_iff.mp hI
    let Y : Set ℕ := (fun n => (S n).vertex) '' I
    refine ⟨c, Y, ?_, hII.image hmono.injective.injOn, ?_⟩
    · rintro _ ⟨n, hn, rfl⟩
      exact hmem n
    · intro T hT hTY
      have hTN : T.Nonempty := Finset.card_pos.mp (hT ▸ Nat.zero_lt_succ k)
      let v := T.min' hTN
      have hv : v ∈ T := T.min'_mem hTN
      obtain ⟨i, hi, hvi⟩ := hTY hv
      change (S i).vertex = v at hvi
      have hvI : (S i).vertex ∈ T := by rwa [hvi]
      have hcard : (T.erase (S i).vertex).card = k := by
        rw [Finset.card_erase_of_mem hvI, hT, Nat.add_sub_cancel]
      have htail : (T.erase (S i).vertex : Set ℕ) ⊆ (S i).set := by
        intro u hu
        have hu' := Finset.mem_erase.mp hu
        obtain ⟨j, hj, huj⟩ := hTY hu'.2
        change (S j).vertex = u at huj
        have hmin : v ≤ u := T.min'_le u hu'.2
        have hne : v ≠ u := by
          intro h
          exact hu'.1 (h.symm.trans hvi.symm)
        have hless : (S i).vertex < (S j).vertex := by
          rw [hvi, huj]
          exact lt_of_le_of_ne hmin hne
        have hij : i < j := hmono.lt_iff_lt.mp hless
        simpa only [huj] using hafter hij
      have hcolor := hcolors i (T.erase (S i).vertex) hcard htail
      rw [Finset.insert_erase hvI] at hcolor
      exact hcolor.trans hi

end Erdos597

/-! # The increasing-tuple form of infinite Ramsey's theorem -/

open Set Function

namespace Erdos597

theorem infinite_tuple_ramsey (k : ℕ) (F : (Fin k → ℕ) → Bool)
    (X : Set ℕ) (hX : X.Infinite) :
    ∃ c : Bool, ∃ Y ⊆ X, Y.Infinite ∧
      ∀ f : Fin k → ℕ, StrictMono f → (∀ i, f i ∈ Y) → F f = c := by
  classical
  let color (T : Finset ℕ) : Bool :=
    if h : T.card = k then F (T.orderEmbOfFin h) else false
  obtain ⟨c, Y, hYX, hY, hcolor⟩ := infinite_set_ramsey k color X hX
  refine ⟨c, Y, hYX, hY, ?_⟩
  intro f hf hmem
  let T : Finset ℕ := Finset.univ.image f
  have hT : T.card = k := by
    change (Finset.univ.image f).card = k
    rw [Finset.card_image_of_injective _ hf.injective, Finset.card_univ, Fintype.card_fin]
  have hTmem (i : Fin k) : f i ∈ T :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hcanonical : f = T.orderEmbOfFin hT := Finset.orderEmbOfFin_unique hT hTmem hf
  have hsubset : (T : Set ℕ) ⊆ Y := by
    rintro _ hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i
  have h := hcolor T hT hsubset
  simpa only [color, dite_eq_left hT, ← hcanonical] using h

end Erdos597

/-! # Increasing tuples and the finite-chain family -/

open Set Function

namespace Erdos597.WeakFamilies

def tupleIndex {k : ℕ} (hk : 0 < k) (f : Fin k → ℕ) : Index :=
  ⟨Finset.univ.image f,
    ⟨f ⟨0, hk⟩, Finset.mem_image.mpr ⟨⟨0, hk⟩, Finset.mem_univ _, rfl⟩⟩⟩

theorem first_tuple {k : ℕ} (hk : 0 < k) (f : Fin k → ℕ) (hf : StrictMono f) :
    first (tupleIndex hk f) = f ⟨0, hk⟩ := by
  apply le_antisymm
  · exact (Finset.univ.image f).min'_le _
      (Finset.mem_image.mpr ⟨⟨0, hk⟩, Finset.mem_univ _, rfl⟩)
  · have hm := (Finset.univ.image f).min'_mem (tupleIndex hk f).property
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hm
    exact (hf.monotone (show (⟨0, hk⟩ : Fin k) ≤ i from Nat.zero_le i.val)).trans_eq heq

theorem tuple_card {k : ℕ} (hk : 0 < k) (f : Fin k → ℕ) (hf : Injective f) :
    (tupleIndex hk f).val.card = k := by
  exact (Finset.card_image_of_injective _ hf).trans (Fintype.card_fin k)

def appendTuple {m n : ℕ} (f : Fin m → ℕ) (g : Fin n → ℕ) (i : Fin (m + n)) : ℕ :=
  if h : i.val < m then f ⟨i.val, h⟩ else g ⟨i.val - m, by omega⟩

@[simp] theorem appendTuple_left {m n : ℕ} (f : Fin m → ℕ) (g : Fin n → ℕ) (i : Fin m) :
    appendTuple f g (Fin.castAdd n i) = f i := by
  simp [appendTuple, i.isLt]

@[simp] theorem appendTuple_right {m n : ℕ} (f : Fin m → ℕ) (g : Fin n → ℕ) (i : Fin n) :
    appendTuple f g (Fin.natAdd m i) = g i := by
  simp [appendTuple, Nat.not_lt.mpr (Nat.le_add_right m i.val)]

theorem appendTuple_strictMono {m n : ℕ} (f : Fin m → ℕ) (g : Fin n → ℕ)
    (hf : StrictMono f) (hg : StrictMono g) (hcross : ∀ i j, f i < g j) :
    StrictMono (appendTuple f g) := by
  intro i j hij
  dsimp [appendTuple]
  split_ifs with hi hj
  · exact hf hij
  · exact hcross _ _
  · have hij' : i.val < j.val := hij
    omega
  · apply hg
    change i.val - m < j.val - m
    have hij' : i.val < j.val := hij
    omega

end Erdos597.WeakFamilies

/-!
# Martin's axiom and the finite-independent-set forcing

The axiom is stated through partial orders, countable antichains, dense sets,
and filters. The extraction theorem below retains explicit ccc and density
hypotheses for the particular forcing. Those hypotheses require separate proofs.
-/

open Set Function Cardinal
open scoped Cardinal

namespace Erdos597

def CountableChainCondition (P : Type) [PartialOrder P] : Prop :=
  ∀ A : Set P, A.Pairwise (fun p q => ¬ ∃ r : P, r ≤ p ∧ r ≤ q) → A.Countable

def MartinAxiomAlephOne : Prop :=
  ∀ (P : Type) [PartialOrder P], CountableChainCondition P →
    ∀ (I : Type), #I ≤ ℵ₁ → ∀ D : I → Set P,
      (∀ i p, ∃ q ∈ D i, q ≤ p) → ∀ p : P,
        ∃ F : Order.PFilter P, p ∈ F ∧ ∀ i, ∃ q ∈ F, q ∈ D i

abbrev BlockVertex := ℕ × One

def BlockIndependent (G : SimpleGraph BlockVertex) (S : Set BlockVertex) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x.1 ≠ y.1 → ¬ G.Adj x y

structure IndependentCondition (G : SimpleGraph BlockVertex) (H : Set BlockVertex)
    (cut : One) where
  points : Finset BlockVertex
  contained : ∀ x ∈ points, x ∈ H ∧ cut < x.2
  independent : BlockIndependent G (points : Set BlockVertex)

namespace IndependentCondition

variable {G : SimpleGraph BlockVertex} {H : Set BlockVertex} {cut : One}

@[ext] theorem ext {p q : IndependentCondition G H cut} (h : p.points = q.points) : p = q := by
  cases p
  cases q
  cases h
  rfl

instance : PartialOrder (IndependentCondition G H cut) where
  le p q := q.points ⊆ p.points
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ hpq hqr := hqr.trans hpq
  le_antisymm _ _ hpq hqp := ext (Finset.Subset.antisymm hqp hpq)

def empty : IndependentCondition G H cut where
  points := ∅
  contained := by simp
  independent := by
    intro x hx
    simp at hx

noncomputable def union (p q : IndependentCondition G H cut)
    (hcross : ∀ x ∈ p.points, ∀ y ∈ q.points, x.1 ≠ y.1 → ¬ G.Adj x y) :
    IndependentCondition G H cut where
  points := p.points ∪ q.points
  contained := by
    intro x hx
    rcases Finset.mem_union.mp hx with hp | hq
    · exact p.contained x hp
    · exact q.contained x hq
  independent := by
    intro x hx y hy hrow
    rcases Finset.mem_union.mp hx with hxp | hxq <;>
      rcases Finset.mem_union.mp hy with hyp | hyq
    · exact p.independent x hxp y hyp hrow
    · exact hcross x hxp y hyq hrow
    · intro h
      exact hcross y hyp x hxq hrow.symm h.symm
    · exact q.independent x hxq y hyq hrow

theorem compatible_of_cross (p q : IndependentCondition G H cut)
    (hcross : ∀ x ∈ p.points, ∀ y ∈ q.points, x.1 ≠ y.1 → ¬ G.Adj x y) :
    ∃ r : IndependentCondition G H cut, r ≤ p ∧ r ≤ q :=
  ⟨union p q hcross, Finset.subset_union_left, Finset.subset_union_right⟩

def limitSet (F : Order.PFilter (IndependentCondition G H cut)) : Set BlockVertex :=
  {x | ∃ p ∈ F, x ∈ p.points}

theorem limitSet_subset (F : Order.PFilter (IndependentCondition G H cut)) :
    limitSet F ⊆ H := by
  rintro x ⟨p, hp, hx⟩
  exact (p.contained x hx).1

theorem limitSet_independent (F : Order.PFilter (IndependentCondition G H cut)) :
    BlockIndependent G (limitSet F) := by
  rintro x ⟨p, hp, hx⟩ y ⟨q, hq, hy⟩ hrow
  obtain ⟨r, hr, hrp, hrq⟩ := F.directed p hp q hq
  exact r.independent x (hrp hx) y (hrq hy) hrow

end IndependentCondition

def ActiveRows (H : Set BlockVertex) : Set ℕ :=
  {n | ¬ {b : One | (n, b) ∈ H}.Countable}

def RowDense (G : SimpleGraph BlockVertex) (H : Set BlockVertex) (cut : One)
    (i : ActiveRows H × One) : Set (IndependentCondition G H cut) :=
  {p | ∃ b : One, i.2 < b ∧ (i.1.val, b) ∈ p.points}

theorem forcing_extract (hMA : MartinAxiomAlephOne)
    (G : SimpleGraph BlockVertex) (H : Set BlockVertex) (cut : One)
    (hccc : CountableChainCondition (IndependentCondition G H cut))
    (hdense : ∀ i p, ∃ q ∈ RowDense G H cut i, q ≤ p) :
    ∃ S ⊆ H, BlockIndependent G S ∧
      ∀ n ∈ ActiveRows H, ¬ {b : One | (n, b) ∈ S}.Countable := by
  classical
  have hindex : #(ActiveRows H × One) ≤ ℵ₁ := by
    let e : ActiveRows H × One ↪ ℕ × One :=
      ⟨fun i => (i.1.val, i.2), by
        intro i j h
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun z : ℕ × One => z.1) h
        · exact congrArg (fun z : ℕ × One => z.2) h⟩
    calc
      #(ActiveRows H × One) ≤ #(ℕ × One) := Cardinal.mk_le_of_injective e.injective
      _ = ℵ₁ := by simp
  obtain ⟨F, hstart, hmeet⟩ := hMA (IndependentCondition G H cut) hccc
    (ActiveRows H × One) hindex (RowDense G H cut) hdense IndependentCondition.empty
  refine ⟨IndependentCondition.limitSet F, IndependentCondition.limitSet_subset F,
    IndependentCondition.limitSet_independent F, ?_⟩
  intro n hn hc
  have : Countable {b : One | (n, b) ∈ IndependentCondition.limitSet F} := hc.to_subtype
  obtain ⟨bound, hbound⟩ := countable_family_bounded
    (fun b : {b : One | (n, b) ∈ IndependentCondition.limitSet F} => b.val)
  obtain ⟨p, hp, b, hlarge, hb⟩ := hmeet (⟨n, hn⟩, bound)
  have hmem : (n, b) ∈ IndependentCondition.limitSet F := ⟨p, hp, hb⟩
  exact lt_asymm hlarge (hbound ⟨b, hmem⟩)

end Erdos597

/-! # Simultaneous thinning for finitely many good pairs -/

open Set Function

namespace Erdos597

theorem finite_good_rectangles {K : Type} [DecidableEq K]
    (x y : K → One ↪ One) (E : K → One → One → Prop)
    (hgood : ∀ k, GoodPair (E k) (range (x k)) (range (y k))) :
    ∀ s : Finset K, ∀ A B : Set One, ¬ A.Countable → ¬ B.Countable →
      ∃ A' ⊆ A, ¬ A'.Countable ∧ ∃ B' ⊆ B, ¬ B'.Countable ∧
        ∀ k ∈ s, ∀ a ∈ A', ∀ b ∈ B', ¬ E k (x k a) (y k b) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro A B hA hB
    exact ⟨A, Subset.rfl, hA, B, Subset.rfl, hB, by simp⟩
  | @insert k s hks ih =>
    intro A B hA hB
    have hxA : ¬ ((x k) '' A).Countable := by
      intro hc
      exact hA (countable_of_injective_of_countable_image (x k).injective.injOn hc)
    have hyB : ¬ ((y k) '' B).Countable := by
      intro hc
      exact hB (countable_of_injective_of_countable_image (y k).injective.injOn hc)
    obtain ⟨X, hX, hXU, Y, hY, hYU, hnone⟩ := hgood k
      ((x k) '' A) (by rintro _ ⟨a, ha, rfl⟩; exact ⟨a, rfl⟩) hxA
      ((y k) '' B) (by rintro _ ⟨b, hb, rfl⟩; exact ⟨b, rfl⟩) hyB
    let A₁ : Set One := {a | a ∈ A ∧ x k a ∈ X}
    let B₁ : Set One := {b | b ∈ B ∧ y k b ∈ Y}
    have hXA : X ⊆ (x k) '' A₁ := by
      intro z hz
      obtain ⟨a, ha, heq⟩ := hX hz
      exact ⟨a, ⟨ha, heq ▸ hz⟩, heq⟩
    have hYB : Y ⊆ (y k) '' B₁ := by
      intro z hz
      obtain ⟨b, hb, heq⟩ := hY hz
      exact ⟨b, ⟨hb, heq ▸ hz⟩, heq⟩
    have hA₁ : ¬ A₁.Countable := fun hc => hXU ((hc.image (x k)).mono hXA)
    have hB₁ : ¬ B₁.Countable := fun hc => hYU ((hc.image (y k)).mono hYB)
    obtain ⟨A', hA', hAU, B', hB', hBU, hrest⟩ := ih A₁ B₁ hA₁ hB₁
    refine ⟨A', (fun _ ha => (hA' ha).1), hAU,
      B', (fun _ hb => (hB' hb).1), hBU, ?_⟩
    intro j hj a ha b hb
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hnone _ (hA' ha).2 _ (hB' hb).2
    · exact hrest j hj a ha b hb

end Erdos597

/-! # The uncountable delta-system lemma for finite sets -/

open Set Function

namespace Erdos597

theorem uncountable_disjoint_family {X : Type} [DecidableEq X]
    (f : One → Finset X) (hf : ∀ x, {i | x ∈ f i}.Countable) :
    ∃ I : Set One, ¬ I.Countable ∧ I.Pairwise (fun i j => Disjoint (f i) (f j)) := by
  classical
  let S : Set (Set One) := {I | I.Pairwise (fun i j => Disjoint (f i) (f j))}
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c →
      ∃ ub ∈ S, ∀ I ∈ c, I ⊆ ub := by
    intro c hc hcc
    refine ⟨⋃₀ c, ?_, fun I hI => subset_sUnion_of_mem hI⟩
    rintro i ⟨I, hI, hi⟩ j ⟨J, hJ, hj⟩ hij
    obtain rfl | hne := eq_or_ne I J
    · exact hc hI hi hj hij
    · rcases hcc hI hJ hne with hIJ | hJI
      · exact hc hJ (hIJ hi) hj hij
      · exact hc hI hi (hJI hj) hij
  obtain ⟨I, hI⟩ := zorn_subset S hchain
  refine ⟨I, ?_, hI.prop⟩
  intro hcI
  let used : Set One := I ∪ ⋃ i ∈ I, ⋃ x ∈ f i, {j | x ∈ f j}
  have hused : used.Countable :=
    hcI.union (hcI.biUnion (fun i hi => (f i).countable_toSet.biUnion (fun x hx => hf x)))
  have hOne : ¬ (univ : Set One).Countable := by
    simpa using uncountable_injective_range (id : One → One) injective_id
  obtain ⟨j, _, hj⟩ := exists_mem_outside_countable hOne hused
  have hjI : j ∉ I := fun h => hj (Or.inl h)
  have hdis (i : One) (hi : i ∈ I) : Disjoint (f j) (f i) := by
    apply Finset.disjoint_left.mpr
    intro x hxj hxi
    exact hj (Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi,
      mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hxi, hxj⟩⟩⟩⟩))
  have hnew : insert j I ∈ S := by
    intro a ha b hb hab
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact False.elim (hab rfl)
    · exact hdis b hb
    · exact (hdis a ha).symm
    · exact hI.prop ha hb hab
  have hsub : insert j I ⊆ I := hI.2 hnew (subset_insert j I)
  exact hjI (hsub (mem_insert j I))

theorem delta_system_bounded {X : Type} [DecidableEq X] :
    ∀ (n : ℕ) (f : One → Finset X), (∀ i, (f i).card ≤ n) →
      ∃ I : Set One, ¬ I.Countable ∧ ∃ root : Finset X,
        ∀ i ∈ I, ∀ j ∈ I, i ≠ j → f i ∩ f j = root := by
  classical
  intro n
  induction n with
  | zero =>
    intro f hcard
    refine ⟨univ, ?_, ∅, ?_⟩
    · simpa using uncountable_injective_range (id : One → One) injective_id
    · intro i hi j hj hij
      have hfi : f i = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hcard i))
      simp [hfi]
  | succ n ih =>
    intro f hcard
    by_cases hex : ∃ x : X, ¬ {i | x ∈ f i}.Countable
    · obtain ⟨x, hx⟩ := hex
      obtain ⟨e⟩ := one_embeds_in_uncountable hx
      let g : One → Finset X := fun i => (f (e i).val).erase x
      have hg (i : One) : (g i).card ≤ n :=
        Nat.le_of_lt_succ ((Finset.card_erase_lt_of_mem (e i).property).trans_le (hcard _))
      obtain ⟨J, hJ, root, hroot⟩ := ih g hg
      let index : One → One := fun i => (e i).val
      have hinj : Injective index := Subtype.val_injective.comp e.injective
      refine ⟨index '' J, ?_, insert x root, ?_⟩
      · intro hc
        exact hJ (countable_of_injective_of_countable_image hinj.injOn hc)
      · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hij
        have hne : i ≠ j := fun h => hij (congrArg index h)
        have hr := hroot i hi j hj hne
        have hxi : x ∈ f (index i) := (e i).property
        have hxj : x ∈ f (index j) := (e j).property
        ext y
        by_cases hyx : y = x
        · subst y
          simp [hxi, hxj]
        · have hy : y ∈ g i ∩ g j ↔ y ∈ root := by rw [hr]
          simpa [g, index, hyx] using hy
    · have hf (x : X) : {i | x ∈ f i}.Countable := by
        by_contra h
        exact hex ⟨x, h⟩
      obtain ⟨I, hI, hdis⟩ := uncountable_disjoint_family f hf
      refine ⟨I, hI, ∅, fun i hi j hj hij => ?_⟩
      exact Finset.disjoint_iff_inter_eq_empty.mp (hdis hi hj hij)

theorem delta_system {X : Type} [DecidableEq X] (f : One → Finset X) :
    ∃ I : Set One, ¬ I.Countable ∧ ∃ root : Finset X,
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j → f i ∩ f j = root := by
  obtain ⟨n, hn⟩ := exists_uncountable_fiber (fun i => (f i).card)
  obtain ⟨e⟩ := one_embeds_in_uncountable hn
  let index : One → One := fun i => (e i).val
  have hinj : Injective index := Subtype.val_injective.comp e.injective
  obtain ⟨J, hJ, root, hr⟩ := delta_system_bounded n (fun i => f (index i))
    (fun i => (e i).property.le)
  refine ⟨index '' J, ?_, root, ?_⟩
  · intro hc
    exact hJ (countable_of_injective_of_countable_image hinj.injOn hc)
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hij
    exact hr i hi j hj (fun h => hij (congrArg index h))

end Erdos597

/-! # A delta-system family with fixed row coordinates -/

open Set Function

namespace Erdos597

theorem uniform_finite_family (f : One → Finset (ℕ × One)) :
    ∃ index : One ↪ One, ∃ n : ℕ, ∃ root : Finset (ℕ × One),
      ∃ row : Fin n → ℕ, ∃ col : Fin n → One ↪ One,
        (∀ i, root ⊆ f (index i)) ∧
        (∀ i k, (row k, col k i) ∈ f (index i)) ∧
        (∀ i x, x ∈ f (index i) → x ∈ root ∨ ∃ k, x = (row k, col k i)) := by
  classical
  obtain ⟨I, hI, root, hroot⟩ := delta_system f
  obtain ⟨e₀⟩ := one_embeds_in_uncountable hI
  let q : One → Finset (ℕ × One) := fun i => f (e₀ i).val
  have hdelta (i j : One) (hij : i ≠ j) : q i ∩ q j = root := by
    apply hroot _ (e₀ i).property _ (e₀ j).property
    intro h
    exact hij (e₀.injective (Subtype.ext h))
  have hrootSub (i : One) : root ⊆ q i := by
    obtain ⟨j, hji⟩ := exists_ne i
    rw [← hdelta i j hji.symm]
    exact Finset.inter_subset_left
  let petal : One → Finset (ℕ × One) := fun i => q i \ root
  have hdis (i j : One) (hij : i ≠ j) : Disjoint (petal i) (petal j) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := Finset.mem_sdiff.mp hx
    have hy' := Finset.mem_sdiff.mp hy
    apply hx'.2
    rw [← hdelta i j hij]
    exact Finset.mem_inter.mpr ⟨hx'.1, hy'.1⟩
  obtain ⟨n, hn⟩ := exists_uncountable_fiber (fun i => (petal i).card)
  obtain ⟨e₁⟩ := one_embeds_in_uncountable hn
  let enum (i : One) : Fin n ≃ (petal (e₁ i).val) :=
    (Finset.equivFinOfCardEq (e₁ i).property).symm
  let pattern (i : One) : Fin n → ℕ := fun k => (enum i k).val.1
  obtain ⟨row, hrow⟩ := exists_uncountable_fiber pattern
  obtain ⟨e₂⟩ := one_embeds_in_uncountable hrow
  let mid : One ↪ One :=
    ⟨fun i => (e₁ (e₂ i).val).val,
      (Subtype.val_injective.comp e₁.injective).comp (Subtype.val_injective.comp e₂.injective)⟩
  let index : One ↪ One :=
    ⟨fun i => (e₀ (mid i)).val, (Subtype.val_injective.comp e₀.injective).comp mid.injective⟩
  let point (i : One) (k : Fin n) : ℕ × One := (enum (e₂ i).val k).val
  have point_mem (i : One) (k : Fin n) : point i k ∈ petal (mid i) :=
    (enum (e₂ i).val k).property
  have point_row (i : One) (k : Fin n) : (point i k).1 = row k :=
    congrFun (e₂ i).property k
  have point_inj (k : Fin n) : Injective (fun i => (point i k).2) := by
    intro i j hcol
    by_contra hij
    have hpoint : point i k = point j k :=
      Prod.ext ((point_row i k).trans (point_row j k).symm) hcol
    exact Finset.disjoint_left.mp (hdis (mid i) (mid j) (mid.injective.ne hij))
      (point_mem i k) (hpoint ▸ point_mem j k)
  let col (k : Fin n) : One ↪ One := ⟨fun i => (point i k).2, point_inj k⟩
  have point_eq (i : One) (k : Fin n) : point i k = (row k, col k i) :=
    Prod.ext (point_row i k) rfl
  refine ⟨index, n, root, row, col, ?_, ?_, ?_⟩
  · intro i
    exact hrootSub (mid i)
  · intro i k
    rw [← point_eq i k]
    exact (Finset.mem_sdiff.mp (point_mem i k)).1
  · intro i x hx
    by_cases hxr : x ∈ root
    · exact Or.inl hxr
    · right
      have hxp : x ∈ petal (mid i) := Finset.mem_sdiff.mpr ⟨hx, hxr⟩
      let k : Fin n := (enum (e₂ i).val).symm ⟨x, hxp⟩
      refine ⟨k, ?_⟩
      have hk : point i k = x :=
        congrArg Subtype.val ((enum (e₂ i).val).apply_symm_apply ⟨x, hxp⟩)
      exact hk.symm.trans (point_eq i k)

end Erdos597

/-! # Compatibility in the finite-independent-set forcing -/

open Set Function

namespace Erdos597

def WeaklyIndependent (G : SimpleGraph BlockVertex) (H : Set BlockVertex) : Prop :=
  ∀ r s : ℕ, r ≠ s →
    GoodPair (fun a b => G.Adj (r, a) (s, b))
      {a | (r, a) ∈ H} {b | (s, b) ∈ H}

theorem compatible_uniform_family
    {G : SimpleGraph BlockVertex} {H : Set BlockVertex} {cut : One}
    (hweak : WeaklyIndependent G H) (p : One → IndependentCondition G H cut)
    (n : ℕ) (root : Finset BlockVertex) (row : Fin n → ℕ) (col : Fin n → One ↪ One)
    (hroot : ∀ i, root ⊆ (p i).points)
    (hmem : ∀ i k, (row k, col k i) ∈ (p i).points)
    (hcover : ∀ i x, x ∈ (p i).points → x ∈ root ∨ ∃ k, x = (row k, col k i)) :
    ∃ i j, i ≠ j ∧ ∃ q : IndependentCondition G H cut, q ≤ p i ∧ q ≤ p j := by
  classical
  let E (k : Fin n × Fin n) (a b : One) : Prop :=
    row k.1 ≠ row k.2 ∧ G.Adj (row k.1, a) (row k.2, b)
  have hgood (k : Fin n × Fin n) :
      GoodPair (E k) (range (col k.1)) (range (col k.2)) := by
    by_cases hrow : row k.1 = row k.2
    · intro A hA hAU B hB hBU
      exact ⟨A, Subset.rfl, hAU, B, Subset.rfl, hBU,
        fun a ha b hb he => he.1 hrow⟩
    · intro A hA hAU B hB hBU
      have hAH : A ⊆ {a | (row k.1, a) ∈ H} := by
        intro a ha
        obtain ⟨i, rfl⟩ := hA ha
        exact ((p i).contained _ (hmem i k.1)).1
      have hBH : B ⊆ {b | (row k.2, b) ∈ H} := by
        intro b hb
        obtain ⟨i, rfl⟩ := hB hb
        exact ((p i).contained _ (hmem i k.2)).1
      obtain ⟨A', hA', hAU', B', hB', hBU', hnone⟩ :=
        hweak _ _ hrow A hAH hAU B hBH hBU
      exact ⟨A', hA', hAU', B', hB', hBU', fun a ha b hb he => hnone a ha b hb he.2⟩
  have hOne : ¬ (univ : Set One).Countable := by
    simpa using uncountable_injective_range (id : One → One) injective_id
  obtain ⟨A, hA, hAU, B, hB, hBU, hnone⟩ :=
    finite_good_rectangles (fun k => col k.1) (fun k => col k.2) E hgood
      Finset.univ univ univ hOne hOne
  obtain ⟨i, hi, _⟩ := exists_mem_outside_countable hAU (countable_empty : (∅ : Set One).Countable)
  obtain ⟨j, hj, hji⟩ := exists_mem_outside_countable hBU (countable_singleton i)
  refine ⟨i, j, fun h => hji (mem_singleton_iff.mpr h.symm), ?_⟩
  apply IndependentCondition.compatible_of_cross
  intro x hx y hy hrow
  rcases hcover i x hx with hxroot | ⟨k, rfl⟩
  · exact (p j).independent x (hroot j hxroot) y hy hrow
  · rcases hcover j y hy with hyroot | ⟨l, rfl⟩
    · exact (p i).independent _ hx y (hroot i hyroot) hrow
    · intro he
      exact hnone (k, l) (Finset.mem_univ _) i hi j hj ⟨hrow, he⟩

theorem finite_condition_ccc {G : SimpleGraph BlockVertex} {H : Set BlockVertex}
    (hweak : WeaklyIndependent G H) (cut : One) :
    CountableChainCondition (IndependentCondition G H cut) := by
  classical
  intro A hanti
  by_contra hA
  obtain ⟨e⟩ := one_embeds_in_uncountable hA
  let p : One → IndependentCondition G H cut := fun i => (e i).val
  have hp : Injective p := Subtype.val_injective.comp e.injective
  obtain ⟨index, n, root, row, col, hroot, hmem, hcover⟩ :=
    uniform_finite_family (fun i => (p i).points)
  obtain ⟨i, j, hij, hcompat⟩ := compatible_uniform_family hweak
    (fun i => p (index i)) n root row col hroot hmem hcover
  exact hanti (e (index i)).property (e (index j)).property
    (hp.ne (index.injective.ne hij)) hcompat

end Erdos597

/-! # The finite-clique form of the uncountable Ramsey theorem -/

open Set Function

namespace Erdos597

def CompleteMap {X : Type} (G : SimpleGraph X) (n : ℕ) : Prop :=
  ∃ f : Fin n → X, Injective f ∧ ∀ i j, i ≠ j → G.Adj (f i) (f j)

theorem uncountable_independent_of_countable_neighbors (G : SimpleGraph One)
    (hdegree : ∀ x, {y | G.Adj x y}.Countable) :
    ∃ I : Set One, ¬ I.Countable ∧ I.Pairwise (fun i j => ¬ G.Adj i j) := by
  classical
  let S : Set (Set One) := {I | I.Pairwise (fun i j => ¬ G.Adj i j)}
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c →
      ∃ ub ∈ S, ∀ I ∈ c, I ⊆ ub := by
    intro c hc hcc
    refine ⟨⋃₀ c, ?_, fun I hI => subset_sUnion_of_mem hI⟩
    rintro i ⟨I, hI, hi⟩ j ⟨J, hJ, hj⟩ hij
    obtain rfl | hne := eq_or_ne I J
    · exact hc hI hi hj hij
    · rcases hcc hI hJ hne with hIJ | hJI
      · exact hc hJ (hIJ hi) hj hij
      · exact hc hI hi (hJI hj) hij
  obtain ⟨I, hI⟩ := zorn_subset S hchain
  refine ⟨I, ?_, hI.prop⟩
  intro hcI
  let used : Set One := I ∪ ⋃ i ∈ I, {j | G.Adj i j}
  have hused : used.Countable := hcI.union (hcI.biUnion (fun i hi => hdegree i))
  have hOne : ¬ (univ : Set One).Countable := by
    simpa using uncountable_injective_range (id : One → One) injective_id
  obtain ⟨j, _, hj⟩ := exists_mem_outside_countable hOne hused
  have hjI : j ∉ I := fun h => hj (Or.inl h)
  have hcross (i : One) (hi : i ∈ I) : ¬ G.Adj i j := by
    intro he
    exact hj (Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, he⟩⟩))
  have hnew : insert j I ∈ S := by
    intro a ha b hb hab
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact False.elim (hab rfl)
    · exact fun he => hcross b hb he.symm
    · exact hcross a ha
    · exact hI.prop ha hb hab
  exact hjI (hI.2 hnew (subset_insert j I) (mem_insert j I))

theorem uncountable_independent_or_complete :
    ∀ n : ℕ, ∀ G : SimpleGraph One,
      (∃ I : Set One, ¬ I.Countable ∧ I.Pairwise (fun i j => ¬ G.Adj i j)) ∨
        CompleteMap G n := by
  classical
  intro n
  induction n with
  | zero =>
    intro G
    exact Or.inr ⟨Fin.elim0, (fun i => i.elim0), (fun i => i.elim0)⟩
  | succ n ih =>
    intro G
    by_cases hex : ∃ x, ¬ {y | G.Adj x y}.Countable
    · obtain ⟨x, hx⟩ := hex
      obtain ⟨e⟩ := one_embeds_in_uncountable hx
      let index : One → One := fun i => (e i).val
      have hinj : Injective index := Subtype.val_injective.comp e.injective
      rcases ih (G.comap index) with ⟨I, hI, hnone⟩ | ⟨f, hf, he⟩
      · left
        refine ⟨index '' I, ?_, ?_⟩
        · intro hc
          exact hI (countable_of_injective_of_countable_image hinj.injOn hc)
        · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hij
          exact hnone hi hj (fun h => hij (congrArg index h))
      · right
        let g : Fin (n + 1) → One := Fin.cases x (fun i => index (f i))
        have hg : ∀ i j, i ≠ j → G.Adj (g i) (g j) := by
          intro i j hij
          cases i using Fin.cases with
          | zero =>
            cases j using Fin.cases with
            | zero => exact False.elim (hij rfl)
            | succ j => exact (e (f j)).property
          | succ i =>
            cases j using Fin.cases with
            | zero => exact (e (f i)).property.symm
            | succ j => exact he i j (fun h => hij (congrArg Fin.succ h))
        refine ⟨g, ?_, hg⟩
        intro i j hij
        by_contra hne
        exact (G.ne_of_adj (hg i j hne)) hij
    · left
      apply uncountable_independent_of_countable_neighbors
      intro x
      by_contra h
      exact hex ⟨x, h⟩

theorem uncountable_independent_of_cliqueFree (G : SimpleGraph One) (n : ℕ)
    (hG : G.CliqueFree n) :
    ∃ I : Set One, ¬ I.Countable ∧ I.Pairwise (fun i j => ¬ G.Adj i j) := by
  rcases uncountable_independent_or_complete n G with hI | ⟨f, hf, he⟩
  · exact hI
  · let c : SimpleGraph.Copy (⊤ : SimpleGraph (Fin n)) G :=
      { toHom := { toFun := f, map_rel' := fun hij => he _ _ hij }
        injective' := hf }
    exact False.elim (c.isContained.not_cliqueFree hG)

end Erdos597

/-! # Passing between row families and weakly independent subsets -/

open Set Function

namespace Erdos597

theorem goodPair_graph_swap {G : SimpleGraph BlockVertex} {r s : ℕ} {A B : Set One}
    (h : GoodPair (fun a b => G.Adj (r, a) (s, b)) A B) :
    GoodPair (fun b a => G.Adj (s, b) (r, a)) B A := by
  intro B' hB hBU A' hA hAU
  obtain ⟨A'', hA'', hAU'', B'', hB'', hBU'', hnone⟩ := h A' hA hAU B' hB hBU
  exact ⟨B'', hB'', hBU'', A'', hA'', hAU'',
    fun b hb a ha he => hnone a ha b hb he.symm⟩

def rowUnion (r : ℕ → ℕ) (A : ℕ → Set One) : Set BlockVertex :=
  {x | ∃ n, x.1 = r n ∧ x.2 ∈ A n}

theorem rowUnion_column {r : ℕ → ℕ} (hr : Injective r) (A : ℕ → Set One) (n : ℕ) :
    {b : One | (r n, b) ∈ rowUnion r A} = A n := by
  ext b
  constructor
  · rintro ⟨m, hm, hb⟩
    have hnm : n = m := hr hm
    simpa only [hnm] using hb
  · intro hb
    exact ⟨n, rfl, hb⟩

theorem weak_rows_union {G : SimpleGraph BlockVertex} {r : ℕ → ℕ}
    (hr : StrictMono r) (A : ℕ → Set One) (hA : ∀ n, ¬ (A n).Countable)
    (hgood : ∀ m n, m < n → GoodPair (fun a b => G.Adj (r m, a) (r n, b)) (A m) (A n)) :
    WeaklyIndependent G (rowUnion r A) ∧ (ActiveRows (rowUnion r A)).Infinite := by
  have hcolumn := rowUnion_column hr.injective A
  constructor
  · intro s t hst
    by_cases hs : s ∈ range r
    · obtain ⟨i, rfl⟩ := hs
      by_cases ht : t ∈ range r
      · obtain ⟨j, rfl⟩ := ht
        rw [hcolumn i, hcolumn j]
        have hij : i ≠ j := fun h => hst (congrArg r h)
        rcases lt_or_gt_of_ne hij with hij | hji
        · exact hgood i j hij
        · exact goodPair_graph_swap (hgood j i hji)
      · intro B hB hBU C hC hCU
        apply False.elim
        apply hCU
        apply (countable_empty : (∅ : Set One).Countable).mono
        intro b hb
        obtain ⟨j, hj, hjb⟩ := hC hb
        exact False.elim (ht ⟨j, hj.symm⟩)
    · intro B hB hBU C hC hCU
      apply False.elim
      apply hBU
      apply (countable_empty : (∅ : Set One).Countable).mono
      intro b hb
      obtain ⟨i, hi, hib⟩ := hB hb
      exact False.elim (hs ⟨i, hi.symm⟩)
  · apply (Set.infinite_range_of_injective hr.injective).mono
    rintro s ⟨n, rfl⟩
    change ¬ {b : One | (r n, b) ∈ rowUnion r A}.Countable
    rw [hcolumn n]
    exact hA n

theorem completeMap_of_bad_fibers (G : SimpleGraph BlockVertex) (n : ℕ)
    (row : Fin n → ℕ) (hrow : Injective row) (A : Fin n → Set One)
    (hA : ∀ i, ¬ (A i).Countable)
    (hbad : ∀ i j, i < j → BadPair (fun a b => G.Adj (row i, a) (row j, b)) (A i) (A j))
    (hfibers : ∀ i j, i < j → ∀ b ∈ A j,
      {a | a ∈ A i ∧ G.Adj (row i, a) (row j, b)}.Countable) : CompleteMap G n := by
  obtain ⟨x, hx, he⟩ := select_from_bad_pairs n
    (fun i j a b => G.Adj (row i, a) (row j, b)) A hA hbad hfibers
  refine ⟨fun i => (row i, x i), ?_, ?_⟩
  · intro i j h
    exact hrow (congrArg Prod.fst h)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact he i j hij
    · exact (he j i hji).symm

end Erdos597

/-! # The good homogeneous branch supplies weakly independent rows -/

open Set Function

namespace Erdos597

open WeakFamilies

def GoodHalves (G : SimpleGraph BlockVertex) (D : ℕ → Set One)
    (hD : ∀ r, ¬ (D r).Countable) (k : ℕ) (hk : 0 < k) (f : Fin (k + k) → ℕ) : Prop :=
  let L := tupleIndex hk (fun i => f (Fin.castAdd k i))
  let R := tupleIndex hk (fun i => f (Fin.natAdd k i))
  GoodPair (fun a b => G.Adj (first L, a) (first R, b))
    (sets D (fun r s a b => G.Adj (r, a) (s, b)) hD L)
    (sets D (fun r s a b => G.Adj (r, a) (s, b)) hD R)

theorem weak_rows_of_good_blocks (G : SimpleGraph BlockVertex) (D : ℕ → Set One)
    (hD : ∀ r, ¬ (D r).Countable) (k : ℕ) (hk : 0 < k)
    (Y : Set ℕ) (hY : Y.Infinite)
    (hgood : ∀ f : Fin (k + k) → ℕ, StrictMono f → (∀ i, f i ∈ Y) →
      GoodHalves G D hD k hk f) :
    ∃ H : Set BlockVertex, H ⊆ {x | x.2 ∈ D x.1} ∧
      WeaklyIndependent G H ∧ (ActiveRows H).Infinite := by
  classical
  let E := fun r s a b => G.Adj (r, a) (s, b)
  have : Nonempty Y := hY.nonempty.to_subtype
  have : NoMaxOrder Y := ⟨by
    intro x
    obtain ⟨z, hz, hxz⟩ := hY.exists_gt x.val
    exact ⟨⟨z, hz⟩, hxz⟩⟩
  obtain ⟨seq, hseq⟩ := Nat.exists_strictMono Y
  let a : ℕ → ℕ := fun m => (seq m).val
  have ha : StrictMono a := hseq
  have haY (m : ℕ) : a m ∈ Y := (seq m).property
  let block (m : ℕ) (i : Fin k) : ℕ := a (k * m + i.val)
  have hblock (m : ℕ) : StrictMono (block m) := by
    intro i j hij
    exact ha (Nat.add_lt_add_left hij (k * m))
  let row (m : ℕ) : ℕ := a (k * m)
  have hrow : StrictMono row := by
    intro m n hmn
    exact ha (Nat.mul_lt_mul_of_pos_left hmn hk)
  let A (m : ℕ) : Set One := sets D E hD (tupleIndex hk (block m))
  have hA (m : ℕ) : ¬ (A m).Countable := sets_uncountable D E hD _
  have hfirst (m : ℕ) : first (tupleIndex hk (block m)) = row m := by
    rw [first_tuple hk (block m) (hblock m)]
    rfl
  have hAsub (m : ℕ) : A m ⊆ D (row m) := by
    have h := sets_subset D E hD (tupleIndex hk (block m))
    rwa [hfirst m] at h
  have hAgood (m n : ℕ) (hmn : m < n) :
      GoodPair (fun x y => G.Adj (row m, x) (row n, y)) (A m) (A n) := by
    let f := appendTuple (block m) (block n)
    have hcross (i j : Fin k) : block m i < block n j := by
      apply ha
      have hbase : k * m + k ≤ k * n := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left k (Nat.succ_le_of_lt hmn)
      exact ((Nat.add_lt_add_left i.isLt (k * m)).trans_le hbase).trans_le
        (Nat.le_add_right (k * n) j.val)
    have hf : StrictMono f := appendTuple_strictMono _ _ (hblock m) (hblock n) hcross
    have hfY (i : Fin (k + k)) : f i ∈ Y := by
      dsimp [f, appendTuple]
      split_ifs <;> exact haY _
    have h := hgood f hf hfY
    have hL : (fun i : Fin k => f (Fin.castAdd k i)) = block m := by
      funext i
      exact appendTuple_left _ _ i
    have hR : (fun i : Fin k => f (Fin.natAdd k i)) = block n := by
      funext i
      exact appendTuple_right _ _ i
    simpa only [GoodHalves, hL, hR, hfirst m, hfirst n] using h
  have hH := weak_rows_union hrow A hA hAgood
  refine ⟨rowUnion row A, ?_, hH.1, hH.2⟩
  rintro x ⟨m, hm, hx⟩
  change x.2 ∈ D x.1
  rw [hm]
  exact hAsub m hx

end Erdos597

/-! # Homogeneous thinning under the absence of weakly independent rows -/

open Set Function

namespace Erdos597

def HasWeakRows (G : SimpleGraph BlockVertex) (D : ℕ → Set One) : Prop :=
  ∃ H : Set BlockVertex, H ⊆ {x | x.2 ∈ D x.1} ∧
    WeaklyIndependent G H ∧ (ActiveRows H).Infinite

theorem bad_homogeneous_blocks (G : SimpleGraph BlockVertex) (D : ℕ → Set One)
    (hD : ∀ r, ¬ (D r).Countable) (hNo : ¬ HasWeakRows G D)
    (k : ℕ) (hk : 0 < k) (X : Set ℕ) (hX : X.Infinite) :
    ∃ Y ⊆ X, Y.Infinite ∧ ∀ f : Fin (k + k) → ℕ,
      StrictMono f → (∀ i, f i ∈ Y) → ¬ GoodHalves G D hD k hk f := by
  classical
  let color (f : Fin (k + k) → ℕ) : Bool := decide (GoodHalves G D hD k hk f)
  obtain ⟨c, Y, hYX, hY, hcolor⟩ := infinite_tuple_ramsey (k + k) color X hX
  cases c with
  | false =>
    refine ⟨Y, hYX, hY, ?_⟩
    intro f hf hfY
    exact of_decide_eq_false (hcolor f hf hfY)
  | true =>
    apply False.elim
    apply hNo
    apply weak_rows_of_good_blocks G D hD k hk Y hY
    intro f hf hfY
    exact of_decide_eq_true (hcolor f hf hfY)

theorem simultaneous_bad_blocks (G : SimpleGraph BlockVertex) (D : ℕ → Set One)
    (hD : ∀ r, ¬ (D r).Countable) (hNo : ¬ HasWeakRows G D) :
    ∀ n : ℕ, ∀ X : Set ℕ, X.Infinite →
      ∃ Y ⊆ X, Y.Infinite ∧ ∀ k : ℕ, ∀ hk : 0 < k, k ≤ n →
        ∀ f : Fin (k + k) → ℕ, StrictMono f → (∀ i, f i ∈ Y) →
          ¬ GoodHalves G D hD k hk f := by
  intro n
  induction n with
  | zero =>
    intro X hX
    refine ⟨X, Subset.rfl, hX, ?_⟩
    intro k hk hkn
    exact False.elim (Nat.not_lt_zero 0 (hk.trans_le hkn))
  | succ n ih =>
    intro X hX
    obtain ⟨Y, hYX, hY, hbad⟩ := ih X hX
    obtain ⟨Z, hZY, hZ, hnew⟩ :=
      bad_homogeneous_blocks G D hD hNo (n + 1) (Nat.zero_lt_succ n) Y hY
    refine ⟨Z, hZY.trans hYX, hZ, ?_⟩
    intro k hk hkn f hf hfZ
    rcases Nat.eq_or_lt_of_le hkn with hkeq | hklt
    · subst k
      exact hnew f hf hfZ
    · exact hbad k hk (Nat.le_of_lt_succ hklt) f hf (fun i => hZY (hfZ i))

end Erdos597

/-! # Consecutive finite chains in an increasing sequence -/

open Set Function

namespace Erdos597.WeakFamilies

def intervalIndex (f : ℕ → ℕ) (i j : ℕ) (hij : i < j) : Index :=
  ⟨(Finset.Ico i j).image f,
    ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_Ico.mpr ⟨le_rfl, hij⟩, rfl⟩⟩⟩

theorem interval_mem (f : ℕ → ℕ) (i j : ℕ) (hij : i < j) (x : ℕ) :
    x ∈ (intervalIndex f i j hij).val ↔ ∃ a, i ≤ a ∧ a < j ∧ f a = x := by
  simp [intervalIndex, and_assoc]

theorem first_interval (f : ℕ → ℕ) (hf : StrictMono f) (i j : ℕ) (hij : i < j) :
    first (intervalIndex f i j hij) = f i := by
  apply le_antisymm
  · exact (intervalIndex f i j hij).val.min'_le _
      ((interval_mem f i j hij _).mpr ⟨i, le_rfl, hij, rfl⟩)
  · obtain ⟨a, hai, haj, ha⟩ := (interval_mem f i j hij _).mp
      ((intervalIndex f i j hij).val.min'_mem (intervalIndex f i j hij).property)
    exact (hf.monotone hai).trans_eq ha

theorem last_interval_succ (f : ℕ → ℕ) (hf : StrictMono f) (i j : ℕ) (hij : i ≤ j) :
    last (intervalIndex f i (j + 1) (Nat.lt_succ_of_le hij)) = f j := by
  apply le_antisymm
  · apply (intervalIndex f i (j + 1) (Nat.lt_succ_of_le hij)).val.max'_le
    intro x hx
    obtain ⟨a, hai, haj, rfl⟩ := (interval_mem f i (j + 1) _ x).mp hx
    exact hf.monotone (Nat.le_of_lt_succ haj)
  · exact (intervalIndex f i (j + 1) (Nat.lt_succ_of_le hij)).val.le_max' _
      ((interval_mem f i (j + 1) _ _).mpr ⟨j, hij, Nat.lt_succ_self j, rfl⟩)

theorem interval_singleton (f : ℕ → ℕ) (i : ℕ) :
    intervalIndex f i (i + 1) (Nat.lt_succ_self i) = singleton (f i) := by
  apply Subtype.ext
  simp [intervalIndex, singleton]

theorem erase_last_interval (f : ℕ → ℕ) (hf : StrictMono f)
    (i j : ℕ) (hij : i < j) :
    (intervalIndex f i (j + 1) (hij.trans (Nat.lt_succ_self j))).val.erase (f j) =
      (intervalIndex f i j hij).val := by
  ext x
  constructor
  · intro hx
    have hx' := Finset.mem_erase.mp hx
    obtain ⟨a, hai, haj, ha⟩ := (interval_mem f i (j + 1) _ x).mp hx'.2
    have hane : a ≠ j := fun h => hx'.1 (ha.symm.trans (congrArg f h))
    exact (interval_mem f i j hij x).mpr ⟨a, hai, lt_of_le_of_ne (Nat.le_of_lt_succ haj) hane, ha⟩
  · intro hx
    obtain ⟨a, hai, haj, rfl⟩ := (interval_mem f i j hij x).mp hx
    refine Finset.mem_erase.mpr ⟨hf.injective.ne (ne_of_lt haj), ?_⟩
    exact (interval_mem f i (j + 1) _ _).mpr ⟨a, hai, haj.trans (Nat.lt_succ_self j), rfl⟩

theorem sets_interval_prefix (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) (f : ℕ → ℕ) (hf : StrictMono f)
    (i j k : ℕ) (hij : i < j) (hjk : j ≤ k) :
    sets D E hD (intervalIndex f i k (hij.trans_le hjk)) ⊆
      sets D E hD (intervalIndex f i j hij) := by
  apply sets_subset_of_prefix
  · intro x hx
    obtain ⟨a, hai, haj, rfl⟩ := (interval_mem f i j hij x).mp hx
    exact (interval_mem f i k _ _).mpr ⟨a, hai, haj.trans_le hjk, rfl⟩
  · intro x hx y hy hynot
    obtain ⟨a, hai, haj, rfl⟩ := (interval_mem f i j hij x).mp hx
    obtain ⟨b, hbi, hbk, rfl⟩ := (interval_mem f i k _ y).mp hy
    have hjb : j ≤ b := by
      by_contra h
      exact hynot ((interval_mem f i j hij _).mpr ⟨b, hbi, lt_of_not_ge h, rfl⟩)
    exact hf (haj.trans_le hjb)

theorem shifted_tuple_index (f : ℕ → ℕ) (i j : ℕ) (hij : i < j) :
    tupleIndex (Nat.sub_pos_of_lt hij) (fun a : Fin (j - i) => f (i + a.val)) =
      intervalIndex f i j hij := by
  apply Subtype.ext
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    apply (interval_mem f i j hij _).mpr
    exact ⟨i + a.val, Nat.le_add_right i a.val, by omega, rfl⟩
  · intro hx
    obtain ⟨a, hai, haj, rfl⟩ := (interval_mem f i j hij x).mp hx
    refine Finset.mem_image.mpr ⟨⟨a - i, by omega⟩, Finset.mem_univ _, ?_⟩
    change f (i + (a - i)) = f a
    congr 1
    omega

end Erdos597.WeakFamilies

/-! # Bad pairs between the suffix chains -/

open Set Function

namespace Erdos597

open WeakFamilies

theorem sets_to_first (D : ℕ → Set One) (E : ℕ → ℕ → One → One → Prop)
    (hD : ∀ r, ¬ (D r).Countable) (s : Index) :
    sets D E hD s ⊆ sets D E hD (singleton (first s)) := by
  apply sets_subset_of_prefix
  · intro a ha
    have ha' : a = first s := Finset.mem_singleton.mp ha
    subst a
    exact s.val.min'_mem s.property
  · intro a ha b hb hbt
    have ha' : a = first s := Finset.mem_singleton.mp ha
    subst a
    have hne : b ≠ first s := fun h => hbt (Finset.mem_singleton.mpr h)
    exact lt_of_le_of_ne (s.val.min'_le b hb) hne.symm

theorem bad_interval_pair (G : SimpleGraph BlockVertex) (D : ℕ → Set One)
    (hD : ∀ r, ¬ (D r).Countable) (Y : Set ℕ)
    (f : ℕ → ℕ) (hf : StrictMono f) (hfY : ∀ m, f m ∈ Y)
    (i j n : ℕ) (hij : i < j) (hjn : j < n)
    (hNo : ∀ t : Fin ((j - i) + (j - i)) → ℕ,
      StrictMono t → (∀ a, t a ∈ Y) →
        ¬ GoodHalves G D hD (j - i) (Nat.sub_pos_of_lt hij) t) :
    BadPair (fun a b => G.Adj (f i, a) (f j, b))
      (sets D (fun r s a b => G.Adj (r, a) (s, b)) hD
        (intervalIndex f i n (hij.trans hjn)))
      (sets D (fun r s a b => G.Adj (r, a) (s, b)) hD
        (intervalIndex f j n hjn)) := by
  classical
  let E := fun r s a b => G.Adj (r, a) (s, b)
  let k := j - i
  have hk : 0 < k := Nat.sub_pos_of_lt hij
  let L : Fin k → ℕ := fun a => f (i + a.val)
  let R : Fin k → ℕ := fun a => f (j + a.val)
  have hL : StrictMono L := fun a b hab => hf (Nat.add_lt_add_left hab i)
  have hR : StrictMono R := fun a b hab => hf (Nat.add_lt_add_left hab j)
  have hcross (a b : Fin k) : L a < R b := by
    apply hf
    have ha := a.isLt
    dsimp [k] at ha
    omega
  let t := appendTuple L R
  have ht : StrictMono t := appendTuple_strictMono _ _ hL hR hcross
  have htY (a : Fin (k + k)) : t a ∈ Y := by
    dsimp [t, appendTuple]
    split_ifs <;> exact hfY _
  have htL : (fun a : Fin k => t (Fin.castAdd k a)) = L := by
    funext a
    exact appendTuple_left _ _ a
  have htR : (fun a : Fin k => t (Fin.natAdd k a)) = R := by
    funext a
    exact appendTuple_right _ _ a
  let b := intervalIndex f i j hij
  let c := tupleIndex hk R
  have hLb : tupleIndex hk L = b := shifted_tuple_index f i j hij
  have hbfirst : first b = f i := first_interval f hf i j hij
  have hcfirst : first c = f j := by
    rw [first_tuple hk R hR]
    rfl
  have hNot : ¬ GoodPair (E (f i) (f j)) (sets D E hD b) (sets D E hD c) := by
    have h := hNo t ht htY
    change ¬ GoodHalves G D hD k hk t at h
    dsimp only [GoodHalves] at h
    rw [htL, htR, hLb] at h
    change ¬ GoodPair (E (first b) (first c)) (sets D E hD b) (sets D E hD c) at h
    rwa [hbfirst, hcfirst] at h
  have hCsub : sets D E hD c ⊆ sets D E hD (singleton (f j)) := by
    simpa only [hcfirst] using sets_to_first D E hD c
  have hNotSingleton : ¬ GoodPair (E (f i) (f j))
      (sets D E hD b) (sets D E hD (singleton (f j))) := by
    intro h
    exact hNot (h.mono Subset.rfl hCsub)
  let s := intervalIndex f i (j + 1) (hij.trans (Nat.lt_succ_self j))
  have hslast : last s = f j := last_interval_succ f hf i j hij.le
  have herase : s.val.erase (last s) = b.val := by
    rw [hslast]
    exact erase_last_interval f hf i j hij
  have he : (s.val.erase (last s)).Nonempty := by
    rw [herase]
    exact b.property
  have hp : priorIndex (erasePrior s rfl he) = b := Subtype.ext herase
  have hbad : BadPair (E (f i) (f j)) (sets D E hD s)
      (sets D E hD (singleton (f j))) := by
    have hin : ¬ GoodPair (E (first (priorIndex (erasePrior s rfl he))) (last s))
        (sets D E hD (priorIndex (erasePrior s rfl he)))
        (sets D E hD (singleton (last s))) := by
      simpa only [hp, hslast, hbfirst] using hNotSingleton
    have h := sets_bad_extension D E hD s he hin
    simpa only [hp, hslast, hbfirst] using h
  apply hbad.mono
  · exact sets_interval_prefix D E hD f hf i (j + 1) n
      (hij.trans (Nat.lt_succ_self j)) (Nat.succ_le_of_lt hjn)
  · have h := sets_to_first D E hD (intervalIndex f j n hjn)
    simpa only [first_interval f hf j n hjn] using h

end Erdos597

/-! # Weakly independent rows for upward or downward edge relations -/

open Set Function

namespace Erdos597

open WeakFamilies

def UpwardEdges (G : SimpleGraph BlockVertex) : Prop :=
  ∀ i j : ℕ, ∀ a b : One, i < j → G.Adj (i, a) (j, b) → a < b

def DownwardEdges (G : SimpleGraph BlockVertex) : Prop :=
  ∀ i j : ℕ, ∀ a b : One, i < j → G.Adj (i, a) (j, b) → b ≤ a

theorem badPair_graph_swap {G : SimpleGraph BlockVertex} {r s : ℕ} {A B : Set One}
    (h : BadPair (fun a b => G.Adj (r, a) (s, b)) A B) :
    BadPair (fun b a => G.Adj (s, b) (r, a)) B A := by
  intro B' hB hBU A' hA hAU
  obtain ⟨a, ha, b, hb, he⟩ := h A' hA hAU B' hB hBU
  exact ⟨b, hb, a, ha, he.symm⟩

theorem oriented_weak_rows (G : SimpleGraph BlockVertex) (n : ℕ) (hG : G.CliqueFree n)
    (horient : UpwardEdges G ∨ DownwardEdges G)
    (D : ℕ → Set One) (hD : ∀ r, ¬ (D r).Countable) : HasWeakRows G D := by
  classical
  by_contra hNo
  obtain ⟨Y, hYsub, hY, hbadAll⟩ := simultaneous_bad_blocks G D hD hNo n univ Set.infinite_univ
  have : Nonempty Y := hY.nonempty.to_subtype
  have : NoMaxOrder Y := ⟨by
    intro x
    obtain ⟨z, hz, hxz⟩ := hY.exists_gt x.val
    exact ⟨⟨z, hz⟩, hxz⟩⟩
  obtain ⟨seq, hseq⟩ := Nat.exists_strictMono Y
  let f : ℕ → ℕ := fun i => (seq i).val
  have hf : StrictMono f := hseq
  have hfY (i : ℕ) : f i ∈ Y := (seq i).property
  let E := fun r s a b => G.Adj (r, a) (s, b)
  let A (i : Fin n) : Set One := sets D E hD (intervalIndex f i.val n i.isLt)
  have hA (i : Fin n) : ¬ (A i).Countable := sets_uncountable D E hD _
  have hbad (i j : Fin n) (hij : i < j) :
      BadPair (E (f i.val) (f j.val)) (A i) (A j) := by
    have hk : 0 < j.val - i.val := Nat.sub_pos_of_lt hij
    have hkn : j.val - i.val ≤ n := (Nat.sub_le _ _).trans j.isLt.le
    exact bad_interval_pair G D hD Y f hf hfY i.val j.val n hij j.isLt
      (hbadAll _ hk hkn)
  have hcomplete : CompleteMap G n := by
    rcases horient with hup | hdown
    · apply completeMap_of_bad_fibers G n (fun i => f i.val)
        (hf.injective.comp Fin.val_injective) A hA hbad
      intro i j hij b hb
      apply (countable_initial_segment b).mono
      intro a ha
      exact (hup _ _ _ _ (hf hij) ha.2).le
    · let row (i : Fin n) : ℕ := f i.rev.val
      let B (i : Fin n) : Set One := A i.rev
      have hrow : Injective row := by
        intro i j h
        exact Fin.rev_injective (Fin.val_injective (hf.injective h))
      have hB (i : Fin n) : ¬ (B i).Countable := hA i.rev
      have hbadB (i j : Fin n) (hij : i < j) :
          BadPair (fun a b => G.Adj (row i, a) (row j, b)) (B i) (B j) :=
        badPair_graph_swap (hbad j.rev i.rev (Fin.rev_strictAnti hij))
      apply completeMap_of_bad_fibers G n row hrow B hB hbadB
      intro i j hij b hb
      apply (countable_initial_segment b).mono
      intro a ha
      exact hdown _ _ _ _ (hf (Fin.rev_strictAnti hij)) ha.2.symm
  obtain ⟨f, hf, he⟩ := hcomplete
  let copy : SimpleGraph.Copy (⊤ : SimpleGraph (Fin n)) G :=
    { toHom := { toFun := f, map_rel' := fun h => he _ _ h }
      injective' := hf }
  exact copy.isContained.not_cliqueFree hG

end Erdos597

/-! # A common tail on which all row requirements are dense -/

open Set Function

namespace Erdos597

theorem exists_dense_tail {G : SimpleGraph BlockVertex} {H : Set BlockVertex}
    (hweak : WeaklyIndependent G H) :
    ∃ cut : One, ∀ i p, ∃ q ∈ RowDense G H cut i, q ≤ p := by
  classical
  by_contra h
  push Not at h
  choose target condition obstruction using h
  obtain ⟨r, hr⟩ := exists_uncountable_fiber (fun c => (target c).1.val)
  obtain ⟨e⟩ := one_embeds_in_uncountable hr
  obtain ⟨index, n, root, row, col, hroot, hmem, hcover⟩ :=
    uniform_finite_family (fun i => (condition (e i).val).points)
  let cut : One ↪ One :=
    ⟨fun i => (e (index i)).val, (Subtype.val_injective.comp e.injective).comp index.injective⟩
  have hrow (i : One) : (target (cut i)).1.val = r := (e (index i)).property
  have hrootEmpty : root = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    apply uncountable_injective_range cut cut.injective
    apply (countable_initial_segment v.2).mono
    rintro _ ⟨i, rfl⟩
    exact ((condition (cut i)).contained v (hroot i hv)).2.le
  have hrUncountable : ¬ {b : One | (r, b) ∈ H}.Countable := by
    have hx := (target (cut zeroOne)).1.property
    change ¬ {b : One | ((target (cut zeroOne)).1.val, b) ∈ H}.Countable at hx
    rwa [hrow zeroOne] at hx
  obtain ⟨eB⟩ := one_embeds_in_uncountable hrUncountable
  let y : One ↪ One := ⟨fun i => (eB i).val, Subtype.val_injective.comp eB.injective⟩
  let E (k : Fin n) (a b : One) : Prop := row k ≠ r ∧ G.Adj (row k, a) (r, b)
  have hgood (k : Fin n) : GoodPair (E k) (range (col k)) (range y) := by
    by_cases hkr : row k = r
    · intro A hA hAU B hB hBU
      exact ⟨A, Subset.rfl, hAU, B, Subset.rfl, hBU,
        fun a ha b hb he => he.1 hkr⟩
    · intro A hA hAU B hB hBU
      have hAH : A ⊆ {a | (row k, a) ∈ H} := by
        intro a ha
        obtain ⟨i, rfl⟩ := hA ha
        exact ((condition (cut i)).contained _ (hmem i k)).1
      have hBH : B ⊆ {b | (r, b) ∈ H} := by
        intro b hb
        obtain ⟨i, rfl⟩ := hB hb
        exact (eB i).property
      obtain ⟨A', hA', hAU', B', hB', hBU', hnone⟩ :=
        hweak _ _ hkr A hAH hAU B hBH hBU
      exact ⟨A', hA', hAU', B', hB', hBU', fun a ha b hb he => hnone a ha b hb he.2⟩
  have hOne : ¬ (univ : Set One).Countable := by
    simpa using uncountable_injective_range (id : One → One) injective_id
  obtain ⟨A, hA, hAU, B, hB, hBU, hnone⟩ :=
    finite_good_rectangles col (fun _ => y) E hgood Finset.univ univ univ hOne hOne
  obtain ⟨a, ha, _⟩ := exists_mem_outside_countable hAU (countable_empty : (∅ : Set One).Countable)
  have hyB : ¬ (y '' B).Countable := by
    intro hc
    exact hBU (countable_of_injective_of_countable_image y.injective.injOn hc)
  obtain ⟨b, hb, hlarge⟩ := exists_gt_of_uncountable hyB (max (cut a) (target (cut a)).2)
  obtain ⟨j, hj, rfl⟩ := hb
  let v : BlockVertex := (r, y j)
  have hvH : v ∈ H := (eB j).property
  have hvCut : cut a < v.2 := (le_max_left _ _).trans_lt hlarge
  have hvLarge : (target (cut a)).2 < y j := (le_max_right _ _).trans_lt hlarge
  let single : IndependentCondition G H (cut a) :=
    { points := {v}
      contained := by
        intro x hx
        have hxv : x = v := Finset.mem_singleton.mp hx
        subst x
        exact ⟨hvH, hvCut⟩
      independent := by
        intro x hx z hz hrow
        have hxv : x = v := Finset.mem_singleton.mp hx
        have hzv : z = v := Finset.mem_singleton.mp hz
        subst x
        subst z
        exact False.elim (hrow rfl) }
  have hcross : ∀ x ∈ (condition (cut a)).points, ∀ z ∈ single.points,
      x.1 ≠ z.1 → ¬ G.Adj x z := by
    intro x hx z hz hxr
    have hzv : z = v := Finset.mem_singleton.mp hz
    subst z
    rcases hcover a x hx with hxroot | ⟨k, rfl⟩
    · simp [hrootEmpty] at hxroot
    · intro hedge
      exact hnone k (Finset.mem_univ k) a ha j hj ⟨hxr, hedge⟩
  let q := IndependentCondition.union (condition (cut a)) single hcross
  have hq : q ∈ RowDense G H (cut a) (target (cut a)) := by
    refine ⟨y j, hvLarge, ?_⟩
    change ((target (cut a)).1.val, y j) ∈ (condition (cut a)).points ∪ {v}
    rw [hrow a]
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))
  exact obstruction (cut a) q hq Finset.subset_union_left

theorem independent_refinement_under_MA (hMA : MartinAxiomAlephOne)
    {G : SimpleGraph BlockVertex} {H : Set BlockVertex} (hweak : WeaklyIndependent G H) :
    ∃ S ⊆ H, BlockIndependent G S ∧
      ∀ n ∈ ActiveRows H, ¬ {b : One | (n, b) ∈ S}.Countable := by
  obtain ⟨cut, hdense⟩ := exists_dense_tail hweak
  exact forcing_extract hMA G H cut (finite_condition_ccc hweak cut) hdense

end Erdos597

/-!
# Transfer of a positive block partition theorem

Baumgartner's Theorem 3.5(a) asserts the hypothesis `BlockCliquePartition`
under Martin's axiom for aleph-one dense sets. This file proves its transfer
to the exact finite-graph clause of Erdős 597. The implication from Martin's
axiom to that hypothesis is a separate proof obligation.
-/

open Cardinal Ordinal Set Function
open scoped Cardinal Ordinal

namespace Erdos597

theorem OrdinalGraphRamsey.mono_host {W : Type} {α β γ : Ordinal.{0}}
    {G : SimpleGraph W} (h : OrdinalGraphRamsey β γ G) (hle : β ≤ α) :
    OrdinalGraphRamsey α γ G := by
  classical
  obtain ⟨f⟩ : Nonempty (((· < ·) : β.ToType → β.ToType → Prop) ↪r
      ((· < ·) : α.ToType → α.ToType → Prop)) :=
    type_le_iff'.mp (by simpa only [type_toType] using hle)
  intro red blue hcomp
  rcases h (blue.comap f)ᶜ (blue.comap f) isCompl_compl.symm with
    ⟨s, hs, htype⟩ | ⟨g, hg, hedge⟩
  · left
    refine ⟨f '' s, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
      rw [← hcomp.symm.compl_eq]
      apply (SimpleGraph.compl_adj _ _ _).mpr
      refine ⟨hne, ?_⟩
      exact ((SimpleGraph.compl_adj _ _ _).mp
        (hs hx hy (fun hxy => hne (congrArg f hxy)))).2
    · let e : ((· < ·) : s → s → Prop) ≃r ((· < ·) : (f '' s) → (f '' s) → Prop) :=
        { toEquiv := Equiv.Set.image f s f.injective
          map_rel_iff' := by
            intro a b
            exact f.map_rel_iff }
      exact (type_eq.mpr ⟨e⟩).symm.trans htype
  · right
    exact ⟨fun w => f (g w), f.injective.comp hg, hedge⟩

def BlockCliquePartition : Prop :=
  ∀ n : ℕ, OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) * ω)
    ((ω₁ : Ordinal.{0}) * ω) (⊤ : SimpleGraph (Fin n))

theorem finite_partition_of_block_cliques (h : BlockCliquePartition)
    (W : Type) [Fintype W] (G : SimpleGraph W) :
    OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ))
      ((ω₁ : Ordinal.{0}) * ω) G := by
  classical
  have hle : (ω₁ : Ordinal.{0}) * ω ≤ (ω₁ : Ordinal.{0}) ^ (2 : ℕ) := by
    rw [pow_two]
    exact mul_le_mul_right (omega0_le_omega 1) _
  have hclique := (h (Fintype.card W)).mono_host hle
  intro red blue hcomp
  rcases hclique red blue hcomp with hred | ⟨f, hf, hedge⟩
  · exact Or.inl hred
  · right
    let e := Fintype.equivFin W
    refine ⟨fun w => f (e w), hf.comp e.injective, ?_⟩
    intro a b hab
    apply hedge
    exact e.injective.ne (G.ne_of_adj hab)

end Erdos597

/-! # Uncountable row subsets and independent ordered blocks -/

open Set Function Cardinal Ordinal
open scoped Cardinal Ordinal

namespace Erdos597

theorem type_uncountable_subset {S : Set One} (hS : ¬ S.Countable) :
    typeLT S = (ω₁ : Ordinal.{0}) := by
  apply le_antisymm
  · simpa only [type_toType] using type_set_le S
  · apply le_of_not_gt
    intro hlt
    let : Countable (typeLT S).ToType := Cardinal.countable_toType_of_lt_omega_one hlt
    obtain ⟨e⟩ : Nonempty (((· < ·) : S → S → Prop) ≃r
        ((· < ·) : (typeLT S).ToType → (typeLT S).ToType → Prop)) :=
      type_eq.mp (by rw [type_toType])
    have : Countable S := e.injective.countable
    exact hS (Set.countable_coe_iff.mp this)

theorem one_orderIso_uncountable {S : Set One} (hS : ¬ S.Countable) :
    Nonempty (((· < ·) : One → One → Prop) ≃r ((· < ·) : S → S → Prop)) :=
  type_eq.mp (by rw [type_toType, type_uncountable_subset hS])

theorem independent_uncountable_row (G : SimpleGraph BlockVertex) (n : ℕ)
    (hG : G.CliqueFree n) (H : Set BlockVertex) (r : ℕ)
    (hrow : ¬ {b : One | (r, b) ∈ H}.Countable) :
    ∃ B : Set One, B ⊆ {b : One | (r, b) ∈ H} ∧ ¬ B.Countable ∧
      ∀ a ∈ B, ∀ b ∈ B, ¬ G.Adj (r, a) (r, b) := by
  classical
  obtain ⟨e⟩ := one_embeds_in_uncountable hrow
  let col : One → One := fun b => (e b).val
  have hcol : Injective col := Subtype.val_injective.comp e.injective
  let f : One → BlockVertex := fun b => (r, col b)
  let g : SimpleGraph One := G.comap f
  let copy : SimpleGraph.Copy g G :=
    { toHom := { toFun := f, map_rel' := fun h => h }
      injective' := fun a b h => hcol (congrArg Prod.snd h) }
  have hg : g.CliqueFree n := SimpleGraph.CliqueFree.comap copy.isContained hG
  obtain ⟨I, hI, hind⟩ := uncountable_independent_of_cliqueFree g n hg
  refine ⟨col '' I, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact (e a).property
  · intro hc
    exact hI (countable_of_injective_of_countable_image hcol.injOn hc)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    by_cases hab : a = b
    · subst b
      exact G.loopless.irrefl _
    · exact hind ha hb hab

theorem independent_block_from_rows (G : SimpleGraph BlockVertex) (n : ℕ)
    (hG : G.CliqueFree n) (H : Set BlockVertex)
    (hcross : BlockIndependent G H) (hrows : (ActiveRows H).Infinite) :
    ∃ f : BlockVertex → BlockVertex, Injective f ∧
      (∀ x y, BlockLt (f x) (f y) ↔ BlockLt x y) ∧
      ∀ x y, ¬ G.Adj (f x) (f y) := by
  classical
  have : Nonempty (ActiveRows H) := hrows.nonempty.to_subtype
  have : NoMaxOrder (ActiveRows H) := ⟨by
    intro r
    obtain ⟨s, hs, hrs⟩ := hrows.exists_gt r.val
    exact ⟨⟨s, hs⟩, hrs⟩⟩
  obtain ⟨rows, hrowsMono⟩ := Nat.exists_strictMono (ActiveRows H)
  let row : ℕ → ℕ := fun k => (rows k).val
  have hrowMono : StrictMono row := hrowsMono
  choose B hBsub hBU hBind using
    (fun k => independent_uncountable_row G n hG H (row k) (rows k).property)
  let e (k : ℕ) : ((· < ·) : One → One → Prop) ≃r ((· < ·) : B k → B k → Prop) :=
    Classical.choice (one_orderIso_uncountable (hBU k))
  let f : BlockVertex → BlockVertex := fun x => (row x.1, (e x.1 x.2).val)
  have hmem (x : BlockVertex) : f x ∈ H := hBsub x.1 (e x.1 x.2).property
  have hinj : Injective f := by
    intro x y hxy
    have hrow : x.1 = y.1 := hrowMono.injective (congrArg Prod.fst hxy)
    obtain ⟨i, a⟩ := x
    obtain ⟨j, b⟩ := y
    dsimp at hrow
    subst j
    apply Prod.ext
    · rfl
    · apply (e i).injective
      apply Subtype.ext
      exact congrArg Prod.snd hxy
  refine ⟨f, hinj, ?_, ?_⟩
  · rintro ⟨i, a⟩ ⟨j, b⟩
    change (row i < row j ∨ (row i = row j ∧ (e i a).val < (e j b).val)) ↔
      (i < j ∨ (i = j ∧ a < b))
    constructor
    · rintro (h | ⟨h, hab⟩)
      · exact Or.inl (hrowMono.lt_iff_lt.mp h)
      · have hij := hrowMono.injective h
        subst j
        exact Or.inr ⟨rfl, (e i).map_rel_iff.mp hab⟩
    · rintro (h | ⟨rfl, hab⟩)
      · exact Or.inl (hrowMono h)
      · exact Or.inr ⟨rfl, (e i).map_rel_iff.mpr hab⟩
  · rintro ⟨i, a⟩ ⟨j, b⟩
    by_cases hij : i = j
    · subst j
      exact hBind i _ (e i a).property _ (e i b).property
    · exact hcross _ (hmem (i, a)) _ (hmem (j, b)) (hrowMono.injective.ne hij)

end Erdos597

/-!
# From weakly independent rows to the positive ordinal relation

The remaining combinatorial input is the weakly independent row theorem.
This file states that input explicitly and checks the subsequent implications.
-/

open Set Function Cardinal Ordinal
open scoped Cardinal Ordinal

namespace Erdos597

def WeakIndependentRowsProperty : Prop :=
  ∀ (G : SimpleGraph BlockVertex) (n : ℕ), G.CliqueFree n →
    ∃ H : Set BlockVertex, WeaklyIndependent G H ∧ (ActiveRows H).Infinite

theorem independent_block_under_MA (hMA : MartinAxiomAlephOne)
    {G : SimpleGraph BlockVertex} {n : ℕ} (hG : G.CliqueFree n)
    {H : Set BlockVertex} (hweak : WeaklyIndependent G H) (hrows : (ActiveRows H).Infinite) :
    ∃ f : BlockVertex → BlockVertex, Injective f ∧
      (∀ x y, BlockLt (f x) (f y) ↔ BlockLt x y) ∧
      ∀ x y, ¬ G.Adj (f x) (f y) := by
  obtain ⟨S, hSH, hind, hSrows⟩ := independent_refinement_under_MA hMA hweak
  have hactive : ActiveRows H ⊆ ActiveRows S := fun n hn => hSrows n hn
  exact independent_block_from_rows G n hG S hind (hrows.mono hactive)

abbrev BlockOrdinal := ((ω₁ : Ordinal.{0}) * ω).ToType

private theorem block_ordinal_type :
    type (Prod.Lex (· < ·) (· < ·) : BlockVertex → BlockVertex → Prop) =
      (ω₁ : Ordinal.{0}) * ω := by
  rw [type_prod_lex, type_toType, type_nat_lt]

noncomputable def blockIso :
    (Prod.Lex (· < ·) (· < ·) : BlockVertex → BlockVertex → Prop) ≃r
      ((· < ·) : BlockOrdinal → BlockOrdinal → Prop) :=
  Classical.choice (type_eq.mp (by rw [block_ordinal_type, type_toType]))

theorem block_clique_partition_of_weak_rows (hMA : MartinAxiomAlephOne)
    (hweakRows : WeakIndependentRowsProperty) : BlockCliquePartition := by
  classical
  intro n red blue hcomp
  let G : SimpleGraph BlockVertex := blue.comap blockIso
  by_cases hG : G.CliqueFree n
  · obtain ⟨H, hweak, hrows⟩ := hweakRows G n hG
    obtain ⟨f, hf, horder, hnone⟩ := independent_block_under_MA hMA hG hweak hrows
    let g : BlockVertex → BlockOrdinal := fun x => blockIso (f x)
    have hg : Injective g := blockIso.injective.comp hf
    let e : (Prod.Lex (· < ·) (· < ·) : BlockVertex → BlockVertex → Prop) ≃r
        ((· < ·) : (range g) → (range g) → Prop) :=
      { toEquiv := Equiv.ofInjective g hg
        map_rel_iff' := by
          intro x y
          change blockIso (f x) < blockIso (f y) ↔ Prod.Lex (· < ·) (· < ·) x y
          rw [blockIso.map_rel_iff, Prod.lex_def, Prod.lex_def]
          exact horder x y }
    left
    refine ⟨range g, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hne
      rw [← hcomp.symm.compl_eq]
      apply (SimpleGraph.compl_adj _ _ _).mpr
      exact ⟨hne, hnone x y⟩
    · exact (type_eq.mpr ⟨e⟩).symm.trans block_ordinal_type
  · right
    let f := G.topEmbeddingOfNotCliqueFree hG
    refine ⟨fun i => blockIso (f i), blockIso.injective.comp f.injective, ?_⟩
    intro i j hij
    exact f.map_rel_iff.mpr hij

theorem finite_partition_of_weak_rows (hMA : MartinAxiomAlephOne)
    (hweakRows : WeakIndependentRowsProperty) (W : Type) [Fintype W] (G : SimpleGraph W) :
    OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ))
      ((ω₁ : Ordinal.{0}) * ω) G :=
  finite_partition_of_block_cliques (block_clique_partition_of_weak_rows hMA hweakRows) W G

end Erdos597

/-! # Weak independence and the positive partition theorem -/

open Set Function

namespace Erdos597

def upPart (G : SimpleGraph BlockVertex) : SimpleGraph BlockVertex where
  Adj x y := G.Adj x y ∧
    ((x.1 < y.1 ∧ x.2 < y.2) ∨ (y.1 < x.1 ∧ y.2 < x.2))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

def downPart (G : SimpleGraph BlockVertex) : SimpleGraph BlockVertex where
  Adj x y := G.Adj x y ∧
    ((x.1 < y.1 ∧ y.2 ≤ x.2) ∨ (y.1 < x.1 ∧ x.2 ≤ y.2))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

theorem upPart_upward (G : SimpleGraph BlockVertex) : UpwardEdges (upPart G) := by
  intro i j a b hij h
  rcases h.2 with h | h
  · exact h.2
  · exact False.elim (lt_asymm hij h.1)

theorem downPart_downward (G : SimpleGraph BlockVertex) : DownwardEdges (downPart G) := by
  intro i j a b hij h
  rcases h.2 with h | h
  · exact h.2
  · exact False.elim (lt_asymm hij h.1)

theorem good_pair_of_parts (G : SimpleGraph BlockVertex) (i j : ℕ) (hij : i < j)
    (A B : Set One)
    (hu : GoodPair (fun a b => (upPart G).Adj (i, a) (j, b)) A B)
    (hd : GoodPair (fun a b => (downPart G).Adj (i, a) (j, b)) A B) :
    GoodPair (fun a b => G.Adj (i, a) (j, b)) A B := by
  intro A' hA' hAU B' hB' hBU
  obtain ⟨A₁, hA₁, hA₁U, B₁, hB₁, hB₁U, hnoUp⟩ := hu A' hA' hAU B' hB' hBU
  obtain ⟨A₂, hA₂, hA₂U, B₂, hB₂, hB₂U, hnoDown⟩ :=
    hd A₁ (hA₁.trans hA') hA₁U B₁ (hB₁.trans hB') hB₁U
  refine ⟨A₂, hA₂.trans hA₁, hA₂U, B₂, hB₂.trans hB₁, hB₂U, ?_⟩
  intro a ha b hb hedge
  by_cases hab : a < b
  · exact hnoUp a (hA₂ ha) b (hB₂ hb) ⟨hedge, Or.inl ⟨hij, hab⟩⟩
  · exact hnoDown a ha b hb ⟨hedge, Or.inl ⟨hij, le_of_not_gt hab⟩⟩

theorem increasing_nat_sequence {X : Set ℕ} (hX : X.Infinite) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, f n ∈ X := by
  have : Nonempty X := hX.nonempty.to_subtype
  have : NoMaxOrder X := ⟨by
    intro x
    obtain ⟨y, hy, hxy⟩ := hX.exists_gt x.val
    exact ⟨⟨y, hy⟩, hxy⟩⟩
  obtain ⟨f, hf⟩ := Nat.exists_strictMono X
  exact ⟨fun n => (f n).val, hf, fun n => (f n).property⟩

theorem weak_rows_general (G : SimpleGraph BlockVertex) (n : ℕ) (hG : G.CliqueFree n)
    (D : ℕ → Set One) (hD : ∀ r, ¬ (D r).Countable) : HasWeakRows G D := by
  classical
  have hUp : (upPart G).CliqueFree n :=
    SimpleGraph.CliqueFree.comap (SimpleGraph.Copy.ofLE (upPart G) G (fun _ _ h => h.1)).isContained hG
  obtain ⟨H₁, hH₁, hweak₁, hrows₁⟩ :=
    oriented_weak_rows (upPart G) n hUp (Or.inl (upPart_upward G)) D hD
  obtain ⟨r, hr, hrmem⟩ := increasing_nat_sequence hrows₁
  let liftRow : BlockVertex → BlockVertex := fun x => (r x.1, x.2)
  have hlift : Injective liftRow := by
    intro x y h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    exact Prod.ext (hr.injective hfst) hsnd
  let G₂ := (downPart G).comap liftRow
  let D₂ (i : ℕ) : Set One := {a | (r i, a) ∈ H₁}
  have hD₂ (i : ℕ) : ¬ (D₂ i).Countable := hrmem i
  have hDown : (downPart G).CliqueFree n :=
    SimpleGraph.CliqueFree.comap (SimpleGraph.Copy.ofLE (downPart G) G (fun _ _ h => h.1)).isContained hG
  let copy : SimpleGraph.Copy G₂ (downPart G) :=
    { toHom := { toFun := liftRow, map_rel' := fun h => h }, injective' := hlift }
  have hG₂ : G₂.CliqueFree n := SimpleGraph.CliqueFree.comap copy.isContained hDown
  have horient₂ : DownwardEdges G₂ := by
    intro i j a b hij hedge
    exact downPart_downward G (r i) (r j) a b (hr hij) hedge
  obtain ⟨H₂, hH₂, hweak₂, hrows₂⟩ :=
    oriented_weak_rows G₂ n hG₂ (Or.inr horient₂) D₂ hD₂
  obtain ⟨s, hs, hsmem⟩ := increasing_nat_sequence hrows₂
  let row (i : ℕ) := r (s i)
  let A (i : ℕ) : Set One := {a | (s i, a) ∈ H₂}
  have hA (i : ℕ) : ¬ (A i).Countable := hsmem i
  have hAH₁ (i : ℕ) : A i ⊆ {a | (row i, a) ∈ H₁} := fun a ha => hH₂ ha
  have hgood (i j : ℕ) (hij : i < j) :
      GoodPair (fun a b => G.Adj (row i, a) (row j, b)) (A i) (A j) := by
    have hup := (hweak₁ (row i) (row j) (ne_of_lt (hr (hs hij)))).mono (hAH₁ i) (hAH₁ j)
    have hdown := hweak₂ (s i) (s j) (ne_of_lt (hs hij))
    exact good_pair_of_parts G (row i) (row j) (hr (hs hij)) (A i) (A j) hup hdown
  have hfinal := weak_rows_union (hr.comp hs) A hA hgood
  refine ⟨rowUnion row A, ?_, hfinal.1, hfinal.2⟩
  rintro x ⟨i, hi, hx⟩
  have hmem : (row i, x.2) ∈ H₁ := hAH₁ i hx
  have h := hH₁ hmem
  change x.2 ∈ D x.1
  rwa [hi]

theorem weak_independent_rows : WeakIndependentRowsProperty := by
  intro G n hG
  have hD (r : ℕ) : ¬ (univ : Set One).Countable := by
    simpa using uncountable_injective_range (id : One → One) injective_id
  obtain ⟨H, hH, hweak, hrows⟩ := weak_rows_general G n hG (fun _ => univ) hD
  exact ⟨H, hweak, hrows⟩

theorem block_clique_partition_under_MA (hMA : MartinAxiomAlephOne) : BlockCliquePartition :=
  block_clique_partition_of_weak_rows hMA weak_independent_rows

theorem finite_partition_under_MA (hMA : MartinAxiomAlephOne)
    (W : Type) [Fintype W] (G : SimpleGraph W) :
    OrdinalGraphRamsey ((Ordinal.omega 1) ^ (2 : ℕ)) ((Ordinal.omega 1) * Ordinal.omega0) G :=
  finite_partition_of_weak_rows hMA weak_independent_rows W G

end Erdos597
