import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic

/-! Finite graph codes in the canonical universe of ZFC sets. -/

namespace Erdos597Object.SetCodes

noncomputable def naturalSet (n : ℕ) : ZFSet.{0} := (n : Ordinal).toZFSet

@[simp] theorem naturalSet_zero : naturalSet 0 = ∅ := by
  simp [naturalSet]

theorem naturalSet_succ (n : ℕ) :
    naturalSet (n + 1) = insert (naturalSet n) (naturalSet n) := by
  simpa [naturalSet] using Ordinal.toZFSet_add_one (n : Ordinal.{0})

theorem naturalSet_injective : Function.Injective naturalSet := by
  intro m n h
  have h' := Ordinal.toZFSet_injective h
  exact_mod_cast h'

theorem mem_naturalSet (x : ZFSet.{0}) (n : ℕ) :
    x ∈ naturalSet n ↔ ∃ m < n, naturalSet m = x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [naturalSet_succ, ZFSet.mem_insert_iff, ih]
    constructor
    · rintro (h | ⟨m, hm, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h.symm⟩
      · exact ⟨m, Nat.lt_succ_of_lt hm, h⟩
    · rintro ⟨m, hm, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
      · exact Or.inr ⟨m, hm, h⟩
      · exact Or.inl h.symm

theorem naturalSet_mem_omega (n : ℕ) : naturalSet n ∈ ZFSet.omega := by
  induction n with
  | zero => simpa using ZFSet.omega_zero
  | succ n ih =>
    rw [naturalSet_succ]
    exact ZFSet.omega_succ ih

abbrev Elements (n : ℕ) := {x : ZFSet.{0} // x ∈ naturalSet n}

noncomputable def finiteEquiv (n : ℕ) : Fin n ≃ Elements n :=
  Equiv.ofBijective
    (fun i => ⟨naturalSet i.val, (mem_naturalSet _ _).mpr ⟨i.val, i.isLt, rfl⟩⟩)
    (by
      constructor
      · intro i j h
        exact Fin.ext (naturalSet_injective (congrArg Subtype.val h))
      · intro x
        obtain ⟨m, hm, heq⟩ := (mem_naturalSet x.val n).mp x.property
        exact ⟨⟨m, hm⟩, Subtype.ext heq⟩)

@[simp] theorem finiteEquiv_value (n : ℕ) (i : Fin n) :
    ((finiteEquiv n) i).val = naturalSet i.val := rfl

noncomputable def edgeSet {n : ℕ} (G : SimpleGraph (Fin n)) : ZFSet.{0} :=
  ZFSet.range fun e : {p : Fin n × Fin n // G.Adj p.1 p.2} =>
    ZFSet.pair (naturalSet e.val.1.val) (naturalSet e.val.2.val)

theorem pair_mem_edgeSet {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    ZFSet.pair (naturalSet i.val) (naturalSet j.val) ∈ edgeSet G ↔ G.Adj i j := by
  constructor
  · intro h
    obtain ⟨⟨⟨a, b⟩, hab⟩, heq⟩ := ZFSet.mem_range.mp h
    have parts := ZFSet.pair_inj.mp heq
    have ha : a = i := Fin.ext (naturalSet_injective parts.1)
    have hb : b = j := Fin.ext (naturalSet_injective parts.2)
    simpa [ha, hb] using hab
  · intro h
    exact ZFSet.mem_range.mpr ⟨⟨(i, j), h⟩, rfl⟩

noncomputable def decodedGraph {n : ℕ} (G : SimpleGraph (Fin n)) : SimpleGraph (Elements n) :=
  G.comap (finiteEquiv n).symm

noncomputable def graphIso {n : ℕ} (G : SimpleGraph (Fin n)) : decodedGraph G ≃g G :=
  SimpleGraph.Iso.comap (finiteEquiv n).symm G

theorem decodedGraph_adj {n : ℕ} (G : SimpleGraph (Fin n)) (x y : Elements n) :
    (decodedGraph G).Adj x y ↔ ZFSet.pair x.val y.val ∈ edgeSet G := by
  obtain ⟨i, rfl⟩ := (finiteEquiv n).surjective x
  obtain ⟨j, rfl⟩ := (finiteEquiv n).surjective y
  simp [decodedGraph, pair_mem_edgeSet]

theorem decodedGraph_cliqueFree {n k : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree k) : (decodedGraph G).CliqueFree k :=
  SimpleGraph.CliqueFree.comap (graphIso G).toCopy.isContained hG

#print axioms naturalSet_mem_omega
#print axioms finiteEquiv
#print axioms pair_mem_edgeSet
#print axioms decodedGraph_adj
#print axioms decodedGraph_cliqueFree

end Erdos597Object.SetCodes
