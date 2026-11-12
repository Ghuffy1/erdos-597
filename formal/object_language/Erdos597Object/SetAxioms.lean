import Erdos597Object.CollectionSemantics

set_option backward.isDefEq.respectTransparency false

/-! The elementary ZFC axioms in the ordinary set structure. -/

namespace Erdos597Object.SetAxioms

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open Erdos597Object.SetInterpretation Erdos597Object.OrdinalsInSets
open Erdos597Object.OrdinalPresentation Erdos597Object.CHInSets

@[simp] theorem unionValue_set (x : ZFSet.{0}) :
    unionValue setStructure x = ZFSet.sUnion x := rfl

theorem set_models_emptyset : boolean_realize_sentence setStructure axiomOfEmptyset := by
  simp [axiomOfEmptyset, boolean_realize_sentence, var0, lattice.imp]

theorem set_models_ordered_pairs : boolean_realize_sentence setStructure axiomOfOrderedPairs := by
  simp [axiomOfOrderedPairs, boolean_realize_sentence, bd_biimp,
    var0, var1, var2, var3, ZFSet.pair_inj, lattice.imp, or_iff_not_imp_left]

theorem set_models_extensionality : boolean_realize_sentence setStructure axiomOfExtensionality := by
  simp [axiomOfExtensionality, boolean_realize_sentence, bd_biimp,
    var0, var1, var2, lattice.imp, or_iff_not_imp_left, iff_def]
  intro x y hxy
  exact ZFSet.ext (fun z => ⟨(hxy z).1, (hxy z).2⟩)

theorem set_models_union : boolean_realize_sentence setStructure axiomOfUnion := by
  simp [axiomOfUnion, boolean_realize_sentence, bd_biimp, ZFSet.mem_sUnion,
    var0, var1, var2, lattice.imp, or_iff_not_imp_left, iff_def]
  intro x y
  exact ⟨fun z hz hy => ⟨z, hz, hy⟩, fun z hz hy => ⟨z, hz, hy⟩⟩

theorem set_models_powerset : boolean_realize_sentence setStructure axiomOfPowerset := by
  simp [axiomOfPowerset, boolean_realize_sentence, bd_biimp,
    var0, var1, var2, lattice.imp, or_iff_not_imp_left, iff_def]
  intro x y
  constructor
  · intro h z hz
    exact h hz
  · intro h z hz
    exact h z hz

theorem omega_subset_of_ordinal_inductive (x : ZFSet.{0}) (hx : x.IsOrdinal)
    (hzero : (∅ : ZFSet.{0}) ∈ x)
    (hstep : ∀ a ∈ x, ∃ b ∈ x, a ∈ b) : ZFSet.omega ⊆ x := by
  obtain ⟨a, rfl⟩ := ZFSet.isOrdinal_iff_mem_range_toZFSet.mp hx
  have hn : ∀ n : ℕ, (n : Ordinal.{0}) < a := by
    intro n
    induction n with
    | zero =>
      apply Ordinal.toZFSet_mem_toZFSet_iff.mp
      simpa only [Nat.cast_zero, Ordinal.toZFSet_zero] using hzero
    | succ n ih =>
      obtain ⟨y, hy, hny⟩ := hstep (n : Ordinal.{0}).toZFSet
        (Ordinal.toZFSet_mem_toZFSet_iff.mpr ih)
      obtain ⟨b, hba, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hy
      have hnb : (n : Ordinal.{0}) < b := Ordinal.toZFSet_mem_toZFSet_iff.mp hny
      exact lt_of_le_of_lt (by simpa only [Ordinal.natCast_succ] using Order.succ_le_of_lt hnb) hba
  intro z hz
  obtain ⟨n, rfl⟩ := (mem_omega_iff z).mp hz
  exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (hn n)

theorem set_models_infinity : boolean_realize_sentence setStructure axiomOfInfinity := by
  have hstep : ∀ x ∈ (ZFSet.omega : ZFSet.{0}), ∃ y ∈ ZFSet.omega, x ∈ y := by
    intro x hx
    exact ⟨insert x x, ZFSet.omega_succ hx, by simp⟩
  have hord : ZFSet.omega.IsOrdinal := by
    rw [← omega_toZFSet]
    exact ZFSet.isOrdinal_toZFSet _
  simp [axiomOfInfinity, boolean_realize_sentence, realize_ordinal, ordinalValue_set,
    realize_subset, subsetValue_set, var0, var1, var2, lattice.imp, or_iff_not_imp_left]
  refine ⟨?_, hord, ?_⟩
  · intro x hx
    exact hstep x hx
  · intro x hx hzero hnext
    exact omega_subset_of_ordinal_inductive x hx hzero hnext

theorem set_models_regularity : boolean_realize_sentence setStructure axiomOfRegularity := by
  simp [axiomOfRegularity, boolean_realize_sentence, var0, var1, var2,
    lattice.imp, or_iff_not_imp_left]
  intro x hx
  exact (wellFoundedValue_set x).mp (wellFoundedValue_holds x) x (fun _ h => h) hx

end Erdos597Object.SetAxioms
