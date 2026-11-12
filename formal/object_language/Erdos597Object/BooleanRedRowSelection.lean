import Erdos597Object.BooleanRedCopyFamilies
import Erdos597Object.BooleanUnboundedSequences

set_option backward.isDefEq.respectTransparency false

/-! Simultaneous unbounded row fibers and a ground pattern for a red block copy. -/

namespace Erdos597Object.BooleanRedRowSelection

open Erdos597 Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanFiniteGraphs CanonicalDomains
open BooleanRedCopyFamilies BooleanRedImages BooleanUnboundedRows BooleanUnboundedSequences

variable {B : Type} [CompleteBooleanAlgebra B] {context : B} {blue : bSet B}

theorem bounded_rows (F : Family context blue) (hB : has_dense_omega_closed_subset B)
    (hne : context ≠ ⊥) :
    ∃ lower : B, lower ≠ ⊥ ∧ lower ≤ context ∧ ∃ bounds : Nat → One,
      ∀ n v, bounds n < v.1 → lower ⊓ imageWeight (F.values n) v = ⊥ := by
  have hmembers : ∀ n : Nat, context ≤ F.values (n + 1) zeroOne ∈ᴮ
      weightedSet vertexLabel (fun _ => ⊤) := by
    intro n
    exact bSet.subst_congr_mem_right' (le_top.trans (bSet.bv_symm vertexLabel_domain))
      (F.members (n + 1) zeroOne)
  obtain ⟨lower, hlower, hbase, bounds, hbounds⟩ := BooleanCountableDecision.reflect_members
    hB context vertexLabel (fun n : Nat => F.values (n + 1) zeroOne) hne hmembers
  refine ⟨lower, hlower, hbase, fun n => (bounds n).1, ?_⟩
  intro n
  apply image_rows_bounded
  intro i v hv
  let part := lower ⊓ (F.values n i =ᴮ vertexLabel v)
  have heq : part ≤ bSet.pair (F.values n i) (F.values (n + 1) zeroOne) =ᴮ
      bSet.pair (vertexLabel v) (vertexLabel (bounds n)) :=
    bSet.pair_congr inf_le_right (inf_le_left.trans (hbounds n))
  have hbefore := F.before n (n + 1) i zeroOne (Nat.lt_succ_self n)
  change context ≤ bSet.pair (F.values n i) (F.values (n + 1) zeroOne) ∈ᴮ squareOrder at hbefore
  have hedge : part ≤ edgeValue (V B) squareOrder (vertexLabel v) (vertexLabel (bounds n)) := by
    change part ≤ bSet.pair (vertexLabel v) (vertexLabel (bounds n)) ∈ᴮ squareOrder
    exact bSet.subst_congr_mem_left' heq ((inf_le_left.trans hbase).trans hbefore)
  exact bot_unique (hedge.trans_eq (vertex_after_row v (bounds n) hv))

theorem select_rows (F : Family context blue) (hB : has_dense_omega_closed_subset B)
    (hne : context ≠ ⊥) :
    ∃ lower : B, lower ≠ ⊥ ∧ lower ≤ context ∧ ∃ rows : Nat → One,
      ∀ n, lower ≤ unboundedValue (fun column => imageWeight (F.values n) (rows n, column)) := by
  obtain ⟨base, hbase, hcontext, bounds, hbounds⟩ := bounded_rows F hB hne
  have hcover : ∀ n : Nat, base ≤ ⨆ row : One,
      unboundedValue (fun column => imageWeight (F.values n) (row, column)) := by
    intro n
    exact unboundedRow_cover hB base vertexLabel vertexLabel_discrete (imageWeight (F.values n))
      (bounds n) (hbounds n) (hcontext.trans (F.image_uncountable hB n))
  obtain ⟨lower, hlower, hlow, rows, hrows⟩ :=
    BooleanCountableDecision.decide_countable_family hB base
      (fun n row => unboundedValue (fun column => imageWeight (F.values n) (row, column))) hbase hcover
  exact ⟨lower, hlower, hlow.trans hcontext, rows, hrows⟩

theorem selected_rows_increasing (F : Family context blue) (lower : B)
    (hne : lower ≠ ⊥) (hcontext : lower ≤ context) (rows : Nat → One)
    (hrows : ∀ n, lower ≤ unboundedValue (fun column => imageWeight (F.values n) (rows n, column))) :
    StrictMono rows := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hcover : lower ≤ ⨆ column : One, imageWeight (F.values (n + 1)) (rows (n + 1), column) := by
    apply ((hrows (n + 1)).trans (unbounded_le_tail _ zeroOne)).trans
    exact iSup_le fun column => iSup_le fun _ =>
      le_iSup (fun col => imageWeight (F.values (n + 1)) (rows (n + 1), col)) column
  obtain ⟨column, hpositive⟩ := BooleanWeightedSupports.exists_nonzero_intersection lower
    (fun column => imageWeight (F.values (n + 1)) (rows (n + 1), column)) hne hcover
  let part := lower ⊓ imageWeight (F.values (n + 1)) (rows (n + 1), column)
  apply row_lt_of_unbounded_before part hpositive (rows n)
    (fun col => imageWeight (F.values n) (rows n, col)) (rows (n + 1), column)
    (inf_le_left.trans (hrows n))
  intro col
  apply (le_inf (le_inf ((inf_le_left.trans inf_le_left).trans hcontext) inf_le_right)
    (inf_le_left.trans inf_le_right)).trans
  exact F.images_before n (n + 1) (Nat.lt_succ_self n) (rows n, col) (rows (n + 1), column)

theorem extract_pattern (F : Family context blue) (hB : has_dense_omega_closed_subset B)
    (hne : context ≠ ⊥) :
    ∃ lower : B, lower ≠ ⊥ ∧ lower ≤ context ∧ ∃ (firstRow : One) (pattern : Pattern),
      (∀ n, firstRow < pattern.row n) ∧
      lower ≤ unboundedValue (fun column => imageWeight (F.values 0) (firstRow, column)) ∧
      ∀ n m, lower ≤ imageWeight (F.values (n + 1)) (pattern.point n m) := by
  classical
  obtain ⟨base, hbase, hcontext, rows, hrows⟩ := select_rows F hB hne
  have hrowStrict := selected_rows_increasing F base hbase hcontext rows hrows
  let weight (n : Nat) (sequence : Nat → One) : B :=
    ⨆ (_ : StrictMono sequence ∧ ∀ m, rows (n + 1) < sequence m),
      ⨅ m, imageWeight (F.values (n + 1)) (rows (n + 1), sequence m)
  have hcover : ∀ n, base ≤ ⨆ sequence, weight n sequence := fun n =>
    (hrows (n + 1)).trans (increasing_sequences_cover hB
      (fun col => imageWeight (F.values (n + 1)) (rows (n + 1), col)) (rows (n + 1)))
  obtain ⟨lower, hlower, hlow, columns, hcolumns⟩ :=
    BooleanCountableDecision.decide_countable_family hB base weight hbase hcover
  have hproperties : ∀ n, StrictMono (columns n) ∧ ∀ m, rows (n + 1) < columns n m := by
    intro n
    by_contra hnot
    have hzero : weight n (columns n) = ⊥ := by
      apply bot_unique
      exact iSup_le fun h => (hnot h).elim
    exact hlower (bot_unique ((hcolumns n).trans_eq hzero))
  let pattern : Pattern := {
    row := fun n => rows (n + 1)
    column := columns
    rows_increasing := fun _ _ h => hrowStrict (Nat.add_lt_add_right h 1)
    columns_increasing := fun n => (hproperties n).1
    active := fun n m => (hproperties n).2 m }
  refine ⟨lower, hlower, hlow.trans hcontext, rows 0, pattern,
    fun n => hrowStrict (Nat.zero_lt_succ n), hlow.trans (hrows 0), ?_⟩
  intro n m
  exact (hcolumns n).trans ((iSup_le fun _ => le_rfl).trans (iInf_le _ m))

end Erdos597Object.BooleanRedRowSelection
