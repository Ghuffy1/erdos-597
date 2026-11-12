import Erdos597Object.BooleanIndependentFamilies

set_option backward.isDefEq.respectTransparency false

/-! The countable chain condition for finite independent conditions on weak rows. -/

namespace Erdos597Object.BooleanIndependentCCC

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanIteration BooleanPosetCoding BooleanIndependentConditions
open BooleanIndependentFamilies BooleanWeightedSupports BooleanWeightedRectangles
open BooleanRowValues BooleanGoodPairs BooleanSymmetricPairs BooleanGraphNeighborhoods
open CanonicalDomains

variable {B : Type} [CompleteBooleanAlgebra B]

open Classical in
attribute [local instance] propDecidable

theorem good_rows (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (hrows : base ≤ rowFamilyValue blockDomain relation blockOrder rows)
    (hgraph : base ≤ graphValue (V B) blockDomain relation)
    (r s : ℕ) (hne : r ≠ s) : base ≤ goodPair relation (rows r) (rows s) := by
  obtain ⟨_, hsubset, hgood, _⟩ :=
    (rowFamilyValue_spec base blockDomain relation blockOrder rows).mp hrows
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · exact hgood r s hrs
  · exact goodPair_swap base blockDomain relation (rows s) (rows r) hgraph
      (hsubset s) (hsubset r) (hgood s r hsr)

theorem member_ambient (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (hsubset : ∀ r, base ≤ rows r ⊆ᴮ blockDomain)
    (points : Finset Vertex) (v : Vertex) (hv : v ∈ points) :
    weight base rows relation cut points ≤ blockLabel v.2 ∈ᴮ blockDomain :=
  bSet.mem_of_mem_subset'
    ((weight_le_base base rows relation cut points).trans (hsubset v.1))
    (weight_row_member base rows relation cut points v hv)

theorem reverse_red (context : B) (ambient relation x y : bSet B)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hx : context ≤ x ∈ᴮ ambient) (hy : context ≤ y ∈ᴮ ambient)
    (hred : context ≤ (edgeValue (V B) relation x y)ᶜ) :
    context ≤ (edgeValue (V B) relation y x)ᶜ := by
  apply (le_compl_iff_disjoint_right).mpr
  apply disjoint_iff.mpr
  exact bot_unique ((le_inf (inf_le_left.trans hred)
    (graph_symmetry context ambient relation y x hgraph hy hx)).trans_eq compl_inf_eq_bot)

theorem uniform_compatible (hB : Flypitch.BA_CCC B) (base : B)
    (rows : ℕ → bSet B) (relation : bSet B) (cut : Erdos597.One)
    (hrows : base ≤ rowFamilyValue blockDomain relation blockOrder rows)
    (hgraph : base ≤ graphValue (V B) blockDomain relation)
    (points : Erdos597.One → Finset Vertex) (values : Erdos597.One → B)
    (hvalid : ∀ i, values i ≤ weight base rows relation cut (points i))
    (hnonzero : ∀ i, values i ≠ ⊥)
    (n : ℕ) (root : Finset Vertex) (row : Fin n → ℕ)
    (col : Fin n → Erdos597.One ↪ Erdos597.One)
    (hroot : ∀ i, root ⊆ points i)
    (hmem : ∀ i k, point (row k) (col k i) ∈ points i)
    (hcover : ∀ i x, x ∈ points i → x ∈ root ∨ ∃ k, x = point (row k) (col k i)) :
    ∃ i j, i ≠ j ∧
      (values i ⊓ values j) ⊓ weight base rows relation cut (points i ∪ points j) ≠ ⊥ := by
  classical
  have huncountable : ¬ {i | values i ≠ ⊥}.Countable := by
    intro hcount
    apply (Set.not_countable_univ : ¬ (Set.univ : Set Erdos597.One).Countable)
    exact hcount.mono (fun i _ => hnonzero i)
  obtain ⟨context, hcontext, hlarge⟩ := positive_uncountable_part hB (checkLabel (B := B))
    (fun _ _ h => checkLabel_discrete h) values huncountable
  have hbase : context ≤ base := by
    have htotal : context ≤ ⨆ i, values i := by
      simpa using hlarge.trans (uncountable_le_outside (checkLabel (B := B))
        (fun _ _ h => checkLabel_discrete h) values ∅ Set.countable_empty)
    exact htotal.trans (iSup_le fun i => (hvalid i).trans (weight_le_base base rows relation cut (points i)))
  let Pairs := {pair : Fin n × Fin n // (row pair.1).unpair.1 ≠ (row pair.2).unpair.1}
  obtain ⟨left, right, hleft, hright, hleftLarge, hrightLarge, hnone⟩ :=
    finite_refinement hB context relation
      (fun pair : Pairs => rows (row pair.val.1).unpair.1)
      (fun pair : Pairs => rows (row pair.val.2).unpair.1)
      (fun pair : Pairs => fun i => blockLabel (point (row pair.val.1) (col pair.val.1 i)).2)
      (fun pair : Pairs => fun i => blockLabel (point (row pair.val.2) (col pair.val.2 i)).2)
      (fun pair => point_labels_discrete (col pair.val.1))
      (fun pair => point_labels_discrete (col pair.val.2))
      (fun pair => hbase.trans (good_rows base rows relation hrows hgraph _ _ pair.property))
      Finset.univ values values
      (fun pair i => (inf_le_right.trans (hvalid i)).trans
        (weight_row_member base rows relation cut (points i) _ (hmem i pair.val.1)))
      (fun pair i => (inf_le_right.trans (hvalid i)).trans
        (weight_row_member base rows relation cut (points i) _ (hmem i pair.val.2)))
      hlarge hlarge
  obtain ⟨i, j, hij, hnonzeroPair⟩ := exists_distinct_overlap context left right hcontext hleftLarge hrightLarge
  let joint := (context ⊓ left i) ⊓ right j
  have hi : joint ≤ weight base rows relation cut (points i) :=
    (inf_le_left.trans inf_le_right).trans ((hleft i).trans (hvalid i))
  have hj : joint ≤ weight base rows relation cut (points j) :=
    inf_le_right.trans ((hright j).trans (hvalid j))
  have hcross (x : Vertex) (hx : x ∈ points i) (y : Vertex) (hy : y ∈ points j)
      (hxy : x.1 ≠ y.1) : joint ≤ (edgeValue (V B) relation (blockLabel x.2) (blockLabel y.2))ᶜ := by
    rcases hcover i x hx with hr | ⟨k, rfl⟩
    · exact hj.trans (weight_independent base rows relation cut (points j) x y (hroot j hr) hy hxy)
    · rcases hcover j y hy with hr | ⟨l, rfl⟩
      · exact hi.trans (weight_independent base rows relation cut (points i) _ y hx (hroot i hr) hxy)
      · let pair : Pairs := ⟨(k, l), hxy⟩
        exact hnone pair (Finset.mem_univ pair) i j
  obtain ⟨_, hsubset, _, _⟩ :=
    (rowFamilyValue_spec base blockDomain relation blockOrder rows).mp hrows
  have hreverse (x : Vertex) (hx : x ∈ points j) (y : Vertex) (hy : y ∈ points i)
      (hxy : x.1 ≠ y.1) : joint ≤ (edgeValue (V B) relation (blockLabel x.2) (blockLabel y.2))ᶜ :=
    reverse_red joint blockDomain relation (blockLabel y.2) (blockLabel x.2)
      ((inf_le_left.trans inf_le_left).trans (hbase.trans hgraph))
      (hi.trans (member_ambient base rows relation cut hsubset (points i) y hy))
      (hj.trans (member_ambient base rows relation cut hsubset (points j) x hx))
      (hcross y hy x hx hxy.symm)
  have hunion : joint ≤ weight base rows relation cut (points i ∪ points j) := by
    rw [weight_union]
    refine le_inf (le_inf hi hj) (le_inf ?_ ?_)
    · unfold independentWeight
      apply le_iInf
      intro x
      apply le_iInf
      intro hx
      apply le_iInf
      intro y
      apply le_iInf
      intro hy
      split_ifs with hxy
      · exact le_top
      · exact hcross x hx y hy hxy
    · unfold independentWeight
      apply le_iInf
      intro x
      apply le_iInf
      intro hx
      apply le_iInf
      intro y
      apply le_iInf
      intro hy
      split_ifs with hxy
      · exact le_top
      · exact hreverse x hx y hy hxy
  refine ⟨i, j, hij, ?_⟩
  intro hzero
  apply hnonzeroPair
  exact bot_unique ((le_inf (le_inf
    ((inf_le_left.trans inf_le_right).trans (hleft i)) (inf_le_right.trans (hright j))) hunion).trans_eq hzero)

theorem forcing_ccc (hB : Flypitch.BA_CCC B) (base : B)
    (rows : ℕ → bSet B) (relation : bSet B) (cut : Erdos597.One)
    (hrows : base ≤ rowFamilyValue blockDomain relation blockOrder rows)
    (hgraph : base ≤ graphValue (V B) blockDomain relation) :
    BooleanCountableChainCondition (forcing base rows relation cut) := by
  classical
  intro J label values hvalid hincompatible
  have hcount : {j | values j ≠ ⊥}.Countable := by
    by_contra hcount
    obtain ⟨e⟩ := Erdos597.one_embeds_in_uncountable hcount
    obtain ⟨index, n, root, row, col, hroot, hmem, hcover⟩ :=
      uniform_family (fun i => label (e i).val)
    obtain ⟨i, j, hij, hpair⟩ := uniform_compatible hB base rows relation cut hrows hgraph
      (fun i => label (e (index i)).val) (fun i => values (e (index i)).val)
      (fun i => hvalid (e (index i)).val) (fun i => (e (index i)).property)
      n root row col hroot hmem hcover
    apply hpair
    simpa only [compatible_eq_union] using hincompatible (e (index i)).val (e (index j)).val
      (fun h => hij (index.injective (e.injective (Subtype.ext h))))
  apply ContextualCCC.cover_of_contextual_injection (checkLabel (B := B)) values (fun _ => le_top)
  · intro i j hij
    rw [checkLabel_discrete hij, inf_bot_eq]
  · exact countable_of_countable_support ⊤ (checkLabel (B := B))
      (fun _ _ h => checkLabel_discrete h) values (by simpa only [top_inf_eq] using hcount)

end Erdos597Object.BooleanIndependentCCC
