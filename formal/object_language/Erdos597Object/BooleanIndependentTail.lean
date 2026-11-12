import Erdos597Object.BooleanIndependentCCC

set_option backward.isDefEq.respectTransparency false

/-! A common ordinal tail makes all row-bound requirements dense. -/

namespace Erdos597Object.BooleanIndependentTail

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanPosetCoding BooleanIndependentConditions BooleanIndependentFilters
open BooleanIndependentFamilies BooleanIndependentCCC BooleanWeightedSupports BooleanWeightedRectangles
open BooleanRowValues BooleanOrientedSupport BooleanColumns CanonicalDomains

variable {B : Type} [CompleteBooleanAlgebra B]

open Classical in
attribute [local instance] propDecidable

noncomputable def extensionValue (base : B) (rows : ℕ → bSet B) (relation : bSet B)
    (cut : Erdos597.One) (requirement : ℕ × Erdos597.One) (points : Finset Vertex) : B :=
  ⨆ extended, denseWeight base rows relation cut requirement extended ⊓
    (forcing base rows relation cut).leValue extended points

theorem common_dense_cut (hB : Flypitch.BA_CCC B) (base : B)
    (rows : ℕ → bSet B) (relation : bSet B)
    (hrows : base ≤ rowFamilyValue blockDomain relation blockOrder rows)
    (hgraph : base ≤ graphValue (V B) blockDomain relation) :
    ∃ cut : Erdos597.One, ∀ requirement points,
      weight base rows relation cut points ≤ extensionValue base rows relation cut requirement points := by
  classical
  by_contra h
  push Not at h
  choose target points hfail using h
  let obstruction := fun cut => weight base rows relation cut (points cut) ⊓
    (extensionValue base rows relation cut (target cut) (points cut))ᶜ
  have hnonzero (cut : Erdos597.One) : obstruction cut ≠ ⊥ := by
    intro hzero
    apply hfail cut
    have hle : weight base rows relation cut (points cut) ≤
        (extensionValue base rows relation cut (target cut) (points cut))ᶜᶜ :=
      (le_compl_iff_disjoint_right).mpr (disjoint_iff.mpr hzero)
    simpa only [compl_compl] using hle
  obtain ⟨r, hr⟩ := Erdos597.exists_uncountable_fiber (fun cut => (target cut).1)
  obtain ⟨e⟩ := Erdos597.one_embeds_in_uncountable hr
  obtain ⟨index, n, root, row, col, hroot, hmem, hcover⟩ :=
    uniform_family (fun i => points (e i).val)
  let cut : Erdos597.One ↪ Erdos597.One :=
    ⟨fun i => (e (index i)).val, (Subtype.val_injective.comp e.injective).comp index.injective⟩
  have hrow (i : Erdos597.One) : (target (cut i)).1 = r := (e (index i)).property
  have hrootEmpty : root = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    have hbound (i : Erdos597.One) : cut i < column v.2.2 := by
      by_contra hnot
      apply hnonzero (cut i)
      change weight base rows relation (cut i) (points (cut i)) ⊓ _ = ⊥
      rw [weight_below_cut base rows relation (cut i) (points (cut i)) v (hroot i hv) hnot,
        bot_inf_eq]
    apply Erdos597.uncountable_injective_range cut cut.injective
    apply (Erdos597.countable_initial_segment (column v.2.2)).mono
    rintro _ ⟨i, rfl⟩
    exact (hbound i).le
  let values := fun i => obstruction (cut i)
  have hvalues (i : Erdos597.One) : values i ≤ weight base rows relation (cut i) (points (cut i)) :=
    inf_le_left
  have huncountable : ¬ {i | values i ≠ ⊥}.Countable := by
    intro hcount
    apply (Set.not_countable_univ : ¬ (Set.univ : Set Erdos597.One).Countable)
    exact hcount.mono (fun i _ => hnonzero (cut i))
  obtain ⟨context, hcontext, hlarge⟩ := positive_uncountable_part hB (checkLabel (B := B))
    (fun _ _ h => checkLabel_discrete h) values huncountable
  have hbase : context ≤ base := by
    have htotal : context ≤ ⨆ i, values i := by
      simpa using hlarge.trans (uncountable_le_outside (checkLabel (B := B))
        (fun _ _ h => checkLabel_discrete h) values ∅ Set.countable_empty)
    exact htotal.trans (iSup_le fun i => (hvalues i).trans
      (weight_le_base base rows relation (cut i) (points (cut i))))
  obtain ⟨hrowLarge, hrowSubset, _, _⟩ :=
    (rowFamilyValue_spec base blockDomain relation blockOrder rows).mp hrows
  let rightValues := fun j : Erdos597.One => allBlockLabel j ∈ᴮ rows r
  have hrightLarge : context ≤
      (injectsIntoValue (V B) (weightedSet (checkLabel (B := B)) rightValues) bSet.omega)ᶜ := by
    have h := restriction_uncountable hB context allBlockLabel (checkLabel (B := B))
      allBlockLabel_discrete (fun _ _ h => checkLabel_discrete h) (fun _ => ⊤) (rows r)
      (allBlockDomain_subset context (rows r) (hbase.trans (hrowSubset r)))
      (hbase.trans (hrowLarge r))
    simpa only [top_inf_eq] using h
  let Cross := {k : Fin n // (row k).unpair.1 ≠ r}
  obtain ⟨left, right, hleft, hright, hleftLarge, hnewRightLarge, hnone⟩ :=
    finite_refinement hB context relation
      (fun k : Cross => rows (row k.val).unpair.1) (fun _ : Cross => rows r)
      (fun k : Cross => fun i => blockLabel (point (row k.val) (col k.val i)).2)
      (fun _ : Cross => allBlockLabel)
      (fun k => point_labels_discrete (col k.val))
      (fun _ => allBlockLabel_discrete)
      (fun k => hbase.trans (good_rows base rows relation hrows hgraph _ _ k.property))
      Finset.univ values rightValues
      (fun k i => (inf_le_right.trans (hvalues i)).trans
        (weight_row_member base rows relation (cut i) (points (cut i)) _ (hmem i k.val)))
      (fun _ _ => inf_le_right) hlarge hrightLarge
  have hleftCover : context ≤ ⨆ i, left i := by
    simpa using hleftLarge.trans (uncountable_le_outside (checkLabel (B := B))
      (fun _ _ h => checkLabel_discrete h) left ∅ Set.countable_empty)
  obtain ⟨i, hi⟩ := exists_nonzero_intersection context left hcontext hleftCover
  let bound := max (cut i) (target (cut i)).2
  let small : Set Erdos597.One := {j | context ⊓ (allBlockLabel j ∈ᴮ boundedDomain bound) ≠ ⊥}
  have hsmall : small.Countable := BooleanCountableAvoidance.possible_members_countable hB context
    allBlockLabel (fun j k hjk => by rw [allBlockLabel_discrete j k hjk, inf_bot_eq])
    (boundedDomain bound) (le_top.trans (boundedDomain_countable bound))
  have hrightCover : context ≤ ⨆ j : {j : Erdos597.One // j ∉ small}, right j.val := by
    apply (hnewRightLarge.trans (uncountable_le_outside (checkLabel (B := B))
      (fun _ _ h => checkLabel_discrete h) right small hsmall)).trans
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    exact le_iSup_of_le ⟨j, hj⟩ le_rfl
  obtain ⟨j, hj⟩ := exists_nonzero_intersection (context ⊓ left i)
    (fun j : {j : Erdos597.One // j ∉ small} => right j.val) hi (inf_le_left.trans hrightCover)
  let key := blockLabelsEquiv j.val
  let v : Vertex := (r, key)
  let joint := (context ⊓ left i) ⊓ right j.val
  have hbound : bound < column key.2 := by
    apply lt_of_not_ge
    intro hle
    apply j.property
    intro hzero
    have hmember : (⊤ : B) ≤ allBlockLabel j.val ∈ᴮ boundedDomain bound :=
      boundedDomain_member bound key.1 key.2 hle
    exact hcontext (bot_unique ((le_inf le_rfl (le_top.trans hmember)).trans_eq hzero))
  have hvCut : cut i < column v.2.2 := (le_max_left _ _).trans_lt hbound
  have hvTarget : (target (cut i)).2 < column v.2.2 := (le_max_right _ _).trans_lt hbound
  have hvalid : joint ≤ weight base rows relation (cut i) (points (cut i)) :=
    (inf_le_left.trans inf_le_right).trans ((hleft i).trans (hvalues i))
  have hvRow : joint ≤ blockLabel v.2 ∈ᴮ rows v.1 := inf_le_right.trans (hright j.val)
  have hsingle : joint ≤ weight base rows relation (cut i) {v} := by
    apply le_inf ((inf_le_left.trans inf_le_left).trans hbase)
    apply le_inf
    · apply le_iInf
      intro x
      apply le_iInf
      intro hx
      have heq : x = v := Finset.mem_singleton.mp hx
      subst x
      simpa only [vertexWeight, ite_eq_left hvCut] using hvRow
    · unfold independentWeight
      apply le_iInf
      intro x
      apply le_iInf
      intro hx
      apply le_iInf
      intro y
      apply le_iInf
      intro hy
      have hxv : x = v := Finset.mem_singleton.mp hx
      have hyv : y = v := Finset.mem_singleton.mp hy
      subst x
      subst y
      simp only [ite_true, le_top]
  have hcross (x : Vertex) (hx : x ∈ points (cut i)) (hxr : x.1 ≠ v.1) :
      joint ≤ (edgeValue (V B) relation (blockLabel x.2) (blockLabel v.2))ᶜ := by
    rcases hcover i x hx with hr | ⟨k, rfl⟩
    · simp [hrootEmpty] at hr
    · let k' : Cross := ⟨k, hxr⟩
      exact hnone k' (Finset.mem_univ k') i j.val
  have hvAmbient : joint ≤ blockLabel v.2 ∈ᴮ blockDomain :=
    bSet.mem_of_mem_subset' ((inf_le_left.trans inf_le_left).trans (hbase.trans (hrowSubset r))) hvRow
  have hunion : joint ≤ weight base rows relation (cut i) (points (cut i) ∪ {v}) := by
    rw [weight_union]
    refine le_inf (le_inf hvalid hsingle) (le_inf ?_ ?_)
    · unfold independentWeight
      apply le_iInf
      intro x
      apply le_iInf
      intro hx
      apply le_iInf
      intro y
      apply le_iInf
      intro hy
      have hyv : y = v := Finset.mem_singleton.mp hy
      subst y
      split_ifs with hxr
      · exact le_top
      · exact hcross x hx hxr
    · unfold independentWeight
      apply le_iInf
      intro x
      apply le_iInf
      intro hx
      have hxv : x = v := Finset.mem_singleton.mp hx
      subst x
      apply le_iInf
      intro y
      apply le_iInf
      intro hy
      split_ifs with hry
      · exact le_top
      · exact reverse_red joint blockDomain relation (blockLabel y.2) (blockLabel v.2)
          ((inf_le_left.trans inf_le_left).trans (hbase.trans hgraph))
          (hvalid.trans (member_ambient base rows relation (cut i) hrowSubset (points (cut i)) y hy))
          hvAmbient (hcross y hy (fun h => hry h.symm))
  let extended := points (cut i) ∪ {v}
  have hrequirement : ∃ x ∈ extended,
      x.1 = (target (cut i)).1 ∧ (target (cut i)).2 < column x.2.2 :=
    ⟨v, Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self v)), (hrow i).symm, hvTarget⟩
  have hextended : joint ≤ extensionValue base rows relation (cut i) (target (cut i)) (points (cut i)) := by
    apply le_iSup_of_le extended
    change joint ≤ denseWeight base rows relation (cut i) (target (cut i)) extended ⊓
      (if points (cut i) ⊆ extended then weight base rows relation (cut i) extended else ⊥)
    rw [denseWeight, ite_eq_left hrequirement, ite_eq_left Finset.subset_union_left, inf_idem]
    exact hunion
  have hnot : joint ≤ (extensionValue base rows relation (cut i) (target (cut i)) (points (cut i)))ᶜ :=
    (inf_le_left.trans inf_le_right).trans ((hleft i).trans inf_le_right)
  exact hj (bot_unique ((le_inf hextended hnot).trans_eq inf_compl_eq_bot))

theorem independent_refinement (base : ScheduledIteration.finalAlgebra)
    (rows : ℕ → bSet ScheduledIteration.finalAlgebra)
    (relation : bSet ScheduledIteration.finalAlgebra)
    (hrows : base ≤ rowFamilyValue blockDomain relation blockOrder rows)
    (hgraph : base ≤ graphValue (V ScheduledIteration.finalAlgebra) blockDomain relation)
    (hindependent : ∀ row, base ≤ BooleanLocalGraphs.independentValue (rows row) relation) :
    ∃ refined, base ≤ rowFamilyValue blockDomain relation blockOrder refined ∧
      (∀ row, base ≤ BooleanLocalGraphs.independentValue (refined row) relation) ∧
      (∀ r s, r ≠ s → base ≤ BooleanRectangles.emptyRectangle relation (refined r) (refined s)) := by
  obtain ⟨cut, hdense⟩ := common_dense_cut ScheduledIteration.finalAlgebra.ccc base rows relation hrows hgraph
  exact BooleanIndependentDensity.forcing_refinement base rows relation cut hrows hindependent
    (forcing_ccc ScheduledIteration.finalAlgebra.ccc base rows relation cut hrows hgraph) hdense

theorem canonical_independent_rows (base : ScheduledIteration.finalAlgebra) (n : ℕ)
    (relation : bSet ScheduledIteration.finalAlgebra)
    (hgraph : base ≤ graphValue (V ScheduledIteration.finalAlgebra) blockDomain relation)
    (hno : base ≤ (blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n) blockDomain
      (BooleanFiniteGraphs.graphName BooleanFiniteGraphs.naturalLabel (⊤ : SimpleGraph (Fin n))) relation)ᶜ) :
    ∃ rows, base ≤ rowFamilyValue blockDomain relation blockOrder rows ∧
      (∀ row, base ≤ BooleanLocalGraphs.independentValue (rows row) relation) ∧
      (∀ r s, r ≠ s → base ≤ BooleanRectangles.emptyRectangle relation (rows r) (rows s)) := by
  obtain ⟨rows, hrows, hindependent⟩ := BooleanWeakRows.canonical_weak_rows base n relation hgraph hno
  exact independent_refinement base rows relation hrows hgraph hindependent

end Erdos597Object.BooleanIndependentTail
