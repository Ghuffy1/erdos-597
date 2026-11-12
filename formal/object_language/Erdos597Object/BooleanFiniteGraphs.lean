import Erdos597Object.BooleanOrdinalBridge

set_option backward.isDefEq.respectTransparency false

/-! Finite graph names can be decided on Boolean pieces. -/

namespace Erdos597Object.BooleanFiniteGraphs

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanPosetCoding

variable {B I : Type} [CompleteBooleanAlgebra B]

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

noncomputable def decisionValue (values : I → B) (choice : I → Bool) : B :=
  ⨅ i, if choice i then values i else (values i)ᶜ

theorem finite_decisions (values : I → B) (indices : Finset I) :
    ⊤ ≤ ⨆ choice : I → Bool, ⨅ i ∈ indices, if choice i then values i else (values i)ᶜ := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert a indices ha ih =>
    apply ih.trans
    apply iSup_le
    intro choice
    let rest : B := ⨅ i ∈ indices, if choice i then values i else (values i)ᶜ
    have hcase (b : Bool) : rest ⊓ (if b then values a else (values a)ᶜ) ≤
        ⨆ next : I → Bool, ⨅ i ∈ insert a indices, if next i then values i else (values i)ᶜ := by
      apply le_iSup_of_le (Function.update choice a b)
      apply le_iInf
      intro i
      apply le_iInf
      intro hi
      rcases Finset.mem_insert.mp hi with hia | hi
      · subst i
        simpa only [Function.update_self] using
          (inf_le_right : rest ⊓ (if b then values a else (values a)ᶜ) ≤ _)
      · have hia : i ≠ a := fun h => ha (h ▸ hi)
        rw [Function.update_of_ne hia]
        exact inf_le_left.trans ((iInf_le _ i).trans (iInf_le _ hi))
    exact (sup_inf_inf_compl (x := rest) (y := values a)).symm.le.trans
      (sup_le (hcase true) (hcase false))

theorem decisions_cover [Finite I] (values : I → B) :
    (⨆ choice : I → Bool, decisionValue values choice) = ⊤ := by
  classical
  letI := Fintype.ofFinite I
  apply top_unique
  simpa only [decisionValue, Finset.mem_univ, iInf_true] using
    finite_decisions values Finset.univ

theorem decision_le (values : I → B) (choice : I → Bool) (i : I) :
    decisionValue values choice ≤ if choice i then values i else (values i)ᶜ :=
  iInf_le _ i

noncomputable def labelDomain (label : I → bSet B) : bSet B :=
  weightedSet label (fun _ => ⊤)

noncomputable def relationName (label : I → bSet B) (values : I × I → B) : bSet B :=
  weightedSet (pairLabels label) values

theorem relationName_edge (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (values : I × I → B) (i j : I) :
    edgeValue (V B) (relationName label values) (label i) (label j) = values (i, j) :=
  member_weightedSet_discrete (pairLabels label) (pairLabels_discrete label hdiscrete) values (i, j)

theorem relationName_congr (context : B) (label : I → bSet B) (left right : I × I → B)
    (hvalues : ∀ ij, context ⊓ left ij = context ⊓ right ij) :
    context ≤ relationName label left =ᴮ relationName label right := by
  apply bSet.subset_ext
  · apply bSet.subset_intro
    intro ij
    exact le_iSup_of_le ij (le_inf ((hvalues ij).le.trans inf_le_right) bSet.bv_refl)
  · apply bSet.subset_intro
    intro ij
    exact le_iSup_of_le ij (le_inf ((hvalues ij).symm.le.trans inf_le_right) bSet.bv_refl)

theorem pair_witnesses (label : I → bSet B) (entry : bSet B) :
    (⨆ x : bSet B, (x ∈ᴮ labelDomain label) ⊓
      ⨆ y : bSet B, (y ∈ᴮ labelDomain label) ⊓ (entry =ᴮ bSet.pair x y)) =
      ⨆ ij : I × I, entry =ᴮ pairLabels label ij := by
  have hext : bSet.B_ext (fun x : bSet B =>
      ⨆ y : bSet B, (y ∈ᴮ labelDomain label) ⊓ (entry =ᴮ bSet.pair x y)) :=
    bSet.B_ext_iSup fun y => bSet.B_ext_inf (bSet.B_ext_const _)
      (bSet.B_ext_pair_left (bSet.B_ext_eq_right entry) y)
  unfold labelDomain at *
  rw [weighted_bounded_exists label (fun _ => ⊤) _ hext]
  simp only [top_inf_eq]
  have inner (i : I) : (⨆ y : bSet B, (y ∈ᴮ weightedSet label (fun _ => ⊤)) ⊓
      (entry =ᴮ bSet.pair (label i) y)) = ⨆ j, entry =ᴮ bSet.pair (label i) (label j) := by
    rw [weighted_bounded_exists label (fun _ => ⊤) _
      (bSet.B_ext_pair_right (bSet.B_ext_eq_right entry) (label i))]
    simp only [top_inf_eq]
  simp_rw [inner]
  exact (iSup_prod (f := fun ij : I × I => entry =ᴮ bSet.pair (label ij.1) (label ij.2))).symm

theorem relation_eq_coefficients (context : B) (label : I → bSet B) (relation : bSet B)
    (hrel : context ≤ relationBetweenValue (V B) (labelDomain label) (labelDomain label) relation) :
    context ≤ relation =ᴮ relationName label
      (fun ij => edgeValue (V B) relation (label ij.1) (label ij.2)) := by
  apply bSet.subset_ext
  · apply bSet.subset_intro
    intro a
    let part : B := context ⊓ relation.bval a
    have hmember : part ≤ relation.func a ∈ᴮ relation := inf_le_right.trans (bSet.mem.mk' relation a)
    have hcover : part ≤ ⨆ ij : I × I, relation.func a =ᴮ pairLabels label ij := by
      rw [← pair_witnesses]
      exact lattice.bv_context_apply ((inf_le_left.trans hrel).trans (iInf_le _ (relation.func a))) hmember
    apply (le_inf le_rfl hcover).trans
    apply lattice.bv_cases_right
    intro ij
    have hedge : part ⊓ (relation.func a =ᴮ pairLabels label ij) ≤
        edgeValue (V B) relation (label ij.1) (label ij.2) :=
      (le_inf inf_le_right (inf_le_left.trans hmember)).trans
        (bSet.B_ext_mem_left relation (relation.func a) (pairLabels label ij))
    exact le_iSup_of_le ij (le_inf hedge inf_le_right)
  · apply bSet.subset_intro
    intro ij
    exact inf_le_right

noncomputable def chosenGraph (choice : I × I → Bool) : SimpleGraph I where
  Adj i j := i ≠ j ∧ choice (i, j) = true ∧ choice (j, i) = true
  symm := ⟨fun i j h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

noncomputable def graphCoefficient (graph : SimpleGraph I) (ij : I × I) : B := by
  classical
  exact if graph.Adj ij.1 ij.2 then ⊤ else ⊥

noncomputable def graphName (label : I → bSet B) (graph : SimpleGraph I) : bSet B :=
  relationName label (graphCoefficient graph)

theorem graph_loopless (context : B) (label : I → bSet B) (relation : bSet B)
    (hgraph : context ≤ graphValue (V B) (labelDomain label) relation) (i : I) :
    context ≤ (edgeValue (V B) relation (label i) (label i))ᶜ := by
  have hloop := hgraph.trans (inf_le_right.trans inf_le_left)
  exact lattice.bv_context_apply (hloop.trans (iInf_le _ (label i)))
    (le_top.trans (weight_le_member label (fun _ => ⊤) i))

theorem graph_symmetric (context : B) (label : I → bSet B) (relation : bSet B)
    (hgraph : context ≤ graphValue (V B) (labelDomain label) relation) (i j : I) :
    context ⊓ edgeValue (V B) relation (label i) (label j) ≤
      edgeValue (V B) relation (label j) (label i) := by
  have hsym := hgraph.trans (inf_le_right.trans inf_le_right)
  have hi := lattice.bv_context_apply (hsym.trans (iInf_le _ (label i)))
    (le_top.trans (weight_le_member label (fun _ => ⊤) i))
  have hj := lattice.bv_context_apply (hi.trans (iInf_le _ (label j)))
    (le_top.trans (weight_le_member label (fun _ => ⊤) j))
  exact lattice.le_imp_iff.mp (hj.trans inf_le_left)

theorem chosen_coefficients (context : B) (label : I → bSet B) (relation : bSet B)
    (hgraph : context ≤ graphValue (V B) (labelDomain label) relation)
    (choice : I × I → Bool) (i j : I) :
    (context ⊓ decisionValue (fun ij => edgeValue (V B) relation (label ij.1) (label ij.2)) choice) ⊓
      edgeValue (V B) relation (label i) (label j) =
    (context ⊓ decisionValue (fun ij => edgeValue (V B) relation (label ij.1) (label ij.2)) choice) ⊓
      graphCoefficient (chosenGraph choice) (i, j) := by
  classical
  let values : I × I → B := fun ij => edgeValue (V B) relation (label ij.1) (label ij.2)
  let bound : B := context ⊓ decisionValue values choice
  change bound ⊓ values (i, j) = bound ⊓ (if (chosenGraph choice).Adj i j then ⊤ else ⊥)
  by_cases hadj : (chosenGraph choice).Adj i j
  · rw [if_pos hadj, inf_top_eq]
    apply inf_eq_left.mpr
    exact inf_le_right.trans (by simpa only [hadj.2.1, ↓reduceIte] using decision_le values choice (i, j))
  · rw [if_neg hadj, inf_bot_eq]
    apply bot_unique
    let part : B := bound ⊓ values (i, j)
    have hc : part ≤ context := inf_le_left.trans inf_le_left
    have hd : part ≤ decisionValue values choice := inf_le_left.trans inf_le_right
    have he : part ≤ values (i, j) := inf_le_right
    by_cases hij : i = j
    · subst j
      exact (le_inf he (hc.trans (graph_loopless context label relation hgraph i))).trans
        (by simp only [values, edgeValue_bSet, inf_compl_eq_bot]; exact le_rfl)
    · cases hforward : choice (i, j) with
      | false =>
        have hnegative : part ≤ (values (i, j))ᶜ :=
          hd.trans (by simpa only [hforward, Bool.false_eq_true, ↓reduceIte] using decision_le values choice (i, j))
        exact (le_inf he hnegative).trans (by simp)
      | true =>
        cases hback : choice (j, i) with
        | false =>
          have hnegative : part ≤ (values (j, i))ᶜ :=
            hd.trans (by simpa only [hback, Bool.false_eq_true, ↓reduceIte] using decision_le values choice (j, i))
          have hreverse : part ≤ values (j, i) :=
            (le_inf hc he).trans (graph_symmetric context label relation hgraph i j)
          exact (le_inf hreverse hnegative).trans (by simp)
        | true => exact (hadj ⟨hij, hforward, hback⟩).elim

theorem graph_decision_eq (context : B) (label : I → bSet B) (relation : bSet B)
    (hgraph : context ≤ graphValue (V B) (labelDomain label) relation)
    (choice : I × I → Bool) :
    context ⊓ decisionValue (fun ij => edgeValue (V B) relation (label ij.1) (label ij.2)) choice ≤
      relation =ᴮ graphName label (chosenGraph choice) := by
  apply bSet.bv_trans (inf_le_left.trans (relation_eq_coefficients context label relation
    (hgraph.trans inf_le_left)))
  exact relationName_congr _ label _ _ (fun ij => chosen_coefficients context label relation hgraph choice ij.1 ij.2)

theorem graph_cases [Finite I] (context : B) (label : I → bSet B) (relation : bSet B)
    (hgraph : context ≤ graphValue (V B) (labelDomain label) relation) :
    context ≤ ⨆ graph : SimpleGraph I, relation =ᴮ graphName label graph := by
  have hcover := decisions_cover (fun ij : I × I => edgeValue (V B) relation (label ij.1) (label ij.2))
  calc
    context = context ⊓ (⨆ choice : I × I → Bool,
        decisionValue (fun ij => edgeValue (V B) relation (label ij.1) (label ij.2)) choice) := by
      rw [hcover, inf_top_eq]
    _ ≤ _ := by
      apply lattice.bv_cases_right
      intro choice
      exact le_iSup_of_le (chosenGraph choice) (graph_decision_eq context label relation hgraph choice)

theorem graph_predicate [Finite I] (context : B) (label : I → bSet B) (relation : bSet B)
    (hgraph : context ≤ graphValue (V B) (labelDomain label) relation)
    (predicate : bSet B → B) (hext : bSet.B_ext predicate)
    (hchecked : ∀ graph : SimpleGraph I, context ≤ predicate (graphName label graph)) :
    context ≤ predicate relation := by
  apply (le_inf le_rfl (graph_cases context label relation hgraph)).trans
  apply lattice.bv_cases_right
  intro graph
  exact (le_inf (bSet.bv_symm inf_le_right) (inf_le_left.trans (hchecked graph))).trans
    (hext (graphName label graph) relation)

theorem graphName_edge (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (graph : SimpleGraph I) (i j : I) :
    edgeValue (V B) (graphName label graph) (label i) (label j) = graphCoefficient graph (i, j) :=
  relationName_edge label hdiscrete (graphCoefficient graph) i j

theorem graphName_spec (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥) (graph : SimpleGraph I) :
    ⊤ ≤ graphValue (V B) (labelDomain label) (graphName label graph) := by
  classical
  apply le_inf
  · rw [BooleanFunctionBridge.relationBetween_eq_subset_prod]
    apply bSet.subset_intro
    intro ij
    rw [BooleanFunctionBridge.product_membership]
    apply le_iSup_of_le (label ij.1)
    apply le_inf (le_top.trans (weight_le_member label (fun _ => ⊤) ij.1))
    apply le_iSup_of_le (label ij.2)
    exact le_inf (le_top.trans (weight_le_member label (fun _ => ⊤) ij.2)) bSet.bv_refl
  · apply le_inf
    · have hself : bSet.B_ext (fun x => edgeValue (V B) (graphName label graph) x x) := by
        intro x y
        have hpair : (x =ᴮ y) ⊓ (bSet.pair x x ∈ᴮ graphName label graph) ≤
            bSet.pair x x =ᴮ bSet.pair y y :=
          bSet.pair_congr inf_le_left inf_le_left
        exact bSet.subst_congr_mem_left' hpair inf_le_right
      change ⊤ ≤ ⨅ x : bSet B, lattice.imp (x ∈ᴮ weightedSet label (fun _ => ⊤))
        ((edgeValue (V B) (graphName label graph) x x)ᶜ)
      rw [weighted_bounded_forall label (fun _ => ⊤) _ (bSet.B_ext_compl hself)]
      apply le_iInf
      intro i
      rw [graphName_edge label hdiscrete]
      simp [graphCoefficient, lattice.imp]
    · let symmetry : bSet B → bSet B → B := fun x y =>
        lattice.imp (edgeValue (V B) (graphName label graph) x y)
          (edgeValue (V B) (graphName label graph) y x) ⊓
        lattice.imp (edgeValue (V B) (graphName label graph) y x)
          (edgeValue (V B) (graphName label graph) x y)
      have hleft (y : bSet B) : bSet.B_ext (fun x => symmetry x y) :=
        bSet.B_ext_inf
          (bSet.B_ext_imp (edge_left_ext _ y) (edge_right_ext _ y))
          (bSet.B_ext_imp (edge_right_ext _ y) (edge_left_ext _ y))
      have hright (x : bSet B) : bSet.B_ext (symmetry x) :=
        bSet.B_ext_inf
          (bSet.B_ext_imp (edge_right_ext _ x) (edge_left_ext _ x))
          (bSet.B_ext_imp (edge_left_ext _ x) (edge_right_ext _ x))
      change ⊤ ≤ ⨅ x : bSet B, lattice.imp (x ∈ᴮ weightedSet label (fun _ => ⊤))
        (⨅ y : bSet B, lattice.imp (y ∈ᴮ weightedSet label (fun _ => ⊤)) (symmetry x y))
      rw [weighted_bounded_forall label (fun _ => ⊤) _
        (bSet.B_ext_iInf fun y => bSet.B_ext_imp (bSet.B_ext_const _) (hleft y))]
      apply le_iInf
      intro i
      simp only [lattice.imp, compl_top, bot_sup_eq]
      change ⊤ ≤ ⨅ y : bSet B, lattice.imp (y ∈ᴮ weightedSet label (fun _ => ⊤))
        (symmetry (label i) y)
      rw [weighted_bounded_forall label (fun _ => ⊤) _ (hright (label i))]
      apply le_iInf
      intro j
      unfold symmetry
      rw [graphName_edge label hdiscrete, graphName_edge label hdiscrete]
      by_cases hij : graph.Adj i j <;> simp [graphCoefficient, lattice.imp, hij, graph.adj_comm j i]

noncomputable def naturalLabel {n : ℕ} (i : Fin n) : bSet B := bSet.ofNat i.val

theorem natural_domain (n : ℕ) :
    (⊤ : B) ≤ (bSet.ofNat n : bSet B) =ᴮ labelDomain (naturalLabel (n := n)) := by
  have hp : PSet.Equiv (PSet.ofNat n) (PSet.mk (Fin n) (fun i => PSet.ofNat i.val)) := by
    apply PSet.Mem.ext
    intro x
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := pSet.of_nat_of_mem_of_nat hx
      have hmn : m < n := pSet.lt_of_of_nat_mem ((PSet.Mem.congr_left hm).mp hx)
      exact ⟨⟨m, hmn⟩, hm⟩
    · rintro ⟨i, hi⟩
      exact (PSet.Mem.congr_left hi).mpr (pSet.of_nat_mem_of_lt i.isLt)
  exact bSet.check_eq hp

theorem naturalLabel_discrete {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (naturalLabel (B := B) i =ᴮ naturalLabel j) = ⊥ :=
  bSet.ofNat_inj (fun h => hij (Fin.ext h))

theorem graph_vertices_ext (relation : bSet B) :
    bSet.B_ext (fun vertices => graphValue (V B) vertices relation) := by
  intro x y
  have h := boolean_realize_bounded_formula_congr_head (S := V B) x y (relation :: [])
    (graph (var0 : Term 2) var1)
  simpa only [realize_graph, boolean_realize_bounded_term_var0,
    boolean_realize_bounded_term_var1, V_eq] using! h

theorem graph_edges_ext (vertices : bSet B) :
    bSet.B_ext (fun relation => graphValue (V B) vertices relation) := by
  intro x y
  have h := boolean_realize_bounded_formula_congr_second (S := V B) vertices x y []
    (graph (var0 : Term 2) var1)
  simpa only [realize_graph, boolean_realize_bounded_term_var0,
    boolean_realize_bounded_term_var1, V_eq] using! h

theorem natural_graph_spec {n : ℕ} (graph : SimpleGraph (Fin n)) :
    (⊤ : B) ≤ graphValue (V B) (bSet.ofNat n) (graphName naturalLabel graph) :=
  (le_inf (bSet.bv_symm (natural_domain n))
    (graphName_spec naturalLabel naturalLabel_discrete graph)).trans
    (graph_vertices_ext (graphName naturalLabel graph) (labelDomain naturalLabel) (bSet.ofNat n))

theorem natural_graph_edge {n : ℕ} (graph : SimpleGraph (Fin n)) (i j : Fin n) :
    edgeValue (V B) (graphName naturalLabel graph) (naturalLabel i) (naturalLabel j) =
      graphCoefficient graph (i, j) :=
  graphName_edge naturalLabel naturalLabel_discrete graph i j

theorem natural_graph_cases (context : B) (n : ℕ) (relation : bSet B)
    (hgraph : context ≤ graphValue (V B) (bSet.ofNat n) relation) :
    context ≤ ⨆ graph : SimpleGraph (Fin n), relation =ᴮ graphName naturalLabel graph := by
  apply graph_cases context (naturalLabel (n := n)) relation
  exact (le_inf (le_top.trans (natural_domain n)) hgraph).trans
    (graph_vertices_ext relation (bSet.ofNat n) (labelDomain naturalLabel))

theorem natural_graph_predicate (context : B) (n : ℕ) (relation : bSet B)
    (hgraph : context ≤ graphValue (V B) (bSet.ofNat n) relation)
    (predicate : bSet B → B) (hext : bSet.B_ext predicate)
    (hchecked : ∀ graph : SimpleGraph (Fin n), context ≤ predicate (graphName naturalLabel graph)) :
    context ≤ predicate relation := by
  apply (le_inf le_rfl (natural_graph_cases context n relation hgraph)).trans
  apply lattice.bv_cases_right
  intro graph
  exact (le_inf (bSet.bv_symm inf_le_right) (inf_le_left.trans (hchecked graph))).trans
    (hext (graphName naturalLabel graph) relation)

end Erdos597Object.BooleanFiniteGraphs
