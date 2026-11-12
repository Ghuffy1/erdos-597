import Erdos597Object.CompletionCardinality
import Mathlib.Order.Hom.CompleteLattice

set_option backward.isDefEq.respectTransparency false

/-! The complete Boolean embedding into the completion of a two-step forcing. -/

namespace Erdos597Object.CompletionEmbedding

open Set TopologicalSpace Flypitch
open Topology.WithLowerSet
open BooleanIteration PosetCompletion

theorem mem_perp_lower_iff {P : Type} [PartialOrder P]
    (S : Set (Topology.WithLowerSet P)) (p : P) :
    toLowerSet p ∈ Sᵖ ↔ ∀ q : P, q ≤ p → toLowerSet q ∉ S := by
  constructor
  · intro hp q hqp hq
    obtain ⟨T, hdisjoint, hT, hpT⟩ := mem_perp_iff.mp hp
    have hlower : IsLowerSet T := Topology.IsLowerSet.isOpen_iff_isLowerSet.mp hT
    have hqT : toLowerSet q ∈ T := hlower hqp hpT
    have hempty : toLowerSet q ∈ (∅ : Set (Topology.WithLowerSet P)) := by
      rw [← hdisjoint]
      exact ⟨hqT, hq⟩
    exact hempty
  · intro h
    apply mem_perp_iff.mpr
    refine ⟨cone p, ?_, cone_open p, le_rfl⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro q ⟨hqp, hq⟩
    exact h (ofLowerSet q) hqp hq

variable {B I : Type} [CompleteBooleanAlgebra B]

def valueOpen (Q : BooleanPoset B I) (b : B) : Set (Topology.WithLowerSet (Condition Q)) :=
  {p | (ofLowerSet p).value ≤ b}

theorem valueOpen_open (Q : BooleanPoset B I) (b : B) : IsOpen (valueOpen Q b) := by
  apply Topology.IsLowerSet.isOpen_iff_isLowerSet.mpr
  intro p q hpq hq
  exact hpq.1.trans hq

theorem valueOpen_perp (Q : BooleanPoset B I) (b : B) :
    (valueOpen Q b)ᵖ = valueOpen Q bᶜ := by
  classical
  ext p
  rw [show p = toLowerSet (ofLowerSet p) from rfl, mem_perp_lower_iff]
  change (∀ q : Condition Q, q ≤ ofLowerSet p → ¬ q.value ≤ b) ↔
    (ofLowerSet p).value ≤ bᶜ
  constructor
  · intro hp
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff.mpr
    by_contra hnonzero
    let q : Condition Q :=
      ⟨(ofLowerSet p).value ⊓ b, (ofLowerSet p).label, hnonzero,
        inf_le_left.trans (ofLowerSet p).valid⟩
    have hqp : q ≤ ofLowerSet p :=
      ⟨inf_le_left, (inf_le_left.trans (ofLowerSet p).valid).trans
        (Q.reflexive (ofLowerSet p).label)⟩
    exact hp q hqp inf_le_right
  · intro hp q hqp hqb
    apply q.nonzero
    apply bot_unique
    calc
      q.value ≤ b ⊓ bᶜ := le_inf hqb (hqp.1.trans hp)
      _ = ⊥ := inf_compl_self b

theorem valueOpen_regular (Q : BooleanPoset B I) (b : B) : is_regular (valueOpen Q b) := by
  apply regular_iff_p_p.mpr
  rw [valueOpen_perp, valueOpen_perp, compl_compl]

def baseMap (Q : BooleanPoset B I) (b : B) : Completion (Condition Q) :=
  ⟨valueOpen Q b, valueOpen_regular Q b⟩

theorem mem_baseMap (Q : BooleanPoset B I) (b : B) (p : Condition Q) :
    toLowerSet p ∈ (baseMap Q b : Set (Topology.WithLowerSet (Condition Q))) ↔
      p.value ≤ b := Iff.rfl

theorem baseMap_monotone (Q : BooleanPoset B I) : Monotone (baseMap Q) := by
  intro b c hbc p hp
  exact hp.trans hbc

theorem baseMap_bot (Q : BooleanPoset B I) : baseMap Q ⊥ = ⊥ := by
  apply Subtype.ext
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact (ofLowerSet p).nonzero (bot_unique hp)

theorem baseMap_top (Q : BooleanPoset B I) : baseMap Q ⊤ = ⊤ := by
  apply Subtype.ext
  ext p
  exact iff_of_true le_top (Set.mem_univ p)

theorem baseMap_inf (Q : BooleanPoset B I) (b c : B) :
    baseMap Q (b ⊓ c) = baseMap Q b ⊓ baseMap Q c := by
  apply Subtype.ext
  ext p
  exact le_inf_iff

theorem baseMap_compl (Q : BooleanPoset B I) (b : B) :
    baseMap Q bᶜ = (baseMap Q b)ᶜ := by
  apply Subtype.ext
  exact (valueOpen_perp Q b).symm

theorem baseMap_sInf (Q : BooleanPoset B I) (s : Set B) :
    baseMap Q (sInf s) = sInf (baseMap Q '' s) := by
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨b, hb, rfl⟩
    exact baseMap_monotone Q (sInf_le hb)
  · intro p hp
    change (ofLowerSet p).value ≤ sInf s
    apply le_sInf
    intro b hb
    have hbelow : sInf (baseMap Q '' s) ≤ baseMap Q b :=
      sInf_le ⟨b, hb, rfl⟩
    exact hbelow hp

theorem baseMap_sSup (Q : BooleanPoset B I) (s : Set B) :
    baseMap Q (sSup s) = sSup (baseMap Q '' s) := by
  have himages : baseMap Q '' (Compl.compl '' s) = Compl.compl '' (baseMap Q '' s) := by
    ext d
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨baseMap Q b, ⟨b, hb, rfl⟩, (baseMap_compl Q b).symm⟩
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨bᶜ, ⟨b, hb, rfl⟩, baseMap_compl Q b⟩
  apply compl_injective
  rw [← baseMap_compl, compl_sSup', baseMap_sInf, compl_sSup', himages]

def baseHom (Q : BooleanPoset B I) : CompleteLatticeHom B (Completion (Condition Q)) where
  toFun := baseMap Q
  map_sInf' := baseMap_sInf Q
  map_sSup' := baseMap_sSup Q

theorem exists_condition_below (Q : BooleanPoset B I) (hcover : (⨆ i, Q.member i) = ⊤)
    (b : B) (hb : b ≠ ⊥) : ∃ p : Condition Q, p.value ≤ b := by
  classical
  have hex : ∃ i, b ⊓ Q.member i ≠ ⊥ := by
    by_contra! h
    apply hb
    calc
      b = b ⊓ (⨆ i, Q.member i) := by rw [hcover, inf_top_eq]
      _ = ⨆ i, b ⊓ Q.member i := inf_iSup_eq b Q.member
      _ = ⊥ := by simp only [h, iSup_bot]
  obtain ⟨i, hi⟩ := hex
  exact ⟨⟨b ⊓ Q.member i, i, hi, inf_le_right⟩, inf_le_left⟩

theorem baseMap_le_iff (Q : BooleanPoset B I) (hcover : (⨆ i, Q.member i) = ⊤)
    (b c : B) : baseMap Q b ≤ baseMap Q c ↔ b ≤ c := by
  constructor
  · intro hbc
    by_contra hnot
    have hnonzero : b ⊓ cᶜ ≠ ⊥ := by
      intro hzero
      apply hnot
      simpa using le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr hzero)
    obtain ⟨p, hp⟩ := exists_condition_below Q hcover (b ⊓ cᶜ) hnonzero
    have hpc : p.value ≤ c := hbc (a := toLowerSet p) (hp.trans inf_le_left)
    apply p.nonzero
    apply bot_unique
    calc
      p.value ≤ c ⊓ cᶜ := le_inf hpc (hp.trans inf_le_right)
      _ = ⊥ := inf_compl_self c
  · intro hbc
    exact baseMap_monotone Q hbc

theorem baseHom_injective (Q : BooleanPoset B I) (hcover : (⨆ i, Q.member i) = ⊤) :
    Function.Injective (baseHom Q) := by
  intro b c heq
  exact le_antisymm ((baseMap_le_iff Q hcover b c).mp heq.le)
    ((baseMap_le_iff Q hcover c b).mp heq.ge)

theorem principal_le_baseMap (Q : BooleanPoset B I) (p : Condition Q) (b : B) :
    principal p ≤ baseMap Q b ↔ p.value ≤ b := by
  constructor
  · intro h
    have hp : toLowerSet p ∈
        (principal p : Set (Topology.WithLowerSet (Condition Q))) :=
      cone_subset_principal p (by change p ≤ p; exact le_rfl)
    exact h hp
  · intro hp
    apply is_regular_stable_subset (valueOpen_regular Q b)
    intro q hq
    exact hq.1.trans hp

def baseProjection (Q : BooleanPoset B I) (u : Completion (Condition Q)) : B :=
  ⨆ p : {p : Condition Q // toLowerSet p ∈
    (u : Set (Topology.WithLowerSet (Condition Q)))}, p.val.value

theorem baseProjection_le_iff (Q : BooleanPoset B I)
    (u : Completion (Condition Q)) (b : B) :
    baseProjection Q u ≤ b ↔ u ≤ baseMap Q b := by
  constructor
  · intro h p hp
    change (ofLowerSet p).value ≤ b
    have hvalue : (ofLowerSet p).value ≤ baseProjection Q u :=
      le_iSup (fun q : {q : Condition Q // toLowerSet q ∈
        (u : Set (Topology.WithLowerSet (Condition Q)))} => q.val.value)
        ⟨ofLowerSet p, hp⟩
    exact hvalue.trans h
  · intro h
    apply iSup_le
    intro p
    exact h p.property

theorem le_baseMap_projection (Q : BooleanPoset B I) (u : Completion (Condition Q)) :
    u ≤ baseMap Q (baseProjection Q u) :=
  (baseProjection_le_iff Q u _).mp le_rfl

theorem baseProjection_baseMap (Q : BooleanPoset B I) (hcover : (⨆ i, Q.member i) = ⊤)
    (b : B) : baseProjection Q (baseMap Q b) = b := by
  apply le_antisymm
  · exact (baseProjection_le_iff Q (baseMap Q b) b).mpr le_rfl
  · exact (baseMap_le_iff Q hcover b _).mp (le_baseMap_projection Q (baseMap Q b))

theorem baseProjection_nonzero (Q : BooleanPoset B I) (u : Completion (Condition Q))
    (hu : u ≠ ⊥) : baseProjection Q u ≠ ⊥ := by
  intro hzero
  apply hu
  have hbound := le_baseMap_projection Q u
  rw [hzero, baseMap_bot] at hbound
  exact bot_unique hbound

theorem baseProjection_principal (Q : BooleanPoset B I) (p : Condition Q) :
    baseProjection Q (principal p) = p.value := by
  apply le_antisymm
  · exact (baseProjection_le_iff Q (principal p) p.value).mpr
      ((principal_le_baseMap Q p p.value).mpr le_rfl)
  · apply le_iSup_of_le ⟨p, cone_subset_principal p (by change p ≤ p; exact le_rfl)⟩
    exact le_rfl

end Erdos597Object.CompletionEmbedding
