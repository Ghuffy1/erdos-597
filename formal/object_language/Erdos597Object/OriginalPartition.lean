import Erdos597
import Erdos597Object.FiniteCodeBridge
import Erdos597Object.PartitionGraphStatement

set_option backward.isDefEq.respectTransparency false

/-! Comparison with the ordinal graph partition relation used in the checked proof. -/

namespace Erdos597Object.OriginalPartition

open Ordinal Set
open Erdos597Object.SetInterpretation Erdos597Object.SetFunctions
open Erdos597Object.GraphCopies Erdos597Object.SetProducts
open Erdos597Object.OrdinalPresentation Erdos597Object.PartitionGraphStatement
open scoped Cardinal Ordinal SimpleGraph

noncomputable section

theorem avoiding_embedding_iff_clique (alpha beta : Ordinal.{0})
    (H : SimpleGraph alpha.ToType) :
    (∃ f : ((· < ·) : beta.ToType → beta.ToType → Prop) ↪r
        ((· < ·) : alpha.ToType → alpha.ToType → Prop),
      ∀ x y, x ≠ y → ¬ H.Adj (f x) (f y)) ↔
      ∃ s, Hᶜ.IsClique s ∧ typeLT s = beta := by
  constructor
  · rintro ⟨f, havoid⟩
    refine ⟨Set.range f, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hne
      exact (SimpleGraph.compl_adj H _ _).mpr
        ⟨hne, havoid x y (fun hxy => hne (congrArg f hxy))⟩
    · let e : ((· < ·) : beta.ToType → beta.ToType → Prop) ≃r
          ((· < ·) : Set.range f → Set.range f → Prop) :=
        { toEquiv := Equiv.ofInjective f f.injective
          map_rel_iff' := f.map_rel_iff }
      exact (type_eq.mpr ⟨e⟩).symm.trans (type_toType beta)
  · rintro ⟨s, hclique, htype⟩
    let e : ((· < ·) : beta.ToType → beta.ToType → Prop) ≃r
        ((· < ·) : s → s → Prop) :=
      Classical.choice (type_eq.mp (by rw [type_toType, htype]))
    let f : ((· < ·) : beta.ToType → beta.ToType → Prop) ↪r
        ((· < ·) : alpha.ToType → alpha.ToType → Prop) :=
      { toEmbedding := ⟨fun x => (e x).val,
          fun x y hxy => e.injective (Subtype.ext hxy)⟩
        map_rel_iff' := e.map_rel_iff }
    refine ⟨f, ?_⟩
    intro x y hxy
    exact ((SimpleGraph.compl_adj H _ _).mp
      (hclique (e x).property (e y).property
        (fun h => hxy (e.injective (Subtype.ext h))))).2

theorem original_iff_ordered_embeddings {W : Type*} (alpha beta : Ordinal.{0})
    (G : SimpleGraph W) :
    Erdos597.OrdinalGraphRamsey alpha beta G ↔
      ∀ H : SimpleGraph alpha.ToType,
        (∃ f : ((· < ·) : beta.ToType → beta.ToType → Prop) ↪r
            ((· < ·) : alpha.ToType → alpha.ToType → Prop),
          ∀ x y, x ≠ y → ¬ H.Adj (f x) (f y)) ∨ G ⊑ H := by
  constructor
  · intro h H
    rcases h Hᶜ H isCompl_compl.symm with hred | ⟨f, hinj, hmap⟩
    · exact Or.inl ((avoiding_embedding_iff_clique alpha beta H).mpr hred)
    · exact Or.inr ⟨⟨⟨f, fun hxy => hmap _ _ hxy⟩, hinj⟩⟩
  · intro h red blue hcomp
    rcases h blue with hred | hcopy
    · obtain ⟨s, hs, htype⟩ := (avoiding_embedding_iff_clique alpha beta blue).mp hred
      exact Or.inl ⟨s, by simpa only [hcomp.symm.compl_eq] using hs, htype⟩
    · let f : G.Copy blue := Classical.choice hcopy
      exact Or.inr ⟨f, f.injective, fun _ _ hxy => f.toHom.map_rel' hxy⟩

theorem original_iff_transported {U V W : Type*} {r : U → U → Prop} {s : V → V → Prop}
    (alpha beta : Ordinal.{0})
    (redIso : ((· < ·) : beta.ToType → beta.ToType → Prop) ≃r r)
    (hostIso : ((· < ·) : alpha.ToType → alpha.ToType → Prop) ≃r s)
    (G : SimpleGraph W) :
    Erdos597.OrdinalGraphRamsey alpha beta G ↔
      ∀ H : SimpleGraph V,
        (∃ f : r ↪r s, ∀ x y, x ≠ y → ¬ H.Adj (f x) (f y)) ∨ G ⊑ H := by
  rw [original_iff_ordered_embeddings]
  constructor
  · intro h H
    rcases h (H.comap hostIso) with ⟨f, havoid⟩ | hcopy
    · refine Or.inl ⟨(redIso.symm.toRelEmbedding.trans f).trans hostIso.toRelEmbedding, ?_⟩
      intro x y hxy
      exact havoid (redIso.symm x) (redIso.symm y)
        (fun heq => hxy (redIso.symm.injective heq))
    · exact Or.inr (hcopy.trans (SimpleGraph.Iso.comap hostIso.toEquiv H).toCopy.isContained)
  · intro h H
    rcases h (H.comap hostIso.symm) with ⟨f, havoid⟩ | hcopy
    · refine Or.inl ⟨(redIso.toRelEmbedding.trans f).trans hostIso.symm.toRelEmbedding, ?_⟩
      intro x y hxy
      exact havoid (redIso x) (redIso y) (fun heq => hxy (redIso.injective heq))
    · exact Or.inr (hcopy.trans (SimpleGraph.Iso.comap hostIso.symm.toEquiv H).toCopy.isContained)

abbrev kappa : ZFSet.{0} := (ω₁ : Ordinal.{0}).toZFSet

def squarePresentation :
    ((· < ·) : ((ω₁ : Ordinal.{0}) ^ (2 : ℕ)).ToType →
      ((ω₁ : Ordinal.{0}) ^ (2 : ℕ)).ToType → Prop) ≃r
      relationOn (ZFSet.prod kappa kappa) (lexOrderSet kappa kappa) := by
  rw [pow_two]
  exact ordinalProductPresentation (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0})

def blockPresentation :
    ((· < ·) : ((ω₁ : Ordinal.{0}) * ω).ToType →
      ((ω₁ : Ordinal.{0}) * ω).ToType → Prop) ≃r
      relationOn (ZFSet.prod ZFSet.omega kappa) (lexOrderSet ZFSet.omega kappa) := by
  rw [← omega_toZFSet]
  exact ordinalProductPresentation (ω : Ordinal.{0}) (ω₁ : Ordinal.{0})

theorem canonical_partition_iff_original :
    finitePartitionValue setStructure (ZFSet.prod kappa kappa) (ZFSet.prod ZFSet.omega kappa)
      (lexOrderSet kappa kappa) (lexOrderSet ZFSet.omega kappa) ↔
      ∀ n (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
        Erdos597.OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ)) ((ω₁ : Ordinal.{0}) * ω) G := by
  rw [finitePartitionValue_iff_graphs]
  constructor
  · intro h n G hG
    exact (original_iff_transported _ _ blockPresentation squarePresentation G).mpr (h n G hG)
  · intro h n G hG
    exact (original_iff_transported _ _ blockPresentation squarePresentation G).mp (h n G hG)

theorem canonical_partition_under_MA (hMA : Erdos597.MartinAxiomAlephOne) :
    finitePartitionValue setStructure (ZFSet.prod kappa kappa) (ZFSet.prod ZFSet.omega kappa)
      (lexOrderSet kappa kappa) (lexOrderSet ZFSet.omega kappa) := by
  apply canonical_partition_iff_original.mpr
  intro n G _
  exact Erdos597.finite_partition_under_MA hMA (Fin n) G

theorem canonical_partition_fails_under_CH (hCH : (2 : Cardinal.{0}) ^ ℵ₀ = ℵ₁) :
    ¬ finitePartitionValue setStructure (ZFSet.prod kappa kappa) (ZFSet.prod ZFSet.omega kappa)
      (lexOrderSet kappa kappa) (lexOrderSet ZFSet.omega kappa) := by
  intro h
  have hfinite := canonical_partition_iff_original.mp h
  exact Erdos597.finite_universal_fails_under_CH hCH
    (Erdos597.finite_universal_iff_fin_codes.mpr hfinite)

end

end Erdos597Object.OriginalPartition
