import Erdos597

/-! Reduction of the finite graph quantifier to graphs on finite ordinal codes. -/

open Cardinal Ordinal Function
open scoped Cardinal Ordinal

namespace Erdos597

theorem ordinalGraphRamsey_comap_equiv {V W : Type*} (alpha beta : Ordinal.{0})
    (e : V ≃ W) (G : SimpleGraph W) :
    OrdinalGraphRamsey alpha beta (G.comap e) ↔ OrdinalGraphRamsey alpha beta G := by
  constructor
  · intro h red blue hcompl
    rcases h red blue hcompl with hred | ⟨f, hfinj, hmap⟩
    · exact Or.inl hred
    · refine Or.inr ⟨fun w => f (e.symm w), hfinj.comp e.symm.injective, ?_⟩
      intro a b hab
      apply hmap
      simpa using hab
  · intro h red blue hcompl
    rcases h red blue hcompl with hred | ⟨f, hfinj, hmap⟩
    · exact Or.inl hred
    · exact Or.inr ⟨fun v => f (e v), hfinj.comp e.injective, fun _ _ hab => hmap _ _ hab⟩

theorem finite_universal_iff_fin_codes :
    (∀ (W : Type) [Fintype W] (G : SimpleGraph W), G.CliqueFree 4 →
      OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ)) ((ω₁ : Ordinal.{0}) * ω) G) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
      OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ)) ((ω₁ : Ordinal.{0}) * ω) G) := by
  constructor
  · intro h n G hG
    exact h (Fin n) G hG
  · intro h W _ G hG
    let e : Fin (Fintype.card W) ≃ W := (Fintype.equivFin W).symm
    have hfinite : (G.comap e).CliqueFree 4 :=
      SimpleGraph.CliqueFree.comap (SimpleGraph.Iso.comap e G).toCopy.isContained hG
    exact (ordinalGraphRamsey_comap_equiv _ _ e G).mp (h _ _ hfinite)

theorem exists_fixed_finite_CH_counterexample_code :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)), H.CliqueFree 4 ∧
      ((2 : Cardinal.{0}) ^ ℵ₀ = ℵ₁ →
        ¬ OrdinalGraphRamsey ((ω₁ : Ordinal.{0}) ^ (2 : ℕ)) ((ω₁ : Ordinal.{0}) * ω) H) := by
  obtain ⟨W, hW, G, hG, hbad⟩ := exists_fixed_finite_CH_counterexample
  letI : Finite W := hW
  letI : Fintype W := Fintype.ofFinite W
  let e : Fin (Fintype.card W) ≃ W := (Fintype.equivFin W).symm
  refine ⟨Fintype.card W, G.comap e, ?_, ?_⟩
  · exact SimpleGraph.CliqueFree.comap (SimpleGraph.Iso.comap e G).toCopy.isContained hG
  · intro hCH hRamsey
    exact hbad hCH ((ordinalGraphRamsey_comap_equiv _ _ e G).mp hRamsey)

#check ordinalGraphRamsey_comap_equiv
#check finite_universal_iff_fin_codes
#check exists_fixed_finite_CH_counterexample_code
#print axioms ordinalGraphRamsey_comap_equiv
#print axioms finite_universal_iff_fin_codes
#print axioms exists_fixed_finite_CH_counterexample_code

end Erdos597
