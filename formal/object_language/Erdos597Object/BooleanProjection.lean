import Erdos597Object.CompletionEmbedding
import Mathlib.Order.GaloisConnection.Basic

set_option backward.isDefEq.respectTransparency false

/-! Canonical projections associated with complete Boolean homomorphisms. -/

namespace Erdos597Object.BooleanProjection

open Set

variable {A B C : Type} [CompleteBooleanAlgebra A]
  [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

def projection (e : CompleteLatticeHom B C) (c : C) : B :=
  sInf {b | c ≤ e b}

theorem le_image_projection (e : CompleteLatticeHom B C) (c : C) :
    c ≤ e (projection e c) := by
  change c ≤ e (sInf {b | c ≤ e b})
  rw [map_sInf]
  apply le_sInf
  rintro _ ⟨b, hb, rfl⟩
  exact hb

theorem projection_le_iff (e : CompleteLatticeHom B C) (c : C) (b : B) :
    projection e c ≤ b ↔ c ≤ e b := by
  constructor
  · intro h
    exact (le_image_projection e c).trans (OrderHomClass.monotone e h)
  · intro h
    exact sInf_le h

theorem projection_galois (e : CompleteLatticeHom B C) :
    GaloisConnection (projection e) e := projection_le_iff e

theorem projection_monotone (e : CompleteLatticeHom B C) : Monotone (projection e) :=
  (projection_galois e).monotone_l

theorem projection_bot (e : CompleteLatticeHom B C) : projection e ⊥ = ⊥ := by
  apply bot_unique
  exact (projection_le_iff e ⊥ ⊥).mpr bot_le

theorem projection_iSup {J : Sort*} (e : CompleteLatticeHom B C) (f : J → C) :
    projection e (⨆ j, f j) = ⨆ j, projection e (f j) :=
  (projection_galois e).l_iSup

theorem projection_sSup (e : CompleteLatticeHom B C) (s : Set C) :
    projection e (sSup s) = sSup (projection e '' s) :=
  (projection_galois e).l_sSup_eq_sSup_image

theorem map_le_map_iff (e : CompleteLatticeHom B C) (hinj : Function.Injective e)
    (b₁ b₂ : B) : e b₁ ≤ e b₂ ↔ b₁ ≤ b₂ := by
  constructor
  · intro h
    have heq : e (b₁ ⊓ b₂) = e b₁ := by
      rw [map_inf, inf_eq_left.mpr h]
    exact inf_eq_left.mp (hinj heq)
  · exact fun h => OrderHomClass.monotone e h

theorem projection_image (e : CompleteLatticeHom B C) (hinj : Function.Injective e)
    (b : B) : projection e (e b) = b := by
  apply le_antisymm
  · exact (projection_le_iff e (e b) b).mpr le_rfl
  · exact (map_le_map_iff e hinj b _).mp (le_image_projection e (e b))

theorem projection_eq_bot_iff (e : CompleteLatticeHom B C) (c : C) :
    projection e c = ⊥ ↔ c = ⊥ := by
  constructor
  · intro h
    have hc := le_image_projection e c
    rw [h, map_bot] at hc
    exact bot_unique hc
  · rintro rfl
    exact projection_bot e

theorem projection_nonzero (e : CompleteLatticeHom B C) {c : C} (hc : c ≠ ⊥) :
    projection e c ≠ ⊥ := fun h => hc ((projection_eq_bot_iff e c).mp h)

theorem projection_id (b : B) : projection (CompleteLatticeHom.id B) b = b := by
  apply eq_of_forall_ge_iff
  intro a
  exact projection_le_iff (CompleteLatticeHom.id B) b a

theorem projection_comp (e : CompleteLatticeHom A B) (f : CompleteLatticeHom B C)
    (c : C) : projection (f.comp e) c = projection e (projection f c) := by
  apply eq_of_forall_ge_iff
  intro a
  rw [projection_le_iff, projection_le_iff, projection_le_iff]
  rfl

theorem projection_inf_image (e : CompleteLatticeHom B C) (c : C) (b : B) :
    projection e (c ⊓ e b) = projection e c ⊓ b := by
  apply eq_of_forall_ge_iff
  intro a
  calc
    projection e (c ⊓ e b) ≤ a ↔ c ⊓ e b ≤ e a := projection_le_iff e _ _
    _ ↔ c ≤ e b ⇨ e a := le_himp_iff.symm
    _ ↔ c ≤ e (b ⇨ a) := by simp only [himp_eq, map_sup, map_compl']
    _ ↔ projection e c ≤ b ⇨ a := (projection_le_iff e c _).symm
    _ ↔ projection e c ⊓ b ≤ a := le_himp_iff

theorem inf_image_nonzero_iff (e : CompleteLatticeHom B C) (c : C) (b : B) :
    c ⊓ e b ≠ ⊥ ↔ projection e c ⊓ b ≠ ⊥ := by
  rw [← projection_inf_image]
  exact (not_congr (projection_eq_bot_iff e (c ⊓ e b))).symm

theorem projection_unique (e : CompleteLatticeHom B C) (p : C → B)
    (hp : ∀ c b, p c ≤ b ↔ c ≤ e b) : p = projection e := by
  funext c
  apply eq_of_forall_ge_iff
  intro b
  exact (hp c b).trans (projection_le_iff e c b).symm

theorem baseProjection_eq {I : Type} (Q : BooleanIteration.BooleanPoset B I) :
    CompletionEmbedding.baseProjection Q = projection (CompletionEmbedding.baseHom Q) :=
  projection_unique _ _ (CompletionEmbedding.baseProjection_le_iff Q)

theorem baseProjection_inf_baseMap {I : Type} (Q : BooleanIteration.BooleanPoset B I)
    (u : PosetCompletion.Completion (BooleanIteration.Condition Q)) (b : B) :
    CompletionEmbedding.baseProjection Q (u ⊓ CompletionEmbedding.baseMap Q b) =
      CompletionEmbedding.baseProjection Q u ⊓ b := by
  rw [baseProjection_eq]
  exact projection_inf_image (CompletionEmbedding.baseHom Q) u b

end Erdos597Object.BooleanProjection
