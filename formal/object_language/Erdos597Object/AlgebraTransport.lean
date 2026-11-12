import Erdos597Object.ScheduledIteration

set_option backward.isDefEq.respectTransparency false

/-! Transporting complete algebras and requirement data through exact identifications. -/

namespace Erdos597Object.AlgebraTransport

open IterationSystems SystemGluing IterationNameTransport
open scoped Cardinal

theorem castHom_comp {A B C : Algebra} (hAB : A = B) (hBC : B = C) :
    (castHom hBC).comp (castHom hAB) = castHom (hAB.trans hBC) := by
  cases hAB
  cases hBC
  rfl

theorem castHom_injective {A B : Algebra} (h : A = B) : Function.Injective (castHom h) := by
  cases h
  exact Function.injective_id

theorem mapPoset_id {B I : Type} [CompleteBooleanAlgebra B]
    (P : BooleanIteration.BooleanPoset B I) : mapPoset (CompleteLatticeHom.id B) P = P :=
  PosetStageCapture.booleanPoset_ext rfl rfl

theorem mapPoset_comp {A B C I : Type} [CompleteBooleanAlgebra A]
    [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]
    (f : CompleteLatticeHom A B) (g : CompleteLatticeHom B C)
    (P : BooleanIteration.BooleanPoset A I) :
    mapPoset g (mapPoset f P) = mapPoset (g.comp f) P :=
  PosetStageCapture.booleanPoset_ext rfl rfl

def mapRequirement {A B I D : Type} [CompleteBooleanAlgebra A] [CompleteBooleanAlgebra B]
    (f : CompleteLatticeHom A B)
    (data : Option (BooleanIteration.BooleanPoset A I × (D → I → A))) :
    Option (BooleanIteration.BooleanPoset B I × (D → I → B)) :=
  data.map (fun r => (mapPoset f r.1, fun d i => f (r.2 d i)))

theorem mapRequirement_id {A I D : Type} [CompleteBooleanAlgebra A]
    (data : Option (BooleanIteration.BooleanPoset A I × (D → I → A))) :
    mapRequirement (CompleteLatticeHom.id A) data = data := by
  cases data with
  | none => rfl
  | some r =>
    change some (mapPoset (CompleteLatticeHom.id A) r.1, r.2) = some r
    rw [mapPoset_id]

theorem mapRequirement_comp {A B C I D : Type} [CompleteBooleanAlgebra A]
    [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]
    (f : CompleteLatticeHom A B) (g : CompleteLatticeHom B C)
    (data : Option (BooleanIteration.BooleanPoset A I × (D → I → A))) :
    mapRequirement g (mapRequirement f data) = mapRequirement (g.comp f) data := by
  cases data with
  | none => rfl
  | some r =>
    change some (mapPoset g (mapPoset f r.1), fun d i => g (f (r.2 d i))) =
      some (mapPoset (g.comp f) r.1, fun d i => g (f (r.2 d i)))
    rw [mapPoset_comp]

theorem requirementAt_cast {A B : Algebra} {I D : Type} (h : A = B)
    (hI : Cardinal.mk I ≤ Cardinal.aleph 1) (hD : Cardinal.mk D ≤ Cardinal.aleph 1)
    (code : CanonicalIteration.Index) :
    mapRequirement (castHom h) (RequirementCodes.requirementAt A.card_le hI hD code) =
      RequirementCodes.requirementAt B.card_le hI hD code := by
  cases h
  exact mapRequirement_id _

end Erdos597Object.AlgebraTransport
