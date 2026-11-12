import Erdos597Object.GenericFilterValues
import Erdos597Object.WeightedFilterModel
import Erdos597Object.IterationNameTransport

set_option backward.isDefEq.respectTransparency false

/-! The generic filter satisfies the literal set-model formulas for a two-step forcing. -/

namespace Erdos597Object.GenericFilterModel

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanIteration BooleanSets BooleanPosetCoding CompletionEmbedding PosetCompletion
open GenericFilterValues IterationNameTransport

variable {B I : Type} [CompleteBooleanAlgebra B]

noncomputable def filterName (P : BooleanPoset B I) : bSet (Completion (Condition P)) :=
  weightedSet checkLabel (labelValue P)

noncomputable def denseName (P : BooleanPoset B I) (dense : I → B) :
    bSet (Completion (Condition P)) :=
  weightedSet checkLabel (fun i => baseMap P (dense i))

noncomputable def familyName {D : Type} (P : BooleanPoset B I) (dense : D → I → B) :
    bSet (Completion (Condition P)) :=
  weightedSet (fun d => denseName P (dense d)) (fun _ => ⊤)

theorem generic_is_filter (P : BooleanPoset B I) :
    ⊤ ≤ orderFilterValue (V (Completion (Condition P)))
      (domainName (mapPoset (baseHom P) P) checkLabel)
      (orderName (mapPoset (baseHom P) P) checkLabel) (filterName P) := by
  apply WeightedFilterModel.orderFilterValue_of_weights (mapPoset (baseHom P) P) (labelValue P)
  · exact labelValue_le_member P
  · exact labelValue_cover P
  · exact labelValue_upward P
  · intro i j
    simpa only [mapPoset, baseHom, ← inf_assoc] using! labelValue_directed P i j

theorem generic_meets_family {D : Type} (P : BooleanPoset B I) (dense : D → I → B)
    (hdense : ∀ d, ⊤ ≤ denseValue (V B) (domainName P checkLabel) (orderName P checkLabel)
      (weightedSet checkLabel (dense d))) :
    ⊤ ≤ meetsFamilyValue (V (Completion (Condition P))) (filterName P) (familyName P dense) := by
  apply WeightedFilterModel.meetsFamilyValue_of_weights (labelValue P)
    (fun d i => baseMap P (dense d i))
  intro d
  exact labelValue_meets_dense P (dense d) (WeightedFilterModel.dense_coefficients P (dense d) (hdense d))

theorem generic_filter_meets_family {D : Type} (P : BooleanPoset B I) (dense : D → I → B)
    (hdense : ∀ d, ⊤ ≤ denseValue (V B) (domainName P checkLabel) (orderName P checkLabel)
      (weightedSet checkLabel (dense d))) :
    ⊤ ≤ orderFilterValue (V (Completion (Condition P)))
      (domainName (mapPoset (baseHom P) P) checkLabel)
      (orderName (mapPoset (baseHom P) P) checkLabel) (filterName P) ⊓
        meetsFamilyValue (V (Completion (Condition P))) (filterName P) (familyName P dense) :=
  le_inf (generic_is_filter P) (generic_meets_family P dense hdense)

theorem generic_filter_exists {D : Type} (P : BooleanPoset B I) (dense : D → I → B)
    (hdense : ∀ d, ⊤ ≤ denseValue (V B) (domainName P checkLabel) (orderName P checkLabel)
      (weightedSet checkLabel (dense d))) :
    ⊤ ≤ ⨆ filter : bSet (Completion (Condition P)),
      orderFilterValue (V (Completion (Condition P)))
        (domainName (mapPoset (baseHom P) P) checkLabel)
        (orderName (mapPoset (baseHom P) P) checkLabel) filter ⊓
          meetsFamilyValue (V (Completion (Condition P))) filter (familyName P dense) :=
  le_iSup_of_le (filterName P) (generic_filter_meets_family P dense hdense)

end Erdos597Object.GenericFilterModel
