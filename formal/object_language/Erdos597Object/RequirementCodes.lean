import Erdos597Object.BookkeepingSchedule

set_option backward.isDefEq.respectTransparency false

/-! Enumerating the small poset and dense-family coefficients available at a stage. -/

namespace Erdos597Object.RequirementCodes

open Cardinal CanonicalIteration IterationCardinals
open scoped Cardinal

variable {B I D : Type} [CompleteBooleanAlgebra B]

abbrev RawRequirement (B I D : Type) :=
  (I → B) × ((I → I → B) × (D → I → B))

theorem raw_card_le (hB : #B ≤ iterationSize) (hI : #I ≤ ℵ₁) (hD : #D ≤ ℵ₁) :
    #(RawRequirement B I D) ≤ iterationSize := by
  have hm : #(I → B) ≤ iterationSize := function_card_le hB hI
  have ho : #(I → I → B) ≤ iterationSize := function_card_le hm hI
  have hd : #(D → I → B) ≤ iterationSize := function_card_le hm hD
  calc
    #(RawRequirement B I D) = #(I → B) * (#(I → I → B) * #(D → I → B)) := by
      simp only [RawRequirement, Cardinal.mk_prod, Cardinal.lift_id]
    _ ≤ iterationSize * (iterationSize * iterationSize) := mul_le_mul' hm (mul_le_mul' ho hd)
    _ = iterationSize := by
      rw [Cardinal.mul_eq_self iterationSize_infinite, Cardinal.mul_eq_self iterationSize_infinite]

def encode (P : BooleanIteration.BooleanPoset B I) (dense : D → I → B) :
    RawRequirement B I D := (P.member, P.leValue, dense)

noncomputable def interpret (raw : RawRequirement B I D) :
    Option (BooleanIteration.BooleanPoset B I × (D → I → B)) := by
  classical
  exact if h : ∃ P : BooleanIteration.BooleanPoset B I,
      P.member = raw.1 ∧ P.leValue = raw.2.1 then
    some (Classical.choose h, raw.2.2)
  else none

theorem interpret_encode (P : BooleanIteration.BooleanPoset B I) (dense : D → I → B) :
    interpret (encode P dense) = some (P, dense) := by
  classical
  have h : ∃ Q : BooleanIteration.BooleanPoset B I,
      Q.member = (encode P dense).1 ∧ Q.leValue = (encode P dense).2.1 :=
    ⟨P, rfl, rfl⟩
  rw [interpret, dif_pos h]
  have hP : Classical.choose h = P :=
    PosetStageCapture.booleanPoset_ext (Classical.choose_spec h).1 (Classical.choose_spec h).2
  exact congrArg some (Prod.ext hP rfl)

noncomputable def encoding (hB : #B ≤ iterationSize) (hI : #I ≤ ℵ₁) (hD : #D ≤ ℵ₁) :
    RawRequirement B I D ↪ Index :=
  Classical.choice ((Cardinal.le_def _ _).mp ((raw_card_le hB hI hD).trans_eq index_card.symm))

noncomputable def rawAt (hB : #B ≤ iterationSize) (hI : #I ≤ ℵ₁) (hD : #D ≤ ℵ₁)
    (i : Index) : RawRequirement B I D := by
  classical
  exact if h : ∃ raw, encoding hB hI hD raw = i then Classical.choose h
    else (fun _ => ⊥, fun _ _ => ⊥, fun _ _ => ⊥)

theorem rawAt_encoding (hB : #B ≤ iterationSize) (hI : #I ≤ ℵ₁) (hD : #D ≤ ℵ₁)
    (raw : RawRequirement B I D) : rawAt hB hI hD (encoding hB hI hD raw) = raw := by
  classical
  have h : ∃ other, encoding hB hI hD other = encoding hB hI hD raw := ⟨raw, rfl⟩
  rw [rawAt, dif_pos h]
  exact (encoding hB hI hD).injective (Classical.choose_spec h)

noncomputable def requirementAt (hB : #B ≤ iterationSize) (hI : #I ≤ ℵ₁) (hD : #D ≤ ℵ₁)
    (i : Index) : Option (BooleanIteration.BooleanPoset B I × (D → I → B)) :=
  interpret (rawAt hB hI hD i)

theorem every_requirement_has_code (hB : #B ≤ iterationSize) (hI : #I ≤ ℵ₁) (hD : #D ≤ ℵ₁)
    (P : BooleanIteration.BooleanPoset B I) (dense : D → I → B) :
    ∃ i : Index, requirementAt hB hI hD i = some (P, dense) := by
  refine ⟨encoding hB hI hD (encode P dense), ?_⟩
  rw [requirementAt, rawAt_encoding, interpret_encode]

end Erdos597Object.RequirementCodes
