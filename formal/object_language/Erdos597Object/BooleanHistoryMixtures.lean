import Erdos597Object.BooleanHistoryBlocks
import Erdos597Object.BooleanHistoryPoints

set_option backward.isDefEq.respectTransparency false

/-! Set names selected coherently by finite blocks of filter histories. -/

namespace Erdos597Object.BooleanHistoryMixtures

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanInfiniteSets BooleanRamseyTree BooleanRamseyForcing
open BooleanRamseySelection BooleanRamseyCoherence BooleanHistoryBlocks
open BooleanHistoryPoints BooleanPosetCoding

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def historyWeight (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B) (bound : ℕ) (history : List Choice) : B :=
  if bound ≤ history.length then
    context ⊓ FilterCoefficients.values (forcing arity color initial) filter history else ⊥

theorem historyWeight_le_context (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B) (bound : ℕ) (history : List Choice) :
    historyWeight context arity color initial filter bound history ≤ context := by
  unfold historyWeight
  split_ifs <;> simp only [inf_le_left, bot_le]

theorem historyWeight_le_value (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B) (bound : ℕ) (history : List Choice) :
    historyWeight context arity color initial filter bound history ≤
      FilterCoefficients.values (forcing arity color initial) filter history := by
  unfold historyWeight
  split_ifs <;> simp only [inf_le_right, bot_le]

theorem historyWeight_long (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B) (bound : ℕ) (history : List Choice)
    (hne : historyWeight context arity color initial filter bound history ≠ ⊥) :
    bound ≤ history.length := by
  by_contra h
  exact hne (by simp only [historyWeight, ite_eq_right h])

theorem historyWeight_mono (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B) (small large : ℕ) (hle : small ≤ large)
    (history : List Choice) :
    historyWeight context arity color initial filter large history ≤
      historyWeight context arity color initial filter small history := by
  by_cases hlarge : large ≤ history.length
  · simp only [historyWeight, ite_eq_left hlarge, ite_eq_left (hle.trans hlarge), le_refl]
  · simp only [historyWeight, ite_eq_right hlarge, bot_le]

theorem historyWeight_cover (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (hinfinite : context ≤ infiniteValue (selectedWeight arity color initial filter))
    (bound : ℕ) : context ≤ ⨆ history : List Choice,
      historyWeight context arity color initial filter bound history := by
  apply (le_inf le_rfl (long_cover context arity color initial filter hfilter hinfinite bound)).trans
  rw [longValue, inf_iSup_eq]
  apply iSup_le
  intro history
  apply le_iSup_of_le history
  by_cases hlong : bound ≤ history.length
  · simp only [historyWeight, ite_eq_left hlong, le_refl]
  · simp only [historyWeight, ite_eq_right hlong, inf_bot_eq, le_refl]

noncomputable def blockMixture (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B) (k index : ℕ)
    (names : (Fin k → ℕ) → bSet B) : bSet B :=
  bSet.mixture (historyWeight context arity color initial filter ((index + 1) * k))
    (fun history => names (historyBlock history k index))

theorem blockMixture_eq (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (k index : ℕ) (names : (Fin k → ℕ) → bSet B) (history : List Choice) :
    historyWeight context arity color initial filter ((index + 1) * k) history ≤
      blockMixture context arity color initial filter k index names =ᴮ
        names (historyBlock history k index) := by
  apply bSet.mixing_lemma'
  intro left right
  let part := historyWeight context arity color initial filter ((index + 1) * k) left ⊓
    historyWeight context arity color initial filter ((index + 1) * k) right
  by_cases hzero : part = ⊥
  · change part ≤ _
    rw [hzero]
    exact bot_le
  · have hleft : historyWeight context arity color initial filter ((index + 1) * k) left ≠ ⊥ := by
      intro hz
      exact hzero (bot_unique (inf_le_left.trans_eq hz))
    have hright : historyWeight context arity color initial filter ((index + 1) * k) right ≠ ⊥ := by
      intro hz
      exact hzero (bot_unique (inf_le_right.trans_eq hz))
    have hleftLength := historyWeight_long context arity color initial filter _ left hleft
    have hrightLength := historyWeight_long context arity color initial filter _ right hright
    have hpart : part ≤ context ⊓
        (FilterCoefficients.values (forcing arity color initial) filter left ⊓
          FilterCoefficients.values (forcing arity color initial) filter right) := by
      exact le_inf (inf_le_left.trans (historyWeight_le_context context arity color initial filter _ left))
        (le_inf (inf_le_left.trans (historyWeight_le_value context arity color initial filter _ left))
          (inf_le_right.trans (historyWeight_le_value context arity color initial filter _ right)))
    have hnonzero : context ⊓
        (FilterCoefficients.values (forcing arity color initial) filter left ⊓
          FilterCoefficients.values (forcing arity color initial) filter right) ≠ ⊥ := by
      intro hz
      exact hzero (bot_unique (hpart.trans_eq hz))
    have hblocks : historyBlock left k index = historyBlock right k index := by
      rcases comparable_of_nonzero context arity color initial filter hfilter left right hnonzero with h | h
      · exact historyBlock_prefix left right h k index hleftLength
      · exact (historyBlock_prefix right left h k index hrightLength).symm
    simp only [hblocks, bSet.bv_eq_refl, le_top]

theorem blockMixture_property (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (hinfinite : context ≤ infiniteValue (selectedWeight arity color initial filter))
    (k index : ℕ) (names : (Fin k → ℕ) → bSet B)
    (property : bSet B → B) (hext : bSet.B_ext property)
    (hproperty : ∀ history : List Choice,
      historyWeight context arity color initial filter ((index + 1) * k) history ≤
        property (names (historyBlock history k index))) :
    context ≤ property (blockMixture context arity color initial filter k index names) := by
  apply (historyWeight_cover context arity color initial filter hfilter hinfinite ((index + 1) * k)).trans
  apply iSup_le
  intro history
  have heq := blockMixture_eq context arity color initial filter hfilter k index names history
  exact (le_inf (bSet.bv_symm heq) (hproperty history)).trans (hext _ _)

theorem blockMixture_binary_property (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (hinfinite : context ≤ infiniteValue (selectedWeight arity color initial filter))
    (k i j bound : ℕ) (hi : (i + 1) * k ≤ bound) (hj : (j + 1) * k ≤ bound)
    (leftNames rightNames : (Fin k → ℕ) → bSet B)
    (property : bSet B → bSet B → B)
    (hleft : ∀ right, bSet.B_ext (fun left => property left right))
    (hright : ∀ left, bSet.B_ext (fun right => property left right))
    (hproperty : ∀ history : List Choice,
      historyWeight context arity color initial filter bound history ≤
        property (leftNames (historyBlock history k i)) (rightNames (historyBlock history k j))) :
    context ≤ property (blockMixture context arity color initial filter k i leftNames)
      (blockMixture context arity color initial filter k j rightNames) := by
  apply (historyWeight_cover context arity color initial filter hfilter hinfinite bound).trans
  apply iSup_le
  intro history
  have heqLeft := (historyWeight_mono context arity color initial filter _ bound hi history).trans
    (blockMixture_eq context arity color initial filter hfilter k i leftNames history)
  have heqRight := (historyWeight_mono context arity color initial filter _ bound hj history).trans
    (blockMixture_eq context arity color initial filter hfilter k j rightNames history)
  have hleftProperty := (le_inf (bSet.bv_symm heqLeft) (hproperty history)).trans (hleft _ _ _)
  exact (le_inf (bSet.bv_symm heqRight) hleftProperty).trans (hright _ _ _)

end Erdos597Object.BooleanHistoryMixtures
