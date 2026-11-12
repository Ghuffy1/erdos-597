import Erdos597Object.BooleanGoodSupport

set_option backward.isDefEq.respectTransparency false

/-! Long compatible histories supply the row-block mixtures. -/

namespace Erdos597Object.BooleanHistoryBlocks

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanInfiniteSets BooleanFiniteSelections BooleanRamseyTree
open BooleanRamseyForcing BooleanRamseySelection BooleanRamseyHistories
open BooleanRamseyFiniteCover BooleanPosetCoding

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def longValue (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B) (bound : ℕ) : B :=
  ⨆ history : List Choice, if bound ≤ history.length then
    FilterCoefficients.values (forcing arity color initial) filter history else ⊥

theorem cover_le_long (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B) (bound : ℕ)
    (subset : Finset ℕ) (hsize : bound ≤ subset.card) :
    coverValue arity color initial filter subset ≤ longValue arity color initial filter bound := by
  classical
  apply iSup_le
  intro history
  by_cases hsub : subset ⊆ points history
  · have hlength : bound ≤ history.length := by
      apply (hsize.trans (Finset.card_le_card hsub)).trans
      simpa only [points, List.length_map] using (history.map Prod.fst).toFinset_card_le
    apply le_iSup_of_le history
    simp only [ite_eq_left hsub, ite_eq_left hlength, le_refl]
  · simp only [ite_eq_right hsub, bot_le]

theorem long_cover (context : B) (arity : ℕ) (color : Finset ℕ → B)
    (initial : ℕ → B) (filter : bSet B)
    (hfilter : context ≤ orderFilterValue (V B)
      (domainName (forcing arity color initial) checkLabel)
      (orderName (forcing arity color initial) checkLabel) filter)
    (hinfinite : context ≤ infiniteValue (selectedWeight arity color initial filter))
    (bound : ℕ) : context ≤ longValue arity color initial filter bound := by
  classical
  have hcover := hinfinite.trans
    (increasing_tuples_cover (selectedWeight arity color initial filter) bound)
  apply (le_inf le_rfl hcover).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro tuple
  by_cases htuple : StrictMono tuple
  · rw [ite_eq_left htuple]
    have hcard : (Finset.univ.image tuple).card = bound := by
      rw [Finset.card_image_of_injective _ htuple.injective, Finset.card_univ, Fintype.card_fin]
    have hfinite := finite_selected_cover context arity color initial filter hfilter
      (Finset.univ.image tuple)
    rw [tupleWeight_image] at hfinite
    exact hfinite.trans (cover_le_long arity color initial filter bound _ hcard.ge)
  · simp only [ite_eq_right htuple, inf_bot_eq, bot_le]

end Erdos597Object.BooleanHistoryBlocks
