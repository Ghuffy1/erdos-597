import Erdos597Object.FullMartinModel
import Erdos597Object.BooleanCountableNames
import Erdos597Object.BooleanFilterSemantics

set_option backward.isDefEq.respectTransparency false

/-! Filters meeting countable dense families in the constructed Martin-axiom model. -/

namespace Erdos597Object.BooleanCountableForcing

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanCountableNames BooleanFilterSemantics ScheduledIteration

variable {B : Type} [CompleteBooleanAlgebra B]

theorem ccc_of_countable (context : B) (domain relation : bSet B)
    (hcountable : context ≤ injectsIntoValue (V B) domain bSet.omega) :
    context ≤ countableChainConditionValue (V B) domain relation := by
  apply le_iInf
  intro family
  apply lattice.bv_imp_intro
  apply subset_countable family domain
  · have h : context ⊓ antichainValue (V B) domain relation family ≤
        subsetValue (V B) family domain := inf_le_right.trans inf_le_left
    rwa [subsetValue_bSet] at h
  · exact inf_le_left.trans hcountable

theorem countable_family_filter_exists (context : ScheduledIteration.finalAlgebra)
    (domain relation : bSet ScheduledIteration.finalAlgebra)
    (dense : ℕ → bSet ScheduledIteration.finalAlgebra)
    (hnonempty : context ≤ nonemptyValue (V ScheduledIteration.finalAlgebra) domain)
    (horder : context ≤ partialOrderValue (V ScheduledIteration.finalAlgebra) domain relation)
    (hcountable : context ≤ injectsIntoValue (V ScheduledIteration.finalAlgebra) domain bSet.omega)
    (hdense : ∀ n, context ≤ denseValue (V ScheduledIteration.finalAlgebra) domain relation (dense n)) :
    ∃ filter : bSet ScheduledIteration.finalAlgebra,
      context ≤ orderFilterValue (V ScheduledIteration.finalAlgebra) domain relation filter ∧
        ∀ n, context ≤ ⨆ x : bSet ScheduledIteration.finalAlgebra,
          (x ∈ᴮ filter) ⊓ (x ∈ᴮ dense n) := by
  classical
  have : Infinite Labels := Cardinal.infinite_iff.mpr (by
    rw [labels_card]
    exact Cardinal.aleph0_le_aleph 1)
  let embed : ℕ ↪ Labels := Infinite.natEmbedding Labels
  let decode : Labels → ℕ := Function.invFun embed
  have hdecode (n : ℕ) : decode (embed n) = n := Function.leftInverse_invFun embed.injective n
  let family := weightedSet dense (fun _ => context)
  let labelledDense : Labels → bSet ScheduledIteration.finalAlgebra := fun i => dense (decode i)
  have hfamily : context ≤ family =ᴮ weightedSet labelledDense (fun _ => context) := by
    apply bSet.subset_ext
    · apply bSet.subset_intro
      intro n
      apply le_iSup_of_le (embed n)
      change context ⊓ context ≤ context ⊓ (dense n =ᴮ dense (decode (embed n)))
      rw [hdecode]
      exact le_inf inf_le_left bSet.bv_refl
    · apply bSet.subset_intro
      intro i
      exact le_iSup_of_le (decode i) (le_inf inf_le_left bSet.bv_refl)
  have hex := FullMartinModel.family_filter_exists context domain relation family labelledDense
    (fun _ => context) hnonempty horder (ccc_of_countable context domain relation hcountable)
    hfamily (fun _ => le_rfl) (fun i => hdense (decode i))
  obtain ⟨filter, hfilter⟩ := bSet.exists_convert hex
    (bSet.B_ext_inf (orderFilter_ext domain relation) (meetsFamily_ext family))
  refine ⟨filter, hfilter.trans inf_le_left, ?_⟩
  intro n
  have hmeets := (hfilter.trans inf_le_right).trans (iInf_le _ (dense n))
  exact lattice.bv_context_apply hmeets (weight_le_member dense (fun _ => context) n)

end Erdos597Object.BooleanCountableForcing
