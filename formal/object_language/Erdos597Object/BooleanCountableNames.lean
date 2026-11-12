import Erdos597Object.BooleanNameSupports
import Erdos597Object.BooleanFunctionBridge

set_option backward.isDefEq.respectTransparency false

/-! Countable labelled names and bounded subsets of the first uncountable ordinal. -/

namespace Erdos597Object.BooleanCountableNames

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanNameSupports

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem weighted_countable [Countable I] (label : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥) (weight : I → B) :
    ⊤ ≤ injectsIntoValue (V B) (weightedSet label weight) bSet.omega := by
  classical
  let encode : I → ℕ := Classical.choose (Countable.exists_injective_nat I)
  have hinjective : Function.Injective encode :=
    Classical.choose_spec (Countable.exists_injective_nat I)
  let index : (weightedSet label weight).type → (bSet.omega : bSet B).type :=
    fun i => ULift.up (encode i)
  have hext : ∀ i j {part : B}, part ≤ label i =ᴮ label j →
      part ≤ bSet.ofNat (encode i) =ᴮ bSet.ofNat (encode j) := by
    intro i j part heq
    by_cases hij : i = j
    · subst j
      exact bSet.bv_refl
    · exact (heq.trans_eq (hdiscrete i j hij)).trans bot_le
  have hinj : ∀ i j {part : B}, part ≤ bSet.ofNat (encode i) =ᴮ bSet.ofNat (encode j) →
      part ≤ label i =ᴮ label j := by
    intro i j part heq
    by_cases hij : i = j
    · subst j
      exact bSet.bv_refl
    · have hcode : encode i ≠ encode j := fun h => hij (hinjective h)
      exact (heq.trans_eq (bSet.ofNat_inj hcode)).trans bot_le
  rw [BooleanFunctionBridge.injectsInto_eq_injects_into]
  apply bSet.injects_into_of_injection_into
  apply le_iSup_of_le (bSet.function.mk' index (fun _ => ⊤))
  exact le_inf
    (bSet.function.mk'_is_function index (fun _ => ⊤) hext (fun _ _ _ => ⟨le_top, le_top⟩))
    (bSet.function.mk'_is_inj index (fun _ => ⊤) hinj)

theorem subset_countable {context : B} (domain small : bSet B)
    (hsubset : context ≤ domain ⊆ᴮ small)
    (hsmall : context ≤ injectsIntoValue (V B) small bSet.omega) :
    context ≤ injectsIntoValue (V B) domain bSet.omega := by
  rw [BooleanFunctionBridge.injectsInto_eq_injects_into] at hsmall ⊢
  exact bSet.injects_into_trans (bSet.injects_into_of_subset hsubset) hsmall

theorem below_countable (bound : Erdos597.One) : Countable (Set.Iio bound) := by
  have hsubset : Set.Iio bound ⊆ Set.Iic bound := by
    intro i hi
    change i ≤ bound
    exact _root_.le_of_lt (show i < bound from hi)
  exact (Set.Countable.mono hsubset (Erdos597.countable_initial_segment bound)).to_subtype

theorem bounded_countable (label : Erdos597.One → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥) (bound : Erdos597.One) :
    ⊤ ≤ injectsIntoValue (V B) (boundedName label bound) bSet.omega := by
  classical
  let small : bSet B := weightedSet (fun i : Set.Iio bound => label i.val) (fun _ => ⊤)
  have : Countable (Set.Iio bound) := below_countable bound
  apply subset_countable (boundedName label bound) small
  · apply bSet.subset_intro
    intro i
    change Erdos597.One at i
    change ⊤ ⊓ (if i < bound then ⊤ else ⊥) ≤ label i ∈ᴮ small
    by_cases hi : i < bound
    · simpa only [hi, ↓reduceIte, inf_top_eq] using
        weight_le_member (fun i : Set.Iio bound => label i.val) (fun _ => (⊤ : B)) ⟨i, hi⟩
    · simp only [hi, ↓reduceIte, inf_bot_eq, bot_le]
  · exact weighted_countable _ (fun i j hij => hdiscrete i.val j.val (fun h => hij (Subtype.ext h))) _

theorem uncountable_member_outside_countable (context : B) (domain small : bSet B)
    (hlarge : context ≤ (injectsIntoValue (V B) domain bSet.omega)ᶜ)
    (hsmall : context ≤ injectsIntoValue (V B) small bSet.omega) :
    ∃ name : bSet B, context ≤ (name ∈ᴮ domain) ⊓ (name ∈ᴮ small)ᶜ := by
  let outside : B := ⨆ name : bSet B, (name ∈ᴮ domain) ⊓ (name ∈ᴮ small)ᶜ
  have hsubset : outsideᶜ ≤ domain ⊆ᴮ small := by
    apply bSet.subset_unfold'.mpr
    simpa only [outside, compl_iSup, compl_inf, compl_compl, lattice.imp] using
      (le_rfl : outsideᶜ ≤ outsideᶜ)
  have hbot : context ⊓ outsideᶜ ≤ ⊥ := by
    have hinjects := subset_countable domain small (inf_le_right.trans hsubset)
      (inf_le_left.trans hsmall)
    exact (le_inf hinjects (inf_le_left.trans hlarge)).trans_eq inf_compl_eq_bot
  have houtside : context ≤ outside := by
    have h : context ≤ outsideᶜᶜ :=
      le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr (le_antisymm hbot bot_le))
    simpa only [compl_compl] using h
  exact bSet.exists_convert houtside
    (bSet.B_ext_inf (bSet.B_ext_mem_left domain) (bSet.B_ext_compl (bSet.B_ext_mem_left small)))

end Erdos597Object.BooleanCountableNames
