import Erdos597Object.BooleanHistoryMixtures

set_option backward.isDefEq.respectTransparency false

/-! Mix entire row families over a disjoint refinement of their Boolean supports. -/

namespace Erdos597Object.BooleanFamilyMixing

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet

variable {B I J : Type} [CompleteBooleanAlgebra B]

theorem disjoint_cover (weight : I → B) :
    ∃ piece : I → B, (∀ i, piece i ≤ weight i) ∧
      (∀ i j, i ≠ j → piece i ⊓ piece j = ⊥) ∧
      (⨆ i, weight i) ≤ ⨆ i, piece i := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : I → I → Prop, IsWellOrder I r := by
    obtain ⟨horder⟩ := exists_wellFoundedLT I
    exact ⟨(· < ·), inferInstance⟩
  let : IsWellOrder I r := hr
  let earlier := fun i => ⨆ j : {j // r j i}, weight j.val
  let piece := fun i => weight i ⊓ (earlier i)ᶜ
  have hzero (i j : I) (hij : r i j) : piece i ⊓ piece j = ⊥ := by
    apply bot_unique
    have hprior : weight i ≤ earlier j := le_iSup_of_le ⟨i, hij⟩ le_rfl
    have hboth : piece i ⊓ piece j ≤ weight i ⊓ (weight i)ᶜ :=
      le_inf (inf_le_left.trans inf_le_left)
        ((inf_le_right.trans inf_le_right).trans (compl_le_compl hprior))
    exact hboth.trans_eq inf_compl_eq_bot
  have hcover (i : I) : weight i ≤ ⨆ j, piece j := by
    induction i using hr.wf.induction with
    | h i ih =>
      have hearlier : earlier i ≤ ⨆ j, piece j :=
        iSup_le fun j => ih j.val j.property
      calc
        weight i = piece i ⊔ (weight i ⊓ earlier i) := by
          dsimp only [piece]
          rw [← inf_sup_left, compl_sup_eq_top, inf_top_eq]
        _ ≤ ⨆ j, piece j := sup_le (le_iSup piece i) (inf_le_right.trans hearlier)
  refine ⟨piece, fun _ => inf_le_left, ?_, iSup_le hcover⟩
  intro i j hij
  rcases trichotomous (r := r) i j with hij' | heq | hji
  · exact hzero i j hij'
  · exact False.elim (hij heq)
  · rw [inf_comm]
    exact hzero j i hji

theorem family_fullness (property : (J → bSet B) → B)
    (hcongr : ∀ context left right,
      (∀ j, context ≤ left j =ᴮ right j) →
      context ≤ property left → context ≤ property right)
    (context : B) (hcover : context ≤ ⨆ family, property family) :
    ∃ family : J → bSet B, context ≤ property family := by
  classical
  let Index := Set.range property
  let family : Index → J → bSet B := fun i => Classical.choose i.property
  have hproperty (i : Index) : property (family i) = i.val :=
    Classical.choose_spec i.property
  obtain ⟨piece, hpiece, hdisjoint, hpiecesCover⟩ :=
    disjoint_cover (fun i : Index => i.val)
  let mixed : J → bSet B := fun j => bSet.mixture piece (fun i => family i j)
  have hequal (i : Index) (j : J) : piece i ≤ mixed j =ᴮ family i j := by
    apply bSet.mixing_lemma'
    intro left right
    by_cases h : left = right
    · subst right
      exact bSet.bv_refl
    · rw [hdisjoint left right h]
      exact bot_le
  have hresult (i : Index) : piece i ≤ property mixed :=
    hcongr (piece i) (family i) mixed (fun j => bSet.bv_symm (hequal i j))
      ((hpiece i).trans_eq (hproperty i).symm)
  have hsmall : (⨆ f, property f) ≤ ⨆ i : Index, i.val := by
    apply iSup_le
    intro f
    exact le_iSup_of_le ⟨property f, Set.mem_range_self f⟩ le_rfl
  exact ⟨mixed, ((hcover.trans hsmall).trans hpiecesCover).trans (iSup_le hresult)⟩

end Erdos597Object.BooleanFamilyMixing
