import Erdos597Object.BooleanSets

set_option backward.isDefEq.respectTransparency false

/-! Infinitude and finite decisions for Boolean-valued subsets of omega. -/

namespace Erdos597Object.BooleanInfiniteSets

variable {B I : Type} [CompleteBooleanAlgebra B]

noncomputable def tailValue (weight : ℕ → B) (bound : ℕ) : B :=
  ⨆ n : ℕ, ⨆ (_ : bound ≤ n), weight n

noncomputable def infiniteValue (weight : ℕ → B) : B :=
  ⨅ bound : ℕ, tailValue weight bound

theorem tail_antitone (weight : ℕ → B) {left right : ℕ} (h : left ≤ right) :
    tailValue weight right ≤ tailValue weight left := by
  apply iSup_le
  intro n
  apply iSup_le
  intro hn
  exact le_iSup_of_le n (le_iSup_of_le (h.trans hn) le_rfl)

theorem tail_mono {left right : ℕ → B} (h : ∀ n, left n ≤ right n) (bound : ℕ) :
    tailValue left bound ≤ tailValue right bound :=
  iSup_mono fun n => iSup_mono fun _ => h n

theorem infinite_mono {left right : ℕ → B} (h : ∀ n, left n ≤ right n) :
    infiniteValue left ≤ infiniteValue right :=
  iInf_mono (tail_mono h)

theorem infinite_le_tail (weight : ℕ → B) (bound : ℕ) :
    infiniteValue weight ≤ tailValue weight bound := iInf_le _ bound

theorem infinite_le_total (weight : ℕ → B) : infiniteValue weight ≤ ⨆ n, weight n := by
  apply (infinite_le_tail weight 0).trans
  exact iSup_le fun n => iSup_le fun _ => le_iSup weight n

theorem tail_sup (left right : ℕ → B) (bound : ℕ) :
    tailValue (fun n => left n ⊔ right n) bound = tailValue left bound ⊔ tailValue right bound := by
  simp only [tailValue, iSup_sup_eq]

theorem infinite_sup (left right : ℕ → B) :
    infiniteValue (fun n => left n ⊔ right n) = infiniteValue left ⊔ infiniteValue right := by
  apply le_antisymm
  · unfold infiniteValue
    rw [sup_iInf_eq]
    apply le_iInf
    intro rightBound
    rw [iInf_sup_eq]
    apply le_iInf
    intro leftBound
    apply (iInf_le _ (max leftBound rightBound)).trans
    rw [tail_sup]
    exact sup_le_sup (tail_antitone left (le_max_left _ _))
      (tail_antitone right (le_max_right _ _))
  · exact sup_le (infinite_mono fun _ => le_sup_left) (infinite_mono fun _ => le_sup_right)

theorem infinite_bot : infiniteValue (fun _ : ℕ => (⊥ : B)) = ⊥ := by
  simp [infiniteValue, tailValue]

noncomputable def fromWeight (weight : ℕ → B) (cutoff n : ℕ) : B :=
  if cutoff ≤ n then weight n else ⊥

theorem infinite_from (weight : ℕ → B) (cutoff : ℕ) :
    infiniteValue (fromWeight weight cutoff) = infiniteValue weight := by
  apply le_antisymm
  · apply infinite_mono
    intro n
    unfold fromWeight
    split_ifs <;> simp only [le_refl, bot_le]
  · apply le_iInf
    intro bound
    apply (infinite_le_tail weight (max cutoff bound)).trans
    apply iSup_le
    intro n
    apply iSup_le
    intro hn
    have hcutoff : cutoff ≤ n := (le_max_left _ _).trans hn
    have hbound : bound ≤ n := (le_max_right _ _).trans hn
    apply le_iSup_of_le n
    apply le_iSup_of_le hbound
    simp only [fromWeight, hcutoff, ↓reduceIte, le_refl]

theorem infinite_split (weight color : ℕ → B) :
    infiniteValue weight = infiniteValue (fun n => weight n ⊓ color n) ⊔
      infiniteValue (fun n => weight n ⊓ (color n)ᶜ) := by
  rw [← infinite_sup]
  congr 1
  funext n
  exact (sup_inf_inf_compl (x := weight n) (y := color n)).symm

theorem infinite_finset_sup (weight : I → ℕ → B) (indices : Finset I) :
    infiniteValue (fun n => indices.sup (fun i => weight i n)) =
      indices.sup (fun i => infiniteValue (weight i)) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp only [Finset.sup_empty, infinite_bot]
  | insert i indices hi ih =>
    simp only [Finset.sup_insert, infinite_sup, ih]

noncomputable def restrictedWeight (weight : ℕ → B) (color : I → ℕ → B)
    (indices : Finset I) (choice : I → Bool) (n : ℕ) : B :=
  weight n ⊓ ⨅ i ∈ indices, if choice i then color i n else (color i n)ᶜ

theorem finite_decisions (weight : ℕ → B) (color : I → ℕ → B) (indices : Finset I) :
    infiniteValue weight ≤ ⨆ choice : I → Bool, infiniteValue (restrictedWeight weight color indices choice) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    apply le_iSup_of_le (fun _ => false)
    have hempty : restrictedWeight weight color ∅ (fun _ => false) = weight := by
      funext n
      simp [restrictedWeight]
    rw [hempty]
  | @insert a indices ha ih =>
    apply ih.trans
    apply iSup_le
    intro choice
    let current : ℕ → B := restrictedWeight weight color indices choice
    have hcase (b : Bool) : infiniteValue (fun n => current n ⊓
        (if b then color a n else (color a n)ᶜ)) ≤
        ⨆ next : I → Bool, infiniteValue (restrictedWeight weight color (insert a indices) next) := by
      apply le_iSup_of_le (Function.update choice a b)
      apply infinite_mono
      intro n
      apply le_inf (inf_le_left.trans inf_le_left)
      apply le_iInf
      intro i
      apply le_iInf
      intro hi
      rcases Finset.mem_insert.mp hi with hia | hi
      · subst i
        simpa only [Function.update_self] using!
          (inf_le_right : current n ⊓ (if b then color a n else (color a n)ᶜ) ≤ _)
      · have hia : i ≠ a := fun h => ha (h ▸ hi)
        rw [Function.update_of_ne hia]
        exact (inf_le_left.trans inf_le_right).trans ((iInf_le _ i).trans (iInf_le _ hi))
    change infiniteValue current ≤ _
    rw [infinite_split current (color a)]
    exact sup_le (by simpa using hcase true) (by simpa using hcase false)

end Erdos597Object.BooleanInfiniteSets
