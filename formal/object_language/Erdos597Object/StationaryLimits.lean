import Erdos597Object.BooleanLimitCCC
import Erdos597Object.LimitReductions
import Mathlib.SetTheory.Cardinal.Cofinality.Club
import Mathlib.Order.SuccPred.CompleteLinearOrder

set_option backward.isDefEq.respectTransparency false

/-! The stationary-set argument for direct limits of cofinality aleph-one. -/

namespace Erdos597Object.StationaryLimits

open Set Cardinal Order
open scoped Cardinal
open BooleanDirectLimit LimitProjections LimitReductions MartinTransport

theorem ici_isClub {α : Type} [LinearOrder α] (a : α) : IsClub (Ici a) := by
  constructor
  · intro s hs hsne _ x hx
    obtain ⟨y, hy⟩ := hsne
    exact (hs hy).trans (hx.1 hy)
  · intro b
    exact ⟨max a b, le_max_left a b, le_max_right a b⟩

theorem stationary_isCofinal {α : Type} [LinearOrder α] {s : Set α}
    (hs : IsStationary s) : IsCofinal s := by
  intro a
  obtain ⟨b, hb, hab⟩ := hs (ici_isClub a)
  exact ⟨b, hb, hab⟩

theorem stationary_not_countable {α : Type} [LinearOrder α]
    (hα : ℵ₀ < Order.cof α) {s : Set α} (hs : IsStationary s) : ¬ s.Countable := by
  intro hcount
  exact hα.not_ge ((Order.cof_le (stationary_isCofinal hs)).trans hcount.le_aleph0)

theorem stationary_inter_club {α : Type} [LinearOrder α] [WellFoundedLT α]
    (hα : Order.cof α ≠ ℵ₀) {s c : Set α} (hs : IsStationary s) (hc : IsClub c) :
    IsStationary (s ∩ c) := by
  intro t ht
  obtain ⟨a, has, hac, hat⟩ := hs (hc.inter hα ht)
  exact ⟨a, ⟨has, hac⟩, hat⟩

theorem succLimits_isClub {α : Type} [LinearOrder α] [WellFoundedLT α]
    (hα : ℵ₀ < Order.cof α) : IsClub {a : α | IsSuccLimit a} := by
  classical
  have hcard : 0 < #α := (Cardinal.aleph0_pos.trans hα).trans_le (Order.cof_le_cardinalMk α)
  letI : Nonempty α := Cardinal.mk_ne_zero_iff.mp hcard.ne'
  letI : OrderBot α := WellFoundedLT.toOrderBot α
  letI : ConditionallyCompleteLinearOrderBot α := WellFoundedLT.conditionallyCompleteLinearOrderBot α
  constructor
  · intro s hs hsne _ x hx
    by_contra hnot
    exact hnot (hs (hx.mem_of_nonempty_of_not_isSuccLimit hsne hnot))
  · intro a
    letI : NoMaxOrder α := (noTopOrder_iff_noMaxOrder α).mp
      (Order.one_lt_cof_iff.mp (Cardinal.one_lt_aleph0.trans hα))
    let next : α → α := fun x => Classical.choose (exists_gt x)
    have hnext (x : α) : x < next x := Classical.choose_spec (exists_gt x)
    let g : ℕ → α := fun n => next^[n] a
    have hg : StrictMono g := by
      apply strictMono_of_lt_add_one
      intro n _
      change next^[n] a < next^[n + 1] a
      rw [Function.iterate_succ_apply']
      exact hnext _
    have hsmall : #(Set.range g) ≤ ℵ₀ := Cardinal.mk_range_le.trans_eq Cardinal.mk_nat
    have hbounded : BddAbove (Set.range g) := BddAbove.of_not_isCofinal
      (fun h => hα.not_ge ((Order.cof_le h).trans hsmall))
    let x := sSup (Set.range g)
    have hx : IsLUB (Set.range g) x := isLUB_csSup (Set.range_nonempty g) hbounded
    have hlimit : IsSuccLimit x := by
      by_contra hnot
      obtain ⟨n, hn⟩ := hx.exists_of_nonempty_of_not_isSuccLimit hnot
      have hlt := hg (Nat.lt_succ_self n)
      rw [hn] at hlt
      exact hlt.not_ge (hx.1 ⟨n + 1, rfl⟩)
    refine ⟨x, hlimit, ?_⟩
    simpa [g] using hx.1 ⟨0, rfl⟩

variable {α : Type} [LinearOrder α] [WellFoundedLT α] [IsRegularCardinalOrder α]
  {ι : Type} [Preorder ι] [IsDirectedOrder ι]
  {B : ι → Type} [∀ i, CompleteBooleanAlgebra (B i)]
  (e : ∀ i j, i ≤ j → CompleteLatticeHom (B i) (B j))
  [DirectedSystem B (e · · ·)]

def DenseAlong (stages : α → ι) (hmono : Monotone stages) (s : Set α) : Prop :=
  ∀ d ∈ s, ∀ c : B (stages d), c ≠ ⊥ →
    ∃ (a : α) (had : a < d) (b : B (stages a)),
      b ≠ ⊥ ∧ e (stages a) (stages d) (hmono had.le) b ≤ c

theorem ccc_of_stationary_density
    (hinj : ∀ i j h, Function.Injective (e i j h))
    (hB : ∀ i, Flypitch.BA_CCC (B i))
    (hα : Order.cof α = ℵ₁) (stages : α → ι) (hmono : Monotone stages)
    (hcofinal : ∀ i, ∃ a, i ≤ stages a) (s : Set α) (hs : IsStationary s)
    (hdense : DenseAlong e stages hmono s) : CountableChainCondition (Condition e) := by
  classical
  intro A hA
  by_contra huncountable
  have hcard : ℵ₁ ≤ #A := by
    apply Cardinal.aleph_one_le_iff.mpr
    apply lt_of_not_ge
    exact fun h => huncountable (Cardinal.le_aleph0_iff_set_countable.mp h)
  have hcardα : #α = ℵ₁ := (Order.cof_eq_cardinalMk (α := α)).symm.trans hα
  obtain ⟨embed⟩ : Nonempty (α ↪ A) :=
    (Cardinal.le_def _ _).mp (by simpa only [hcardα] using hcard)
  let p : α → Condition e := fun a => (embed a).val
  have hpinjective : Function.Injective p := by
    intro a b h
    exact embed.injective (Subtype.ext h)
  choose support hsupport using fun a => hcofinal (representative e (p a)).index
  have hαne : Order.cof α ≠ ℵ₀ := by
    rw [hα]
    exact Cardinal.aleph0_lt_aleph_one.ne'
  let c : Set α := {d | ∀ a < d, support a ≤ d}
  have hc : IsClub c := IsClub.diag hαne (fun a => ici_isClub (support a))
  let dset : Set α := s ∩ c
  have hdset : IsStationary dset := stationary_inter_club hαne hs hc
  have hex : ∀ d : dset, ∃ (a : α) (had : a < d.val) (b : B (stages a)),
      b ≠ ⊥ ∧ e (stages a) (stages d.val) (hmono had.le) b ≤
        stageProjection e hinj (stages d.val) (p d.val) := by
    intro d
    exact hdense d.val d.property.1 _ (stageProjection_nonzero e hinj _ _)
  choose lower hlower value hvalue hbound using hex
  let reg : α → α := fun d => if hd : d ∈ dset then lower ⟨d, hd⟩ else d
  have hreg : ∀ d ∈ dset, reg d < d := by
    intro d hd
    simpa only [reg, dif_pos hd] using hlower ⟨d, hd⟩
  obtain ⟨a, ha⟩ := exists_isStationary_preimage_singleton hαne hdset hreg
  let t : Set α := dset ∩ reg ⁻¹' {a}
  have ht : IsStationary t := ha
  let asDense (d : t) : dset := ⟨d.val, d.property.1⟩
  have hlower_eq (d : t) : lower (asDense d) = a := by
    have h : reg d.val = a := d.property.2
    simpa only [reg, dif_pos d.property.1, asDense] using h
  have had (d : t) : a < d.val := (hlower_eq d) ▸ hlower (asDense d)
  let b (d : t) : B (stages a) :=
    e (stages (lower (asDense d))) (stages a) (hmono (hlower_eq d).le) (value (asDense d))
  have hb (d : t) : b d ≠ ⊥ :=
    mapped_nonzero e hinj (hmono (hlower_eq d).le) (hvalue (asDense d))
  have hb_bound (d : t) : e (stages a) (stages d.val) (hmono (had d).le) (b d) ≤
      stageProjection e hinj (stages d.val) (p d.val) := by
    dsimp only [b]
    simpa only [DirectedSystem.map_map' e] using hbound (asDense d)
  have hb_small (d : t) : b d ≤ stageProjection e hinj (stages a) (p d.val) :=
    pullback_bound e hinj (hmono (had d).le) (p d.val) (b d) (hb_bound d)
  have hordered (d z : t) (hdz : d.val < z.val) : b d ⊓ b z = ⊥ := by
    by_contra hnonzero
    let raw := representative e (p d.val)
    have hindex : raw.index ≤ stages z.val :=
      (hsupport d.val).trans (hmono (z.property.1.2 d.val hdz))
    have hp : ∃ (q : B (stages z.val)) (hq : q ≠ ⊥),
        ofStage e (stages z.val) q hq = p d.val := by
      refine ⟨e raw.index (stages z.val) hindex raw.value,
        mapped_nonzero e hinj hindex raw.nonzero, ?_⟩
      exact (ofStage_map e hinj hindex raw.value raw.nonzero).symm.trans
        (ofRaw_representative e (p d.val))
    have hcommon := compatible_of_reductions e hinj (hmono (had z).le)
      (p d.val) (p z.val) hp (b d) (b z) (hb_small d) (hb_bound z) hnonzero
    exact hA (embed d.val).property (embed z.val).property
      (fun h => hdz.ne (hpinjective h)) hcommon
  have hdisjoint (d z : t) (hne : d ≠ z) : b d ⊓ b z = ⊥ := by
    have hne' : d.val ≠ z.val := fun h => hne (Subtype.ext h)
    rcases lt_or_gt_of_ne hne' with hdz | hzd
    · exact hordered d z hdz
    · rw [inf_comm]
      exact hordered z d hzd
  have hbinjective : Function.Injective b := by
    intro d z h
    by_contra hne
    have hzero := hdisjoint d z hne
    rw [h, inf_idem] at hzero
    exact hb z hzero
  have hcount : (Set.range b).Countable := by
    apply hB (stages a)
    · rintro _ ⟨d, rfl⟩
      exact hb d
    · rintro _ ⟨d, rfl⟩ _ ⟨z, rfl⟩ hne
      exact hdisjoint d z (fun h => hne (congrArg b h))
  have hmaps : Set.MapsTo b Set.univ (Set.range b) := fun d _ => ⟨d, rfl⟩
  have huniv := hmaps.countable_of_injOn hbinjective.injOn hcount
  haveI : Countable t := Set.countable_univ_iff.mp huniv
  have hαgt : ℵ₀ < Order.cof α := by simpa only [hα] using Cardinal.aleph0_lt_aleph_one
  exact stationary_not_countable hαgt ht (Set.to_countable t)

theorem completion_ccc_of_stationary_density
    (hinj : ∀ i j h, Function.Injective (e i j h))
    (hB : ∀ i, Flypitch.BA_CCC (B i))
    (hα : Order.cof α = ℵ₁) (stages : α → ι) (hmono : Monotone stages)
    (hcofinal : ∀ i, ∃ a, i ≤ stages a) (s : Set α) (hs : IsStationary s)
    (hdense : DenseAlong e stages hmono s) :
    Flypitch.BA_CCC (PosetCompletion.Completion (Condition e)) :=
  PosetCompletion.completion_ccc
    (ccc_of_stationary_density e hinj hB hα stages hmono hcofinal s hs hdense)

theorem ccc_of_limit_continuity
    (hinj : ∀ i j h, Function.Injective (e i j h))
    (hB : ∀ i, Flypitch.BA_CCC (B i))
    (hα : Order.cof α = ℵ₁) (stages : α → ι) (hmono : Monotone stages)
    (hcofinal : ∀ i, ∃ a, i ≤ stages a)
    (hdense : DenseAlong e stages hmono {a : α | IsSuccLimit a}) :
    CountableChainCondition (Condition e) := by
  have hαgt : ℵ₀ < Order.cof α := by simpa only [hα] using Cardinal.aleph0_lt_aleph_one
  have hcard : 0 < #α := (Cardinal.aleph0_pos.trans hαgt).trans_le (Order.cof_le_cardinalMk α)
  letI : Nonempty α := Cardinal.mk_ne_zero_iff.mp hcard.ne'
  exact ccc_of_stationary_density e hinj hB hα stages hmono hcofinal _
    ((succLimits_isClub hαgt).isStationary hαgt.ne') hdense

theorem completion_ccc_of_limit_continuity
    (hinj : ∀ i j h, Function.Injective (e i j h))
    (hB : ∀ i, Flypitch.BA_CCC (B i))
    (hα : Order.cof α = ℵ₁) (stages : α → ι) (hmono : Monotone stages)
    (hcofinal : ∀ i, ∃ a, i ≤ stages a)
    (hdense : DenseAlong e stages hmono {a : α | IsSuccLimit a}) :
    Flypitch.BA_CCC (PosetCompletion.Completion (Condition e)) :=
  PosetCompletion.completion_ccc
    (ccc_of_limit_continuity e hinj hB hα stages hmono hcofinal hdense)

theorem denseAlong_of_normal {J : Type} [LinearOrder J]
    {C : J → Type} [∀ j, CompleteBooleanAlgebra (C j)]
    (f : ∀ i j, i ≤ j → CompleteLatticeHom (C i) (C j))
    [DirectedSystem C (f · · ·)]
    (hfinj : ∀ i j h, Function.Injective (f i j h))
    (stages : α → J) (hnormal : Order.IsNormal stages)
    (hdensity : ∀ i, IsSuccLimit i → ∀ c : C i, c ≠ ⊥ →
      ∃ (j : J) (hji : j < i) (b : C j), b ≠ ⊥ ∧ f j i hji.le b ≤ c) :
    DenseAlong f stages hnormal.monotone {a : α | IsSuccLimit a} := by
  intro d hd c hc
  obtain ⟨j, hjd, b, hb, hbound⟩ := hdensity (stages d) (hnormal.map_isSuccLimit hd) c hc
  obtain ⟨a, had, hja⟩ := (hnormal.lt_iff_exists_lt hd).mp hjd
  refine ⟨a, had, f j (stages a) hja.le b, mapped_nonzero f hfinj hja.le hb, ?_⟩
  simpa only [DirectedSystem.map_map' f] using hbound

theorem ccc_of_normal_cofinal {J : Type} [LinearOrder J]
    {C : J → Type} [∀ j, CompleteBooleanAlgebra (C j)]
    (f : ∀ i j, i ≤ j → CompleteLatticeHom (C i) (C j))
    [DirectedSystem C (f · · ·)]
    (hfinj : ∀ i j h, Function.Injective (f i j h))
    (hC : ∀ j, Flypitch.BA_CCC (C j)) (hα : Order.cof α = ℵ₁)
    (stages : α → J) (hnormal : Order.IsNormal stages)
    (hcofinal : ∀ j, ∃ a, j ≤ stages a)
    (hdensity : ∀ i, IsSuccLimit i → ∀ c : C i, c ≠ ⊥ →
      ∃ (j : J) (hji : j < i) (b : C j), b ≠ ⊥ ∧ f j i hji.le b ≤ c) :
    CountableChainCondition (Condition f) :=
  ccc_of_limit_continuity f hfinj hC hα stages hnormal.monotone hcofinal
    (denseAlong_of_normal f hfinj stages hnormal hdensity)

theorem completion_ccc_of_normal_cofinal {J : Type} [LinearOrder J]
    {C : J → Type} [∀ j, CompleteBooleanAlgebra (C j)]
    (f : ∀ i j, i ≤ j → CompleteLatticeHom (C i) (C j))
    [DirectedSystem C (f · · ·)]
    (hfinj : ∀ i j h, Function.Injective (f i j h))
    (hC : ∀ j, Flypitch.BA_CCC (C j)) (hα : Order.cof α = ℵ₁)
    (stages : α → J) (hnormal : Order.IsNormal stages)
    (hcofinal : ∀ j, ∃ a, j ≤ stages a)
    (hdensity : ∀ i, IsSuccLimit i → ∀ c : C i, c ≠ ⊥ →
      ∃ (j : J) (hji : j < i) (b : C j), b ≠ ⊥ ∧ f j i hji.le b ≤ c) :
    Flypitch.BA_CCC (PosetCompletion.Completion (Condition f)) :=
  PosetCompletion.completion_ccc
    (ccc_of_normal_cofinal f hfinj hC hα stages hnormal hcofinal hdensity)

end Erdos597Object.StationaryLimits
