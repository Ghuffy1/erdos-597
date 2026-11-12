import Erdos597Object.BooleanClosedUncountability

set_option backward.isDefEq.respectTransparency false

/-! A schedule presentation of the sparse graph and its countable-prefix dependence. -/

namespace Erdos597Object.ScheduledSparseGraph

open Erdos597
open Set Function

noncomputable instance initialSegmentEncodable (b : One) : Encodable (Iio b) := by
  have : Countable (Iio b) := BooleanCountableNames.below_countable b
  exact Encodable.ofCountable _

noncomputable def requests (schedule : One → Pattern) (a b : One) (n : Nat) :
    Option (BelowPattern a b) := by
  classical
  exact (Encodable.decode (α := Iio b) n).bind fun index =>
    if h : (∀ k, a < (schedule index.val).row k) ∧
        ∀ k m, (schedule index.val).column k m < b then
      some ⟨schedule index.val, h⟩
    else none

theorem requests_covers (schedule : One → Pattern) (a b index : One)
    (hindex : index < b) (hrow : ∀ k, a < (schedule index).row k)
    (hcolumn : ∀ k m, (schedule index).column k m < b) :
    requests schedule a b (Encodable.encode (⟨index, hindex⟩ : Iio b)) =
      some ⟨schedule index, hrow, hcolumn⟩ := by
  classical
  simp [requests, hrow, hcolumn]

theorem requests_prefix (left right : One → Pattern) (a b : One)
    (hprefix : ∀ index, index < b → left index = right index) :
    requests left a b = requests right a b := by
  funext n
  unfold requests
  cases hdecode : Encodable.decode (α := Iio b) n with
  | none => rfl
  | some index =>
    simp only [Option.bind_some]
    rw [hprefix index.val index.property]

structure Neighborhood (code : RowCodes) (a b : One) where
  seq : Nat → Option Vertex
  nested : ∀ n p, seq n = some p → Nested (a, b) p
  rows_ne : ∀ i j p q, i < j → seq i = some p → seq j = some q → p.1 ≠ q.1
  source_weight : ∀ i j p q, i < j → seq i = some p → seq j = some q → q.1 < p.1 →
    rowWeight code p.1 a < rowWeight code p.1 q.1
  earlier_weight : ∀ i j k p q r, i < k → j < k →
    seq i = some p → seq j = some q → seq k = some r → r.1 < p.1 → q.1 < p.1 →
      rowWeight code p.1 q.1 < rowWeight code p.1 r.1

namespace Neighborhood

variable {code : RowCodes} {a b : One}

def out (N : Neighborhood code a b) (p : Vertex) : Prop := ∃ n, N.seq n = some p

noncomputable def stage (N : Neighborhood code a b) (p : Vertex) : Nat := by
  classical
  exact if h : N.out p then Nat.find h else 0

theorem stage_spec (N : Neighborhood code a b) {p : Vertex} (hp : N.out p) :
    N.seq (N.stage p) = some p := by
  classical
  simpa only [stage, dite_eq_left hp] using Nat.find_spec hp

theorem nested_of_out (N : Neighborhood code a b) {p : Vertex} (hp : N.out p) :
    Nested (a, b) p := N.nested _ _ (N.stage_spec hp)

theorem eq_of_stage_eq (N : Neighborhood code a b) {p q : Vertex}
    (hp : N.out p) (hq : N.out q) (h : N.stage p = N.stage q) : p = q := by
  have hseq : N.seq (N.stage p) = some q := by simpa only [h] using N.stage_spec hq
  exact Option.some.inj ((N.stage_spec hp).symm.trans hseq)

theorem one_per_row (N : Neighborhood code a b) {p q : Vertex}
    (hp : N.out p) (hq : N.out q) (hrow : p.1 = q.1) : p = q := by
  rcases lt_trichotomy (N.stage p) (N.stage q) with h | h | h
  · exact False.elim (N.rows_ne _ _ _ _ h (N.stage_spec hp) (N.stage_spec hq) hrow)
  · exact N.eq_of_stage_eq hp hq h
  · exact False.elim (N.rows_ne _ _ _ _ h (N.stage_spec hq) (N.stage_spec hp) hrow.symm)

end Neighborhood

noncomputable def neighborhood (code : RowCodes) (a b : One)
    (old : Vertex → Vertex → Prop)
    (hone : ∀ x y z, old x y → old x z → y.1 = z.1 → y = z)
    (request : Nat → Option (BelowPattern a b)) : Neighborhood code a b where
  seq := LocalNeighborhood.pointAt code a b old hone request
  nested := fun _ _ h => LocalNeighborhood.pointAt_nested code a b old hone request h
  rows_ne := fun _ _ _ _ hij hp hq => LocalNeighborhood.rows_ne_of_lt code a b old hone request hij hp hq
  source_weight := fun _ _ _ _ hij hp hq hrow =>
    LocalNeighborhood.source_weight_of_lt code a b old hone request hij hp hq hrow
  earlier_weight := fun _ _ _ _ _ _ hik hjk hp hq hr hrp hqp =>
    LocalNeighborhood.earlier_weight_of_lt code a b old hone request hik hjk hp hq hr hrp hqp

theorem neighborhood_congr (code : RowCodes) (a b : One)
    {old₁ old₂ : Vertex → Vertex → Prop} (heq : old₁ = old₂)
    (h₁ : ∀ x y z, old₁ x y → old₁ x z → y.1 = z.1 → y = z)
    (h₂ : ∀ x y z, old₂ x y → old₂ x z → y.1 = z.1 → y = z)
    {r₁ r₂ : Nat → Option (BelowPattern a b)} (hr : r₁ = r₂) :
    neighborhood code a b old₁ h₁ r₁ = neighborhood code a b old₂ h₂ r₂ := by
  cases heq
  cases hr
  rfl

def previousRelation (code : RowCodes) (b : One)
    (previous : ∀ c, c < b → ∀ a, Neighborhood code a c) (x y : Vertex) : Prop :=
  ∃ h : x.2 < b, (previous x.2 h x.1).out y

theorem previous_one_per_row (code : RowCodes) (b : One)
    (previous : ∀ c, c < b → ∀ a, Neighborhood code a c)
    (x y z : Vertex) (hy : previousRelation code b previous x y)
    (hz : previousRelation code b previous x z) (hrow : y.1 = z.1) : y = z := by
  obtain ⟨h, hy⟩ := hy
  obtain ⟨_, hz⟩ := hz
  exact (previous x.2 h x.1).one_per_row hy hz hrow

noncomputable def family (schedule : One → Pattern) (code : RowCodes) :
    ∀ b a : One, Neighborhood code a b :=
  wellFounded_lt.fix fun b previous a =>
    neighborhood code a b (previousRelation code b previous)
      (previous_one_per_row code b previous) (requests schedule a b)

theorem family_eq (schedule : One → Pattern) (code : RowCodes) (b a : One) :
    family schedule code b a = neighborhood code a b
      (previousRelation code b (fun c _ => family schedule code c))
      (previous_one_per_row code b (fun c _ => family schedule code c))
      (requests schedule a b) := by
  rw [family, WellFounded.fix_eq]

theorem family_prefix (left right : One → Pattern) (code : RowCodes) (b a : One)
    (hprefix : ∀ index, index < b → left index = right index) :
    family left code b a = family right code b a := by
  have wf : WellFounded (fun x y : One => x < y) := wellFounded_lt
  suffices hmain : ∀ b : One, (∀ index, index < b → left index = right index) →
      ∀ a, family left code b a = family right code b a from hmain b hprefix a
  intro b
  apply wf.induction b
  intro b ih hprefix a
  have hprevious :
      previousRelation code b (fun c _ => family left code c) =
        previousRelation code b (fun c _ => family right code c) := by
    funext x y
    apply propext
    constructor
    · rintro ⟨hx, hxy⟩
      refine ⟨hx, ?_⟩
      change (family right code x.2 x.1).out y
      rw [← ih x.2 hx (fun index hi => hprefix index (hi.trans hx)) x.1]
      exact hxy
    · rintro ⟨hx, hxy⟩
      refine ⟨hx, ?_⟩
      change (family left code x.2 x.1).out y
      rw [ih x.2 hx (fun index hi => hprefix index (hi.trans hx)) x.1]
      exact hxy
  rw [family_eq, family_eq]
  exact neighborhood_congr code a b hprevious _ _ (requests_prefix left right a b hprefix)

variable (schedule : One → Pattern) (code : RowCodes)

def out (x y : Vertex) : Prop := (family schedule code x.2 x.1).out y

noncomputable def stage (x y : Vertex) : Nat := (family schedule code x.2 x.1).stage y

theorem nested {x y : Vertex} (h : out schedule code x y) : Nested x y :=
  (family schedule code x.2 x.1).nested_of_out h

theorem loopless (x : Vertex) : ¬ out schedule code x x := by
  intro h
  exact (lt_irrefl x.1) (nested schedule code h).1

theorem avoids {x u v : Vertex} (hu : out schedule code x u) (hv : out schedule code x v)
    (hstage : stage schedule code x u < stage schedule code x v) :
    ¬ previousRelation code x.2 (fun c _ => family schedule code c) u v := by
  have heq := family_eq schedule code x.2 x.1
  change (family schedule code x.2 x.1).out u at hu
  change (family schedule code x.2 x.1).out v at hv
  change (family schedule code x.2 x.1).stage u < (family schedule code x.2 x.1).stage v at hstage
  rw [heq] at hu hv hstage
  exact LocalNeighborhood.avoids_of_lt code x.1 x.2 _ _ (requests schedule x.1 x.2) hstage
    (Neighborhood.stage_spec _ hu) (Neighborhood.stage_spec _ hv)

theorem reversal {x u v : Vertex} (hu : out schedule code x u) (hv : out schedule code x v)
    (huv : out schedule code u v) : stage schedule code x v < stage schedule code x u := by
  by_contra h
  rcases lt_or_eq_of_le (le_of_not_gt h) with hlt | heq
  · apply avoids schedule code hu hv hlt
    exact ⟨(nested schedule code hu).2.2, huv⟩
  · have huvEq : u = v := (family schedule code x.2 x.1).eq_of_stage_eq hu hv heq
    subst v
    exact loopless schedule code u huv

noncomputable def rules : SelectionRules where
  out := out schedule code
  stage := stage schedule code
  weight := rowWeight code
  nested := nested schedule code
  reversal := reversal schedule code
  sourceWeight := by
    intro x u v hu hv hstage hrow
    exact (family schedule code x.2 x.1).source_weight _ _ v u hstage
      (Neighborhood.stage_spec _ hv) (Neighborhood.stage_spec _ hu) hrow
  earlierWeight := by
    intro x u v w hu hv hw hwu hvu huw hvw
    exact (family schedule code x.2 x.1).earlier_weight _ _ _ w v u hwu hvu
      (Neighborhood.stage_spec _ hw) (Neighborhood.stage_spec _ hv)
      (Neighborhood.stage_spec _ hu) huw hvw

theorem hits_index (index a b : One) (hindex : index < b)
    (hrow : ∀ k, a < (schedule index).row k)
    (hcolumn : ∀ k m, (schedule index).column k m < b) :
    ∃ i j, (rules schedule code).graph.Adj (a, b) ((schedule index).point i j) := by
  have hrequest := requests_covers schedule a b index hindex hrow hcolumn
  obtain ⟨i, j, hij⟩ := LocalNeighborhood.hits_request code a b
    (previousRelation code b (fun c _ => family schedule code c))
    (previous_one_per_row code b (fun c _ => family schedule code c))
    (requests schedule a b) hrequest
  refine ⟨i, j, Or.inl ?_⟩
  change (family schedule code b a).out ((schedule index).point i j)
  rw [family_eq]
  exact ⟨_, hij⟩

theorem hits_patterns (hsurjective : Surjective schedule) : HitsPatterns (rules schedule code).graph := by
  intro P
  obtain ⟨index, rfl⟩ := hsurjective P
  exact ⟨index, fun a b hi hr hc => hits_index schedule code index a b hi hr hc⟩

theorem graph_prefix (left right : One → Pattern) (code : RowCodes) (bound : One)
    (hprefix : ∀ index, index < bound → left index = right index)
    (x y : Vertex) (hx : x.2 ≤ bound) (hy : y.2 ≤ bound) :
    (rules left code).graph.Adj x y ↔ (rules right code).graph.Adj x y := by
  change (out left code x y ∨ out left code y x) ↔
    (out right code x y ∨ out right code y x)
  unfold out
  rw [family_prefix left right code x.2 x.1 (fun index hi => hprefix index (hi.trans_le hx)),
    family_prefix left right code y.2 y.1 (fun index hi => hprefix index (hi.trans_le hy))]

end Erdos597Object.ScheduledSparseGraph
