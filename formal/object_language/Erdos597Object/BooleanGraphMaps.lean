import Erdos597Object.BooleanFunctionBridge
import Erdos597Object.BooleanInjections

set_option backward.isDefEq.respectTransparency false

/-! Function and graph-copy names from indexed families of input and output names. -/

namespace Erdos597Object.BooleanGraphMaps

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections

variable {B I : Type} [CompleteBooleanAlgebra B]

noncomputable def mapName (input output : I → bSet B) : bSet B :=
  weightedSet (fun i => bSet.pair (input i) (output i)) (fun _ => ⊤)

theorem map_edge (input output : I → bSet B) (x y : bSet B) :
    edgeValue (V B) (mapName input output) x y =
      ⨆ i, (x =ᴮ input i) ⊓ (y =ᴮ output i) := by
  change (⨆ i, ⊤ ⊓ (bSet.pair x y =ᴮ bSet.pair (input i) (output i))) = _
  simp only [top_inf_eq]
  apply iSup_congr
  intro i
  exact le_antisymm (le_inf bSet.eq_of_eq_pair_left bSet.eq_of_eq_pair_right)
    (bSet.pair_congr inf_le_left inf_le_right)

theorem map_pair_cases (input output : I → bSet B) (context result : B)
    (x a y b : bSet B)
    (hleft : context ≤ edgeValue (V B) (mapName input output) x a)
    (hright : context ≤ edgeValue (V B) (mapName input output) y b)
    (hcases : ∀ i j, (context ⊓ ((x =ᴮ input i) ⊓ (a =ᴮ output i))) ⊓
      ((y =ᴮ input j) ⊓ (b =ᴮ output j)) ≤ result) : context ≤ result := by
  rw [map_edge] at hleft hright
  apply (le_inf le_rfl hleft).trans
  apply lattice.bv_cases_right
  intro i
  apply (le_inf le_rfl (inf_le_left.trans hright)).trans
  apply lattice.bv_cases_right
  intro j
  exact hcases i j

theorem map_between (context : B) (input output : I → bSet B) (target : bSet B)
    (hmembers : ∀ i, context ≤ output i ∈ᴮ target) :
    context ≤ relationBetweenValue (V B) (weightedSet input (fun _ => ⊤)) target
      (mapName input output) := by
  rw [BooleanFunctionBridge.relationBetween_eq_subset_prod]
  apply bSet.subset_intro
  intro i
  change I at i
  apply bSet.mem_prod_iff.mpr
  exact ⟨le_top.trans (weight_le_member input (fun _ => ⊤) i),
    inf_le_left.trans (hmembers i)⟩

theorem map_total (context : B) (input output : I → bSet B) (target : bSet B)
    (hmembers : ∀ i, context ≤ output i ∈ᴮ target) :
    context ≤ totalOnValue (V B) (weightedSet input (fun _ => ⊤)) target
      (mapName input output) := by
  apply le_iInf
  intro x
  apply lattice.bv_imp_intro
  change context ⊓ (x ∈ᴮ weightedSet input (fun _ => ⊤)) ≤
    ⨆ y : bSet B, (y ∈ᴮ target) ⊓ edgeValue (V B) (mapName input output) x y
  rw [member_weightedSet]
  simp only [top_inf_eq]
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  apply le_iSup_of_le (output i)
  apply le_inf (inf_le_left.trans (hmembers i))
  rw [map_edge]
  exact le_iSup_of_le i (le_inf inf_le_right bSet.bv_refl)

theorem map_singleValued (context : B) (input output : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → context ⊓ (input i =ᴮ input j) = ⊥) :
    context ≤ singleValuedValue (V B) (mapName input output) := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  apply map_pair_cases input output _ _ x y x z
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
  intro i j
  let part : B := ((context ⊓
    (edgeValue (V B) (mapName input output) x y ⊓ edgeValue (V B) (mapName input output) x z)) ⊓
    ((x =ᴮ input i) ⊓ (y =ᴮ output i))) ⊓ ((x =ᴮ input j) ⊓ (z =ᴮ output j))
  change part ≤ y =ᴮ z
  have hx : part ≤ x =ᴮ input i := inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hy : part ≤ y =ᴮ output i := inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hx' : part ≤ x =ᴮ input j := inf_le_right.trans inf_le_left
  have hz : part ≤ z =ᴮ output j := inf_le_right.trans inf_le_right
  by_cases hij : i = j
  · subst j
    exact bSet.bv_trans hy (bSet.bv_symm hz)
  · have heq := bSet.bv_trans (bSet.bv_symm hx) hx'
    have hcontext : part ≤ context := inf_le_left.trans (inf_le_left.trans inf_le_left)
    exact ((le_inf hcontext heq).trans_eq (hdiscrete i j hij)).trans bot_le

theorem map_function (context : B) (input output : I → bSet B) (target : bSet B)
    (hdiscrete : ∀ i j, i ≠ j → context ⊓ (input i =ᴮ input j) = ⊥)
    (hmembers : ∀ i, context ≤ output i ∈ᴮ target) :
    context ≤ functionFromValue (V B) (weightedSet input (fun _ => ⊤)) target
      (mapName input output) :=
  le_inf (map_between context input output target hmembers)
    (le_inf (map_singleValued context input output hdiscrete)
      (map_total context input output target hmembers))

theorem map_injective (context : B) (input output : I → bSet B)
    (hdiscrete : ∀ i j, i ≠ j → context ⊓ (output i =ᴮ output j) = ⊥) :
    context ≤ injectiveValue (V B) (mapName input output) := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  apply map_pair_cases input output _ _ x z y z
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
  intro i j
  let part : B := ((context ⊓
    (edgeValue (V B) (mapName input output) x z ⊓ edgeValue (V B) (mapName input output) y z)) ⊓
    ((x =ᴮ input i) ⊓ (z =ᴮ output i))) ⊓ ((y =ᴮ input j) ⊓ (z =ᴮ output j))
  change part ≤ x =ᴮ y
  have hx : part ≤ x =ᴮ input i := inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hz : part ≤ z =ᴮ output i := inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hy : part ≤ y =ᴮ input j := inf_le_right.trans inf_le_left
  have hz' : part ≤ z =ᴮ output j := inf_le_right.trans inf_le_right
  by_cases hij : i = j
  · subst j
    exact bSet.bv_trans hx (bSet.bv_symm hy)
  · have heq := bSet.bv_trans (bSet.bv_symm hz) hz'
    have hcontext : part ≤ context := inf_le_left.trans (inf_le_left.trans inf_le_left)
    exact ((le_inf hcontext heq).trans_eq (hdiscrete i j hij)).trans bot_le

theorem map_preserves (context : B) (input output : I → bSet B) (source target : bSet B)
    (hpreserves : ∀ i j, context ⊓ edgeValue (V B) source (input i) (input j) ≤
      edgeValue (V B) target (output i) (output j)) :
    context ≤ preservesRelationValue (V B) source target (mapName input output) := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  apply le_iInf
  intro a
  apply le_iInf
  intro b
  apply lattice.bv_imp_intro
  apply lattice.bv_imp_intro
  apply map_pair_cases input output _ _ x a y b
    (inf_le_left.trans (inf_le_right.trans inf_le_left))
    (inf_le_left.trans (inf_le_right.trans inf_le_right))
  intro i j
  let base : B := (context ⊓ (edgeValue (V B) (mapName input output) x a ⊓
    edgeValue (V B) (mapName input output) y b)) ⊓ edgeValue (V B) source x y
  let part : B := (base ⊓ ((x =ᴮ input i) ⊓ (a =ᴮ output i))) ⊓
    ((y =ᴮ input j) ⊓ (b =ᴮ output j))
  change part ≤ edgeValue (V B) target a b
  have hbase : part ≤ base := inf_le_left.trans inf_le_left
  have hx : part ≤ x =ᴮ input i := inf_le_left.trans (inf_le_right.trans inf_le_left)
  have ha : part ≤ a =ᴮ output i := inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hy : part ≤ y =ᴮ input j := inf_le_right.trans inf_le_left
  have hb : part ≤ b =ᴮ output j := inf_le_right.trans inf_le_right
  have hsource : part ≤ edgeValue (V B) source (input i) (input j) :=
    bSet.subst_congr_mem_left' (bSet.pair_congr hx hy) (hbase.trans inf_le_right)
  have htarget : part ≤ edgeValue (V B) target (output i) (output j) :=
    (le_inf (hbase.trans (inf_le_left.trans inf_le_left)) hsource).trans (hpreserves i j)
  exact bSet.subst_congr_mem_left' (bSet.pair_congr (bSet.bv_symm ha) (bSet.bv_symm hb)) htarget

end Erdos597Object.BooleanGraphMaps
