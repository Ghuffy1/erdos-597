import Erdos597Object.BooleanOrdinalBridge
import Erdos597Object.BooleanFilterSemantics

set_option backward.isDefEq.respectTransparency false

/-! Total choices of condition names with the required contextual witness properties. -/

namespace Erdos597Object.PosetNameWitnesses

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanInjections BooleanAntichains

variable {B : Type} [CompleteBooleanAlgebra B]

theorem exists_seed {context : B} (domain : bSet B)
    (hnonempty : context ≤ nonemptyValue (V B) domain) :
    ∃ seed : bSet B, context ≤ seed ∈ᴮ domain :=
  bSet.exists_convert hnonempty (bSet.B_ext_mem_left domain)

theorem exists_total_witness {context : B} (domain seed : bSet B)
    (hseed : context ≤ seed ∈ᴮ domain) (active : B) (predicate : bSet B → B)
    (hext : bSet.B_ext predicate)
    (hexists : context ⊓ active ≤ ⨆ x : bSet B, (x ∈ᴮ domain) ⊓ predicate x) :
    ∃ witness : bSet B, context ≤ witness ∈ᴮ domain ∧
      context ⊓ active ≤ predicate witness := by
  obtain ⟨witness, hwitness⟩ := bSet.exists_convert hexists
    (bSet.B_ext_inf (bSet.B_ext_mem_left domain) hext)
  let totalPredicate := fun x : bSet B => (x ∈ᴮ domain) ⊓ lattice.imp active (predicate x)
  have hpositive : context ⊓ active ≤ ⨆ x : bSet B, totalPredicate x :=
    le_iSup_of_le witness (le_inf (hwitness.trans inf_le_left)
      ((hwitness.trans inf_le_right).trans le_sup_right))
  have hnegative : context ⊓ activeᶜ ≤ ⨆ x : bSet B, totalPredicate x :=
    le_iSup_of_le seed (le_inf (inf_le_left.trans hseed) (inf_le_right.trans le_sup_left))
  have htotal : context ≤ ⨆ x : bSet B, totalPredicate x := by
    calc
      context = context ⊓ (active ⊔ activeᶜ) := by simp
      _ = (context ⊓ active) ⊔ (context ⊓ activeᶜ) := inf_sup_left _ _ _
      _ ≤ _ := sup_le hpositive hnegative
  obtain ⟨chosen, hchosen⟩ := bSet.exists_convert htotal
    (bSet.B_ext_inf (bSet.B_ext_mem_left domain)
      (bSet.B_ext_imp (bSet.B_ext_const _) hext))
  exact ⟨chosen, hchosen.trans inf_le_left,
    lattice.le_imp_iff.mp (hchosen.trans inf_le_right)⟩

theorem exists_common_witness {context : B} (domain relation seed x y : bSet B)
    (hseed : context ≤ seed ∈ᴮ domain) :
    ∃ witness : bSet B, context ≤ witness ∈ᴮ domain ∧
      context ⊓ Erdos597Object.compatibleValue (V B) domain relation x y ≤
        edgeValue (V B) relation witness x ⊓ edgeValue (V B) relation witness y :=
  exists_total_witness domain seed hseed _ _ (compatibleWitness_ext relation x y) inf_le_right

theorem exists_dense_witness {context : B} (domain relation denseSet seed x : bSet B)
    (hseed : context ≤ seed ∈ᴮ domain) (active : B)
    (hx : context ⊓ active ≤ x ∈ᴮ domain)
    (hdense : context ⊓ active ≤ denseValue (V B) domain relation denseSet) :
    ∃ witness : bSet B, context ≤ witness ∈ᴮ domain ∧
      context ⊓ active ≤ (witness ∈ᴮ denseSet) ⊓ edgeValue (V B) relation witness x := by
  apply exists_total_witness domain seed hseed active
    (fun y => (y ∈ᴮ denseSet) ⊓ edgeValue (V B) relation y x)
    (bSet.B_ext_inf (bSet.B_ext_mem_left denseSet) (edge_left_ext relation x))
  have hsubset : context ⊓ active ≤ denseSet ⊆ᴮ domain := by
    simpa only [subsetValue_bSet] using! hdense.trans inf_le_left
  have himp := (hdense.trans inf_le_right).trans (iInf_le _ x)
  have hexists := lattice.bv_context_apply himp hx
  obtain ⟨witness, hwitness⟩ := bSet.exists_convert hexists
    (bSet.B_ext_inf (bSet.B_ext_mem_left denseSet) (edge_left_ext relation x))
  exact le_iSup_of_le witness (le_inf
    (bSet.mem_of_mem_subset' hsubset (hwitness.trans inf_le_left)) hwitness)

end Erdos597Object.PosetNameWitnesses
