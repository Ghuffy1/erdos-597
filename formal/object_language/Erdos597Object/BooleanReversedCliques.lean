import Erdos597Object.BooleanBadCliques
import Erdos597Object.BooleanSymmetricPairs

set_option backward.isDefEq.respectTransparency false

/-! Finite clique extraction with countable forward fibres. -/

namespace Erdos597Object.BooleanReversedCliques

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanGoodPairs BooleanGraphNeighborhoods BooleanCountableRectangles
open BooleanBadCliques BooleanSymmetricPairs BooleanFiniteGraphs

variable {B : Type} [CompleteBooleanAlgebra B]

theorem blueCopy_of_forward_pairs (hB : Flypitch.BA_CCC B) (context : B) (n : ℕ)
    (ambient relation : bSet B) (domain : Fin n → bSet B) (label : Fin n → Erdos597.One → bSet B)
    (hdiscrete : ∀ i a b, a ≠ b → (label i a =ᴮ label i b) = ⊥)
    (hsubset : ∀ i, context ≤ domain i ⊆ᴮ weightedSet (label i) (fun _ => ⊤))
    (hambient : ∀ i, context ≤ domain i ⊆ᴮ ambient)
    (hlarge : ∀ i, context ≤ (injectsIntoValue (V B) (domain i) bSet.omega)ᶜ)
    (hgraph : context ≤ graphValue (V B) ambient relation)
    (hbad : ∀ i j, i < j → context ≤ badPair relation (domain i) (domain j))
    (hforward : ∀ i j, i < j → ∀ x, context ⊓ (x ∈ᴮ domain i) ≤
      injectsIntoValue (V B) (neighborhood (domain j) relation x) bSet.omega) :
    context ≤ blueCopyValue (V B) (bSet.ofNat n) ambient
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation := by
  let reversedDomain : Fin n → bSet B := fun i => domain i.rev
  let reversedLabel : Fin n → Erdos597.One → bSet B := fun i => label i.rev
  have hbadReversed (i j : Fin n) (hij : i < j) :
      context ≤ badPair relation (reversedDomain i) (reversedDomain j) :=
    badPair_swap context ambient relation (domain j.rev) (domain i.rev) hgraph
      (hambient j.rev) (hambient i.rev) (hbad j.rev i.rev (Fin.rev_strictAnti hij))
  have hbackward (i j : Fin n) (hij : i < j) (y : bSet B) :
      context ⊓ (y ∈ᴮ reversedDomain j) ≤
        injectsIntoValue (V B) (predecessors (reversedDomain i) relation y) bSet.omega := by
    let part := context ⊓ (y ∈ᴮ domain j.rev)
    have hy : part ≤ y ∈ᴮ ambient :=
      bSet.mem_of_mem_subset' (inf_le_left.trans (hambient j.rev)) inf_le_right
    exact countable_predecessors_of_neighborhood part ambient relation (domain i.rev) y
      (inf_le_left.trans hgraph) (inf_le_left.trans (hambient i.rev)) hy
      (hforward j.rev i.rev (Fin.rev_strictAnti hij) y)
  exact blueCopy_of_bad_pairs hB context n ambient relation reversedDomain reversedLabel
    (fun i => hdiscrete i.rev) (fun i => hsubset i.rev) (fun i => hambient i.rev)
    (fun i => hlarge i.rev) hgraph hbadReversed hbackward

end Erdos597Object.BooleanReversedCliques
