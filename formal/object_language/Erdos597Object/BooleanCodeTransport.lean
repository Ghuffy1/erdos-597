import Erdos597Object.GenericFilterModel

set_option backward.isDefEq.respectTransparency false

/-! Transporting the labelled domain, order and dense-family codes exactly. -/

namespace Erdos597Object.BooleanCodeTransport

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanSets BooleanNameTransport BooleanForcingTransport BooleanPosetCoding
open IterationNameTransport

variable {A B I D : Type} [CompleteBooleanAlgebra A] [CompleteBooleanAlgebra B]

theorem map_weighted_check (f : CompleteLatticeHom A B) (weight : I → A) :
    nameMap f (weightedSet checkLabel weight) =
      weightedSet checkLabel (fun i => f (weight i)) := by
  change bSet.mk I (fun i => nameMap f (checkLabel i)) (fun i => f (weight i)) = _
  simp only [nameMap_checkLabel]
  rfl

theorem map_domain_check (f : CompleteLatticeHom A B) (P : BooleanIteration.BooleanPoset A I) :
    nameMap f (domainName P checkLabel) = domainName (mapPoset f P) checkLabel :=
  map_weighted_check f P.member

theorem map_order_check (f : CompleteLatticeHom A B) (P : BooleanIteration.BooleanPoset A I) :
    nameMap f (orderName P checkLabel) = orderName (mapPoset f P) checkLabel := by
  rw [nameMap_orderName]
  simp only [nameMap_checkLabel]

theorem map_family_check (f : CompleteLatticeHom A B) (weight : D → I → A) :
    nameMap f (weightedSet (fun d => weightedSet checkLabel (weight d)) (fun _ => ⊤)) =
      weightedSet (fun d => weightedSet checkLabel (fun i => f (weight d i))) (fun _ => ⊤) := by
  change bSet.mk D (fun d => nameMap f (weightedSet checkLabel (weight d)))
    (fun _ => f ⊤) = _
  simp only [map_weighted_check, map_top]
  rfl

theorem map_dense_code (f : CompleteLatticeHom A B)
    (P : BooleanIteration.BooleanPoset A I) (dense : I → A) :
    f (denseValue (V A) (domainName P checkLabel) (orderName P checkLabel)
      (weightedSet checkLabel dense)) =
      denseValue (V B) (domainName (mapPoset f P) checkLabel)
        (orderName (mapPoset f P) checkLabel) (weightedSet checkLabel (fun i => f (dense i))) := by
  rw [map_denseValue, map_domain_check, map_order_check, map_weighted_check]

theorem reflect_dense_code (f : CompleteLatticeHom A B) (hf : Function.Injective f)
    (P : BooleanIteration.BooleanPoset A I) (dense : I → A)
    (hdense : ⊤ ≤ denseValue (V B) (domainName (mapPoset f P) checkLabel)
      (orderName (mapPoset f P) checkLabel) (weightedSet checkLabel (fun i => f (dense i)))) :
    ⊤ ≤ denseValue (V A) (domainName P checkLabel) (orderName P checkLabel)
      (weightedSet checkLabel dense) := by
  apply (BooleanNameTransport.map_le_iff f hf _ _).mp
  rw [map_top, map_dense_code]
  exact hdense

end Erdos597Object.BooleanCodeTransport
