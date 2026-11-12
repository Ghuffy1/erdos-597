import Erdos597Object.BooleanForcingTransport
import Erdos597Object.TransfiniteSystems

set_option backward.isDefEq.respectTransparency false

/-! Coherent transport of names and two-step conditions along the iteration embeddings. -/

namespace Erdos597Object.IterationNameTransport

open Flypitch BooleanNameTransport BooleanBoundedTransport BooleanPosetCoding
open scoped Flypitch.bSet

variable {B C : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

def mapPoset {I : Type} (f : CompleteLatticeHom B C) (P : BooleanIteration.BooleanPoset B I) :
    BooleanIteration.BooleanPoset C I where
  member i := f (P.member i)
  leValue i j := f (P.leValue i j)
  le_members i j := by
    simpa only [map_inf] using OrderHomClass.monotone f (P.le_members i j)
  reflexive i := OrderHomClass.monotone f (P.reflexive i)
  transitive i j k := by
    simpa only [map_inf] using OrderHomClass.monotone f (P.transitive i j k)
  antisymmetric i j hij := by
    rw [← map_inf, P.antisymmetric i j hij, map_bot]

theorem mapPoset_compatibleValue {I : Type} (f : CompleteLatticeHom B C)
    (P : BooleanIteration.BooleanPoset B I) (i j : I) :
    f (BooleanIteration.compatibleValue P i j) =
      BooleanIteration.compatibleValue (mapPoset f P) i j := by
  simp only [BooleanIteration.compatibleValue, mapPoset, map_iSup, map_inf]

theorem nameMap_checkLabel {I : Type} (f : CompleteLatticeHom B C) (i : I) :
    nameMap f (checkLabel (B := B) i) = checkLabel (B := C) i :=
  nameMap_check f _

theorem nameMap_domainName {I : Type} (f : CompleteLatticeHom B C)
    (P : BooleanIteration.BooleanPoset B I) (element : I → bSet B) :
    nameMap f (domainName P element) = domainName (mapPoset f P) (fun i => nameMap f (element i)) :=
  rfl

theorem nameMap_orderName {I : Type} (f : CompleteLatticeHom B C)
    (P : BooleanIteration.BooleanPoset B I) (element : I → bSet B) :
    nameMap f (orderName P element) = orderName (mapPoset f P) (fun i => nameMap f (element i)) := by
  unfold orderName BooleanSets.weightedSet
  rw [nameMap_mk]
  congr 1
  funext ij
  exact nameMap_pair f (element ij.1) (element ij.2)

theorem map_ne_bot_iff (f : CompleteLatticeHom B C) (hf : Function.Injective f) (b : B) :
    f b ≠ ⊥ ↔ b ≠ ⊥ := by
  constructor
  · intro h hb
    apply h
    rw [hb, map_bot]
  · intro h hb
    apply h
    apply hf
    simpa only [map_bot] using hb

noncomputable def mapCondition {I : Type} (f : CompleteLatticeHom B C)
    (hf : Function.Injective f) (P : BooleanIteration.BooleanPoset B I)
    (p : BooleanIteration.Condition P) : BooleanIteration.Condition (mapPoset f P) where
  value := f p.value
  label := p.label
  nonzero := (map_ne_bot_iff f hf p.value).mpr p.nonzero
  valid := OrderHomClass.monotone f p.valid

theorem mapCondition_le_iff {I : Type} (f : CompleteLatticeHom B C)
    (hf : Function.Injective f) (P : BooleanIteration.BooleanPoset B I)
    (p q : BooleanIteration.Condition P) :
    mapCondition f hf P p ≤ mapCondition f hf P q ↔ p ≤ q := by
  change (f p.value ≤ f q.value ∧ f p.value ≤ f (P.leValue p.label q.label)) ↔
    (p.value ≤ q.value ∧ p.value ≤ P.leValue p.label q.label)
  rw [map_le_iff f hf, map_le_iff f hf]

theorem mapCondition_injective {I : Type} (f : CompleteLatticeHom B C)
    (hf : Function.Injective f) (P : BooleanIteration.BooleanPoset B I) :
    Function.Injective (mapCondition f hf P) := by
  intro p q hpq
  apply le_antisymm
  · exact (mapCondition_le_iff f hf P p q).mp hpq.le
  · exact (mapCondition_le_iff f hf P q p).mp hpq.ge

theorem mapCondition_compatible_iff {I : Type} (f : CompleteLatticeHom B C)
    (hf : Function.Injective f) (P : BooleanIteration.BooleanPoset B I)
    (p q : BooleanIteration.Condition P) :
    (∃ r, r ≤ mapCondition f hf P p ∧ r ≤ mapCondition f hf P q) ↔
      ∃ r, r ≤ p ∧ r ≤ q := by
  rw [BooleanIteration.compatible_iff, BooleanIteration.compatible_iff]
  change (f p.value ⊓ f q.value ⊓
    BooleanIteration.compatibleValue (mapPoset f P) p.label q.label ≠ ⊥) ↔ _
  rw [← mapPoset_compatibleValue, ← map_inf, ← map_inf]
  exact map_ne_bot_iff f hf _

variable {J : Type} [Preorder J] (S : IterationSystems.System J)

def stageName (i j : J) (hij : i ≤ j) (x : bSet (S.obj i)) : bSet (S.obj j) :=
  nameMap (S.map i j hij) x

theorem stageName_self (i : J) (x : bSet (S.obj i)) : stageName S i i le_rfl x = x := by
  have h : S.map i i le_rfl = CompleteLatticeHom.id (S.obj i) := by
    ext b
    exact DirectedSystem.map_self' S.map b
  unfold stageName
  rw [h, nameMap_id]

theorem stageName_comp (i j k : J) (hij : i ≤ j) (hjk : j ≤ k) (x : bSet (S.obj i)) :
    stageName S j k hjk (stageName S i j hij x) = stageName S i k (hij.trans hjk) x := by
  have h : (S.map j k hjk).comp (S.map i j hij) = S.map i k (hij.trans hjk) := by
    ext b
    exact DirectedSystem.map_map' S.map hij hjk b
  unfold stageName
  rw [← nameMap_comp, h]

end Erdos597Object.IterationNameTransport
