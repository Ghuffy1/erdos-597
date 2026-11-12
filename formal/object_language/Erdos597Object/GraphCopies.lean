import Erdos597Object.SetCopies

set_option backward.isDefEq.respectTransparency false

/-! The ordinary graph-theoretic meanings of the set-coded copy predicates. -/

namespace Erdos597Object.GraphCopies

open Erdos597Object.SetInterpretation Erdos597Object.SetFunctions
open Erdos597Object.SetCopies
open scoped SimpleGraph

noncomputable section

def graphOn (vertices edges : ZFSet.{0})
    (h : graphValue setStructure vertices edges) : SimpleGraph (Members vertices) where
  Adj x y := ZFSet.pair x.val y.val ∈ edges
  symm := ⟨by
    intro x y hxy
    exact (((graphValue_set _ _).mp h).2.2 _ x.property _ y.property).mp hxy⟩
  loopless := ⟨by
    intro x hxx
    exact ((graphValue_set _ _).mp h).2.1 _ x.property hxx⟩

def relationOn (vertices relation : ZFSet.{0}) (x y : Members vertices) : Prop :=
  ZFSet.pair x.val y.val ∈ relation

theorem blueCopyValue_iff_isContained (domain codomain source target : ZFSet.{0})
    (hsource : graphValue setStructure domain source)
    (htarget : graphValue setStructure codomain target) :
    blueCopyValue setStructure domain codomain source target ↔
      graphOn domain source hsource ⊑ graphOn codomain target htarget := by
  rw [blueCopyValue_iff]
  constructor
  · rintro ⟨f, hinj, hpres⟩
    refine ⟨⟨⟨f, ?_⟩, hinj⟩⟩
    intro x y hxy
    exact hpres x y hxy
  · rintro ⟨f⟩
    exact ⟨f, f.injective, fun x y hxy => f.toHom.map_rel' hxy⟩

theorem redCopyValue_iff_relationEmbedding
    (domain codomain sourceOrder targetOrder blue : ZFSet.{0})
    (hblue : graphValue setStructure codomain blue) :
    redCopyValue setStructure domain codomain sourceOrder targetOrder blue ↔
      ∃ f : relationOn domain sourceOrder ↪r relationOn codomain targetOrder,
        ∀ x y : Members domain, x ≠ y → ¬ (graphOn codomain blue hblue).Adj (f x) (f y) := by
  rw [redCopyValue_iff]
  constructor
  · rintro ⟨f, hinj, horder, havoid⟩
    exact ⟨{ toEmbedding := ⟨f, hinj⟩
             map_rel_iff' := fun {x y} => (horder x y).symm }, havoid⟩
  · rintro ⟨f, havoid⟩
    exact ⟨f, f.injective, fun x y => f.map_rel_iff.symm, havoid⟩

end

end Erdos597Object.GraphCopies
