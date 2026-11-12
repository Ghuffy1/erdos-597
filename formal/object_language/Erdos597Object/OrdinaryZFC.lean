import Erdos597Object.SetCollection
import Erdos597Object.SetZorn

set_option backward.isDefEq.respectTransparency false

/-! The ordinary set structure satisfies the complete first-order ZFC theory. -/

namespace Erdos597Object.OrdinaryZFC

open Flypitch Flypitch.fol Flypitch.fol.bfol Flypitch.ZFC
open Erdos597Object.SetInterpretation Erdos597Object.SetAxioms
open Erdos597Object.SetCollection Erdos597Object.SetZorn

theorem set_realizes_ZFC (f : sentence L_ZFC) (hf : f ∈ Flypitch.ZFC.ZFC) :
    boolean_realize_sentence setStructure f := by
  change f ∈
    (({axiomOfEmptyset, axiomOfOrderedPairs, axiomOfExtensionality, axiomOfUnion,
        axiomOfPowerset, axiomOfInfinity, axiomOfRegularity, zornsLemma} : Set (sentence L_ZFC)) ∪
      Set.iUnion (fun n : ℕ =>
        (fun f : bounded_formula L_ZFC (n + 2) => axiomOfCollection f) '' Set.univ)) at hf
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_iUnion,
    Set.mem_image, Set.mem_univ, true_and] at hf
  rcases hf with hbase | hcollection
  · rcases hbase with hf | hf | hf | hf | hf | hf | hf | hf
    · subst f; exact set_models_emptyset
    · subst f; exact set_models_ordered_pairs
    · subst f; exact set_models_extensionality
    · subst f; exact set_models_union
    · subst f; exact set_models_powerset
    · subst f; exact set_models_infinity
    · subst f; exact set_models_regularity
    · subst f; exact set_models_zorn
  · rcases hcollection with ⟨n, f, _, rfl⟩
    exact set_models_collection f

theorem set_models_ZFC : forces_theory (⊤ : Prop) setStructure Flypitch.ZFC.ZFC := by
  unfold forces_theory
  apply le_iInf
  intro f
  apply le_iInf
  intro hf
  exact fun _ => set_realizes_ZFC f hf

end Erdos597Object.OrdinaryZFC
