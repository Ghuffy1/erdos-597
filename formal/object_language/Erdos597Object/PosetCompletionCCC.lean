import Erdos597Object.PosetCompletion

set_option backward.isDefEq.respectTransparency false

/-! The regular-open completion preserves the countable chain condition. -/

namespace Erdos597Object.PosetCompletion

open Set Topology.WithLowerSet
open Erdos597Object.MartinTransport

variable {P : Type} [PartialOrder P]

theorem lower_topology_ccc (hP : CountableChainCondition P) :
    Flypitch.countable_chain_condition (Topology.WithLowerSet P) := by
  classical
  apply Flypitch.countable_chain_condition_of_nonempty
  intro family hnonempty hopen hdisjoint
  have hpoint : ∀ U : family, ∃ p : Topology.WithLowerSet P, p ∈ U.val := by
    intro U
    exact Set.nonempty_iff_ne_empty.mpr (hnonempty U.property)
  choose point hpoint using hpoint
  let choosePoint : family → P := fun U => ofLowerSet (point U)
  have hincompatible : ∀ U V : family, U ≠ V →
      ¬ ∃ r : P, r ≤ choosePoint U ∧ r ≤ choosePoint V := by
    rintro U V hne ⟨r, hrU, hrV⟩
    have hlowerU : IsLowerSet U.val :=
      Topology.IsLowerSet.isOpen_iff_isLowerSet.mp (hopen U.property)
    have hlowerV : IsLowerSet V.val :=
      Topology.IsLowerSet.isOpen_iff_isLowerSet.mp (hopen V.property)
    have hmemU : toLowerSet r ∈ U.val := hlowerU hrU (hpoint U)
    have hmemV : toLowerSet r ∈ V.val := hlowerV hrV (hpoint V)
    exact Set.disjoint_left.mp
      (hdisjoint U.property V.property (fun h => hne (Subtype.ext h))) hmemU hmemV
  have hinjective : Function.Injective choosePoint := by
    intro U V hpointEq
    by_contra hne
    exact hincompatible U V hne ⟨choosePoint U, le_rfl, by rw [hpointEq]⟩
  have hanti : (Set.range choosePoint).Pairwise
      (fun p q => ¬ ∃ r : P, r ≤ p ∧ r ≤ q) := by
    rintro p ⟨U, rfl⟩ q ⟨V, rfl⟩ hpq
    exact hincompatible U V (fun h => hpq (congrArg choosePoint h))
  have hcount := hP (Set.range choosePoint) hanti
  have hmaps : Set.MapsTo choosePoint Set.univ (Set.range choosePoint) :=
    fun U _ => ⟨U, rfl⟩
  have huniv := hmaps.countable_of_injOn hinjective.injOn hcount
  haveI : Countable family := Set.countable_univ_iff.mp huniv
  exact Set.to_countable family

theorem completion_ccc (hP : CountableChainCondition P) :
    Flypitch.BA_CCC (Completion P) :=
  Flypitch.CCC_regular_opens (Topology.WithLowerSet P) (lower_topology_ccc hP)

theorem two_step_completion_ccc {B I : Type} [CompleteBooleanAlgebra B]
    (hB : Flypitch.BA_CCC B) (P : BooleanIteration.BooleanPoset B I)
    (hccc : ⊤ ≤ countableChainConditionValue (Flypitch.ZFC.V B)
      (BooleanPosetCoding.domainName P BooleanPosetCoding.checkLabel)
      (BooleanPosetCoding.orderName P BooleanPosetCoding.checkLabel)) :
    Flypitch.BA_CCC (Completion (BooleanIteration.Condition P)) :=
  completion_ccc (BooleanPosetCoding.two_step_ccc_checkLabels hB P hccc)

end Erdos597Object.PosetCompletion
