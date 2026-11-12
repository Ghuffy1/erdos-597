import Erdos597Object.BooleanRowsFromSupport
import Erdos597Object.BooleanIndependentRows

set_option backward.isDefEq.respectTransparency false

/-! Ordered weakly independent rows in the constructed Martin model. -/

namespace Erdos597Object.BooleanWeakRows

open Flypitch Flypitch.ZFC
open scoped Flypitch.bSet
open BooleanRowValues BooleanRowsFromSupport BooleanOrientedSupport BooleanOrientedGraphs
open BooleanPartsGood BooleanGoodPairs BooleanRowOrder CanonicalDomains BooleanIndependentRows
open BooleanCanonicalRows BooleanCliqueCopies BooleanLocalGraphs BooleanUncountableRamsey
open BooleanFiniteGraphs

theorem ordered_good_rows (base : ScheduledIteration.finalAlgebra) (n : ℕ)
    (relation : bSet ScheduledIteration.finalAlgebra)
    (domain : ℕ → bSet ScheduledIteration.finalAlgebra)
    (hsubset : ∀ r, base ≤ domain r ⊆ᴮ blockDomain)
    (hlarge : ∀ r, base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra)
      (domain r) bSet.omega)ᶜ)
    (hordered : ∀ r s, r < s → base ≤ allBefore blockOrder (domain r) (domain s))
    (hgraph : base ≤ graphValue (V ScheduledIteration.finalAlgebra) blockDomain relation)
    (hno : base ≤ (blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n) blockDomain
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation)ᶜ) :
    ∃ rows, base ≤ rowFamilyValue blockDomain relation blockOrder rows := by
  obtain ⟨upRows, hupRows⟩ := exists_rows_of_blockSupport base blockDomain (upPart relation) blockOrder
    domain hlarge hsubset hordered n
    (up_support_of_no_blue base n relation domain hsubset hlarge hordered hgraph hno)
  obtain ⟨hupLarge, hupSubset, hupGood, hupOrdered⟩ :=
    (rowFamilyValue_spec base blockDomain (upPart relation) blockOrder upRows).mp hupRows
  obtain ⟨rows, hfirst, hsecond⟩ :=
    exists_two_rows_of_blockSupport base blockDomain (upPart relation) (downPart relation) blockOrder
      upRows hupLarge hupSubset hupOrdered hupGood n
      (down_support_of_no_blue base n relation upRows hupSubset hupLarge hupOrdered hgraph hno)
  obtain ⟨hlargeRows, hsubsetRows, hfirstGood, horderRows⟩ :=
    (rowFamilyValue_spec base blockDomain (upPart relation) blockOrder rows).mp hfirst
  obtain ⟨_hlargeSecond, _hsubsetSecond, hsecondGood, _horderSecond⟩ :=
    (rowFamilyValue_spec base blockDomain (downPart relation) blockOrder rows).mp hsecond
  refine ⟨rows, rowFamilyValue_intro base blockDomain relation blockOrder rows
    hlargeRows hsubsetRows ?_ horderRows⟩
  intro i j hij
  exact goodPair_of_parts base relation (rows i) (rows j) (hsubsetRows i) (hsubsetRows j)
    (hfirstGood i j hij) (hsecondGood i j hij)

theorem canonical_good_rows (base : ScheduledIteration.finalAlgebra) (n : ℕ)
    (relation : bSet ScheduledIteration.finalAlgebra)
    (hgraph : base ≤ graphValue (V ScheduledIteration.finalAlgebra) blockDomain relation)
    (hno : base ≤ (blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n) blockDomain
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation)ᶜ) :
    ∃ rows, base ≤ rowFamilyValue blockDomain relation blockOrder rows :=
  ordered_good_rows base n relation rowDomain (fun r => le_top.trans (rowDomain_subset r))
    (fun r => le_top.trans (rowDomain_uncountable ScheduledIteration.finalAlgebra.ccc r))
    (fun _ _ h => le_top.trans (rowDomain_before h)) hgraph hno

theorem independent_refinement (base : ScheduledIteration.finalAlgebra) (n : ℕ)
    (relation : bSet ScheduledIteration.finalAlgebra)
    (rows : ℕ → bSet ScheduledIteration.finalAlgebra)
    (hrows : base ≤ rowFamilyValue blockDomain relation blockOrder rows)
    (hgraph : base ≤ graphValue (V ScheduledIteration.finalAlgebra) blockDomain relation)
    (hno : base ≤ (blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n) blockDomain
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation)ᶜ) :
    ∃ independent, base ≤ rowFamilyValue blockDomain relation blockOrder independent ∧
      ∀ i, base ≤ independentValue (independent i) relation := by
  classical
  obtain ⟨hlarge, hsubset, hgood, hordered⟩ :=
    (rowFamilyValue_spec base blockDomain relation blockOrder rows).mp hrows
  have hexists (i : ℕ) : ∃ independent : bSet ScheduledIteration.finalAlgebra,
      base ≤ independent ⊆ᴮ rows i ∧
      base ≤ (injectsIntoValue (V ScheduledIteration.finalAlgebra) independent bSet.omega)ᶜ ∧
      base ≤ independentValue independent relation :=
    uncountable_independent_of_no_blueClique ScheduledIteration.finalAlgebra.ccc base
      allBlockLabel allBlockLabel_discrete (rows i) blockDomain relation n
      (allBlockDomain_subset base (rows i) (hsubset i)) (hsubset i) (hlarge i) hgraph hno
  let independent := fun i => Classical.choose (hexists i)
  have hspec (i : ℕ) := Classical.choose_spec (hexists i)
  refine ⟨independent, ?_, fun i => (hspec i).2.2⟩
  apply rowFamilyValue_intro
  · exact fun i => (hspec i).2.1
  · exact fun i => subset_trans (hspec i).1 (hsubset i)
  · intro i j hij
    exact goodPair_restrict base relation (rows i) (rows j) (independent i) (independent j)
      (hspec i).1 (hspec j).1 (hgood i j hij)
  · intro i j hij
    exact allBefore_restrict base blockOrder (rows i) (rows j) (independent i) (independent j)
      (hspec i).1 (hspec j).1 (hordered i j hij)

theorem canonical_weak_rows (base : ScheduledIteration.finalAlgebra) (n : ℕ)
    (relation : bSet ScheduledIteration.finalAlgebra)
    (hgraph : base ≤ graphValue (V ScheduledIteration.finalAlgebra) blockDomain relation)
    (hno : base ≤ (blueCopyValue (V ScheduledIteration.finalAlgebra) (bSet.ofNat n) blockDomain
      (graphName naturalLabel (⊤ : SimpleGraph (Fin n))) relation)ᶜ) :
    ∃ rows, base ≤ rowFamilyValue blockDomain relation blockOrder rows ∧
      ∀ i, base ≤ independentValue (rows i) relation := by
  obtain ⟨rows, hrows⟩ := canonical_good_rows base n relation hgraph hno
  exact independent_refinement base n relation rows hrows hgraph hno

end Erdos597Object.BooleanWeakRows
