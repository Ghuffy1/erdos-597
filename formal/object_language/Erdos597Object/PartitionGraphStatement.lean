import Erdos597Object.GraphEncoding

set_option backward.isDefEq.respectTransparency false

/-! The finite-target formula expressed with ordinary graphs and order embeddings. -/

namespace Erdos597Object.PartitionGraphStatement

open Erdos597Object.SetInterpretation Erdos597Object.SetFunctions
open Erdos597Object.GraphCopies Erdos597Object.GraphEncoding
open Erdos597Object.SetCodes Erdos597Object.PartitionInterpretation
open scoped SimpleGraph

noncomputable section

theorem redCopy_graphSet_iff (host redDomain hostOrder redOrder : ZFSet.{0})
    (H : SimpleGraph (Members host)) :
    redCopyValue setStructure redDomain host redOrder hostOrder (graphSet H) ↔
      ∃ f : relationOn redDomain redOrder ↪r relationOn host hostOrder,
        ∀ x y : Members redDomain, x ≠ y → ¬ H.Adj (f x) (f y) := by
  simpa only [graphOn_graphSet] using
    redCopyValue_iff_relationEmbedding redDomain host redOrder hostOrder
      (graphSet H) (graphSet_spec H)

theorem finitePartitionValue_iff_graphs (host redDomain hostOrder redOrder : ZFSet.{0}) :
    finitePartitionValue setStructure host redDomain hostOrder redOrder ↔
      ∀ n (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
        ∀ H : SimpleGraph (Members host),
          (∃ f : relationOn redDomain redOrder ↪r relationOn host hostOrder,
            ∀ x y : Members redDomain, x ≠ y → ¬ H.Adj (f x) (f y)) ∨ G ⊑ H := by
  rw [finitePartitionValue_iff_fin_graphs]
  constructor
  · intro h n G hG H
    have hresult := h n G hG (graphSet H) (graphSet_spec H)
    exact (or_congr (redCopy_graphSet_iff host redDomain hostOrder redOrder H)
      (blueCopy_graphSet_iff G H)).mp hresult
  · intro h n G hG blue hblue
    let H := graphOn host blue hblue
    have hresult := h n G hG H
    have hencoded := (or_congr (redCopy_graphSet_iff host redDomain hostOrder redOrder H)
      (blueCopy_graphSet_iff G H)).mpr hresult
    simpa only [H, graphSet_graphOn] using hencoded

end

end Erdos597Object.PartitionGraphStatement
