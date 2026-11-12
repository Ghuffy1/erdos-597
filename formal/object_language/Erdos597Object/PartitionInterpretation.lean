import Erdos597Object.PartitionSemantics

set_option backward.isDefEq.respectTransparency false

/-! Finite-target quantifiers in the ordinary set interpretation. -/

namespace Erdos597Object.PartitionInterpretation

open Flypitch Flypitch.fol Flypitch.ZFC
open Erdos597Object.SetInterpretation Erdos597Object.SetCodes
open Erdos597Object.FinitePresentation Erdos597Object.OrdinalPresentation

local notation "[]" => dvector.nil

@[simp] theorem omegaValue_set :
    setStructure.fun_map ZFCFunc.omega [] = ZFSet.omega := rfl

theorem finitePartitionValue_set_raw (host redDomain hostOrder redOrder : ZFSet.{0}) :
    finitePartitionValue setStructure host redDomain hostOrder redOrder ↔
      ∀ vertices ∈ ZFSet.omega, ∀ edges,
        graphValue setStructure vertices edges →
        cliqueFreeFourValue setStructure vertices edges →
        ∀ blue, graphValue setStructure host blue →
          redCopyValue setStructure redDomain host redOrder hostOrder blue ∨
            blueCopyValue setStructure vertices host edges blue := by
  simp [finitePartitionValue, or_iff_not_imp_left]
  rfl

theorem finitePartitionValue_iff_fin_graphs (host redDomain hostOrder redOrder : ZFSet.{0}) :
    finitePartitionValue setStructure host redDomain hostOrder redOrder ↔
      ∀ n (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
        ∀ blue, graphValue setStructure host blue →
          redCopyValue setStructure redDomain host redOrder hostOrder blue ∨
            blueCopyValue setStructure (naturalSet n) host (edgeSet G) blue := by
  rw [finitePartitionValue_set_raw]
  constructor
  · intro h n G hG blue hblue
    exact h (naturalSet n) (naturalSet_mem_omega n) (edgeSet G)
      (edgeSet_graph G) ((edgeSet_cliqueFree_iff G).mpr hG) blue hblue
  · intro h vertices hvertices edges hgraph hfree blue hblue
    obtain ⟨n, rfl⟩ := (mem_omega_iff vertices).mp hvertices
    let G := decode n edges hgraph
    have hG : G.CliqueFree 4 := (decode_cliqueFree_iff n edges hgraph).mpr hfree
    have hresult := h n G hG blue hblue
    simpa only [G, edgeSet_decode] using hresult

end Erdos597Object.PartitionInterpretation
