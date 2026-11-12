import Erdos597Object.PartitionInterpretation

set_option backward.isDefEq.respectTransparency false

/-! Exact encoding of all graphs on the elements of a set. -/

namespace Erdos597Object.GraphEncoding

open Erdos597Object.SetInterpretation Erdos597Object.SetFunctions
open Erdos597Object.GraphCopies Erdos597Object.SetCodes
open scoped SimpleGraph

noncomputable section

def graphSet {vertices : ZFSet.{0}} (G : SimpleGraph (Members vertices)) : ZFSet.{0} :=
  ZFSet.range fun e : {p : Members vertices × Members vertices // G.Adj p.1 p.2} =>
    ZFSet.pair e.val.1.val e.val.2.val

theorem pair_mem_graphSet {vertices : ZFSet.{0}} (G : SimpleGraph (Members vertices))
    (x y : Members vertices) :
    ZFSet.pair x.val y.val ∈ graphSet G ↔ G.Adj x y := by
  constructor
  · intro h
    obtain ⟨⟨⟨a, b⟩, hab⟩, heq⟩ := ZFSet.mem_range.mp h
    obtain ⟨ha, hb⟩ := ZFSet.pair_inj.mp heq
    have hax : a = x := Subtype.ext ha
    have hby : b = y := Subtype.ext hb
    simpa only [hax, hby] using hab
  · intro h
    exact ZFSet.mem_range.mpr ⟨⟨(x, y), h⟩, rfl⟩

theorem graphSet_spec {vertices : ZFSet.{0}} (G : SimpleGraph (Members vertices)) :
    graphValue setStructure vertices (graphSet G) := by
  rw [graphValue_set]
  refine ⟨?_, ?_, ?_⟩
  · intro entry hentry
    obtain ⟨⟨⟨x, y⟩, _⟩, rfl⟩ := ZFSet.mem_range.mp hentry
    exact ⟨x.val, x.property, y.val, y.property, rfl⟩
  · intro x hx hxx
    exact G.loopless.irrefl ⟨x, hx⟩ ((pair_mem_graphSet G ⟨x, hx⟩ ⟨x, hx⟩).mp hxx)
  · intro x hx y hy
    exact (pair_mem_graphSet G ⟨x, hx⟩ ⟨y, hy⟩).trans
      ((G.adj_comm ⟨x, hx⟩ ⟨y, hy⟩).trans (pair_mem_graphSet G ⟨y, hy⟩ ⟨x, hx⟩).symm)

theorem graphOn_graphSet {vertices : ZFSet.{0}} (G : SimpleGraph (Members vertices)) :
    graphOn vertices (graphSet G) (graphSet_spec G) = G := by
  ext x y
  exact pair_mem_graphSet G x y

theorem graphSet_graphOn (vertices edges : ZFSet.{0})
    (h : graphValue setStructure vertices edges) : graphSet (graphOn vertices edges h) = edges := by
  apply ZFSet.ext
  intro entry
  constructor
  · intro hentry
    obtain ⟨⟨⟨x, y⟩, hxy⟩, rfl⟩ := ZFSet.mem_range.mp hentry
    exact hxy
  · intro hentry
    obtain ⟨x, hx, y, hy, rfl⟩ := (relationBetweenValue_set _ _ _).mp h.1 entry hentry
    exact ZFSet.mem_range.mpr ⟨⟨(⟨x, hx⟩, ⟨y, hy⟩), hentry⟩, rfl⟩

theorem graph_quantifier_iff (vertices : ZFSet.{0}) (P : ZFSet.{0} → Prop) :
    (∀ edges, graphValue setStructure vertices edges → P edges) ↔
      ∀ G : SimpleGraph (Members vertices), P (graphSet G) := by
  constructor
  · intro h G
    exact h _ (graphSet_spec G)
  · intro h edges hgraph
    simpa only [graphSet_graphOn] using h (graphOn vertices edges hgraph)

def finiteGraphIso {n : ℕ} (G : SimpleGraph (Fin n)) :
    graphOn (naturalSet n) (edgeSet G) (edgeSet_graph G) ≃g G where
  toEquiv := (finiteEquiv n).symm
  map_rel_iff' := by
    intro x y
    exact decodedGraph_adj G x y

theorem blueCopy_graphSet_iff {n : ℕ} (G : SimpleGraph (Fin n))
    {host : ZFSet.{0}} (H : SimpleGraph (Members host)) :
    blueCopyValue setStructure (naturalSet n) host (edgeSet G) (graphSet H) ↔ G ⊑ H := by
  rw [blueCopyValue_iff_isContained _ _ _ _ (edgeSet_graph G) (graphSet_spec H)]
  rw [graphOn_graphSet]
  exact SimpleGraph.isContained_congr_left (finiteGraphIso G)

end

end Erdos597Object.GraphEncoding
