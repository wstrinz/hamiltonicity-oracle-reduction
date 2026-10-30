module

public import HamParity.WeightedGraphMeaning
public import HamParity.GeneralGraphExamples

@[expose] public section
namespace HamParity.WeightedGraphExamples

theorem triangle_bucket_three :
    modelCount (SelectionExamples.triangle.weightedGraphCNF 0 (fun _ => 0) 3)=1 := by
  rw [IndexedGraph.weightedGraphCNF_count_primary]
  decide

theorem triangle_wrong_bucket :
    modelCount (SelectionExamples.triangle.weightedGraphCNF 0 (fun _ => 0) 2)=0 := by
  rw [IndexedGraph.weightedGraphCNF_count_primary]
  decide

theorem triangle_nonuniform_weights :
    modelCount (SelectionExamples.triangle.weightedGraphCNF 0 (fun e => e.val) 7)=1 := by
  rw [IndexedGraph.weightedGraphCNF_count_primary]
  decide

theorem missing_degree_rejected :
    modelCount (SelectionExamples.oneEdge.weightedGraphCNF 0 (fun _ => 0) 1)=0 := by
  rw [IndexedGraph.weightedGraphCNF_count_primary]
  decide

/-- Non-simple inputs are counted but never given a Hamiltonian interpretation. -/
theorem loop_incidence_count :
    modelCount (SelectionExamples.oneLoop.weightedGraphCNF 0 (fun _ => 0) 1)=1 := by
  rw [IndexedGraph.weightedGraphCNF_count_primary]
  decide

theorem disconnected_colors_retained :
    SelectionExamples.twoTriangles.weightedGraphFiber 0 (fun _ => 0) 6 (fun _ => true)=2 := by
  rw [IndexedGraph.weightedGraphFiber_eq, IndexedGraph.generalFiber_count]
  decide

theorem disconnected_wrong_bucket :
    SelectionExamples.twoTriangles.weightedGraphFiber 0 (fun _ => 0) 5 (fun _ => true)=0 := by
  rw [IndexedGraph.weightedGraphFiber_eq]
  have h : edgeWeight (m := 6) (fun _ => 0) (fun _ => true) ≠ 5 := by decide
  simp [h]

set_option maxRecDepth 16384 in
theorem degree_four_input_count :
    modelCount (GeneralGraphExamples.highDegreeCycle.weightedGraphCNF 0 (fun _ => 0) 5)=1 := by
  rw [IndexedGraph.weightedGraphCNF_count_primary]
  decide

def edgeless : IndexedGraph 1 0 := ⟨Fin.elim0⟩

theorem edgeless_rejected : modelCount (edgeless.weightedGraphCNF 0 Fin.elim0 0)=0 := by
  rw [IndexedGraph.weightedGraphCNF_count_primary]
  decide

end HamParity.WeightedGraphExamples
