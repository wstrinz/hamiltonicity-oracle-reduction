module

public import HamParity.SelectionParity
public import HamParity.SelectionGraphMeaning

@[expose] public section

namespace HamParity.SelectionExamples

def triangle : IndexedGraph 3 3 := ⟨fun e =>
  match e.val with | 0 => (0, 1) | 1 => (1, 2) | _ => (2, 0)⟩

def oneEdge : IndexedGraph 2 1 := ⟨fun _ => (0, 1)⟩

def oneLoop : IndexedGraph 1 1 := ⟨fun _ => (0, 0)⟩

def parallelPair : IndexedGraph 2 2 := ⟨fun _ => (0, 1)⟩

def twoTriangles : IndexedGraph 6 6 := ⟨fun e =>
  match e.val with
  | 0 => (0, 1) | 1 => (1, 2) | 2 => (2, 0)
  | 3 => (3, 4) | 4 => (4, 5) | _ => (5, 3)⟩

theorem triangle_subcubic : triangle.Subcubic := by
  unfold IndexedGraph.Subcubic
  decide
theorem twoTriangles_subcubic : twoTriangles.Subcubic := by
  unfold IndexedGraph.Subcubic
  decide

theorem triangle_count : modelCount (triangle.selectionCNF 0) = 1 := by decide

theorem missing_degree_rejected : modelCount (oneEdge.selectionCNF 0) = 0 := by decide

/- These two examples expose the multigraph/small-order scope. They must not be
reported as a Hamiltonian-cycle theorem under a simple-graph n>=3 convention. -/
theorem loop_incidence_count : modelCount (oneLoop.selectionCNF 0) = 1 := by decide
theorem parallel_edge_count : modelCount (parallelPair.selectionCNF 0) = 1 := by decide

theorem disconnected_cycle_cover_fiber :
    twoTriangles.selectionFiber 0 (fun _ => true) = 2 := by
  rw [twoTriangles.selectionFiber_count twoTriangles_subcubic]
  decide

theorem unselected_triangle_rejected : triangle.selectionFiber 0 (fun _ => false) = 0 := by
  rw [triangle.selectionFiber_count triangle_subcubic]
  decide

end HamParity.SelectionExamples
