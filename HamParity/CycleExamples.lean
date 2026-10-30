module

public import HamParity.CycleOrder

@[expose] public section

namespace HamParity.CycleExamples

open SelectionExamples

theorem triangle_simple : triangle.Simple := by
  unfold IndexedGraph.Simple EdgeGraph.Simple
  decide

theorem loop_not_simple : ¬oneLoop.Simple := by
  unfold IndexedGraph.Simple EdgeGraph.Simple
  decide

theorem parallel_not_simple : ¬parallelPair.Simple := by
  unfold IndexedGraph.Simple EdgeGraph.Simple
  decide

theorem triangle_cyclicOrder : Nonempty triangle.inputGraph.CyclicOrder := by
  apply triangle.odd_selectionCNF_input_cyclicOrder triangle_subcubic triangle_simple 0
  rw [triangle_count]

theorem triangle_order_length (C : triangle.inputGraph.CyclicOrder) :
    C.vertices.length = 3 := C.length_eq

end HamParity.CycleExamples
