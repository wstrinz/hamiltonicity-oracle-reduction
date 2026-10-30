module

public import HamParity.GeneralGraphParity

@[expose] public section

namespace HamParity.GeneralGraphExamples

theorem overlapping_rows_count :
    modelCount (batchCNF ([[0,1,2,3], [0,1]] : List (List (Fin 4))) []) = 1 := by
  rw [batchCNF_count]
  decide

theorem repeated_rows_count :
    modelCount (batchCNF ([[0,1], [0,1]] : List (List (Fin 2))) []) = 1 := by
  rw [batchCNF_count]
  decide

theorem empty_batch_counts_unused_primary_bits :
    modelCount (batchCNF ([] : List (List (Fin 2))) []) = 4 := by
  rw [batchCNF_count]
  decide

def highDegreeCycle : IndexedGraph 5 7 := ⟨fun e =>
  match e.val with
  | 0 => (0,1) | 1 => (1,2) | 2 => (2,3) | 3 => (3,4)
  | 4 => (4,0) | 5 => (0,2) | _ => (0,3)⟩

def fourStar : IndexedGraph 5 4 := ⟨fun e => (0, e.succ)⟩

theorem highDegree_not_subcubic : ¬highDegreeCycle.Subcubic := by
  intro h
  have hv := h 0
  have he : (highDegreeCycle.incidences 0).length = 4 := by decide
  rw [he] at hv
  omega

theorem highDegree_simple : highDegreeCycle.Simple := by
  unfold IndexedGraph.Simple EdgeGraph.Simple
  decide

set_option maxRecDepth 16384 in
theorem highDegree_count : modelCount (highDegreeCycle.generalCNF 0) = 1 := by
  rw [IndexedGraph.generalCNF_count_primary]
  decide

theorem highDegree_has_cyclicOrder : Nonempty highDegreeCycle.inputGraph.CyclicOrder := by
  apply highDegreeCycle.odd_generalCNF_input_cyclicOrder highDegree_simple 0
  rw [highDegree_count]

theorem highDegree_declared_variables : highDegreeCycle.generalWires = 171 := by
  rw [IndexedGraph.generalCNF_variables]

set_option maxRecDepth 8192 in
theorem fourStar_count : modelCount (fourStar.generalCNF 0) = 0 := by
  rw [IndexedGraph.generalCNF_count_primary]
  decide

theorem agrees_with_subcubic {n m : Nat} (G : IndexedGraph n m) (hs : G.Subcubic)
    (root : Fin n) : modelCount (G.generalCNF root) = modelCount (G.selectionCNF root) := by
  rw [G.generalCNF_exact_count, G.selectionCNF_exact_count hs]

theorem triangle_count_preserved :
    modelCount (SelectionExamples.triangle.generalCNF 0) = 1 := by
  rw [agrees_with_subcubic _ SelectionExamples.triangle_subcubic,
    SelectionExamples.triangle_count]

end HamParity.GeneralGraphExamples
