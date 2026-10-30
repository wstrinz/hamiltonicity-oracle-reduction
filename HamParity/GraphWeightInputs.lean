module

public import HamParity.WeightedBucket
public import HamParity.CycleSelectionCompleteness

/-! Additive graph-integration draft; checked status requires final receipts. -/
@[expose] public section
namespace HamParity

def edgeWeightHeap {m : Nat} (weights : Fin m → Nat) : List (WeightedWire m) :=
  (List.finRange m).map (fun e => (weights e,e))

def edgeWeight {m : Nat} (weights : Fin m → Nat) (s : Assignment m) : Nat :=
  heapValue (edgeWeightHeap weights) s

theorem edgeWeightHeap_length {m : Nat} (weights : Fin m → Nat) :
    (edgeWeightHeap weights).length = m := by simp [edgeWeightHeap]

namespace IndexedGraph
variable {n m : Nat}

/-- Exactly one term per edge. Neither colors nor graph helpers are terms. -/
def graphWeightHeap (G : IndexedGraph n m) (weights : Fin m → Nat) :
    List (WeightedWire G.generalWires) :=
  renameHeap (fun e => G.generalCircuit.inputWire (Fin.castAdd n e)) (edgeWeightHeap weights)

theorem graphWeightHeap_length (G : IndexedGraph n m) (weights : Fin m → Nat) :
    (G.graphWeightHeap weights).length = m := by
  simp [graphWeightHeap, renameHeap, edgeWeightHeap_length]

theorem graphWeightHeap_mass (G : IndexedGraph n m) (weights : Fin m → Nat) :
    heapMass (G.graphWeightHeap weights) = heapMass (edgeWeightHeap weights) := by
  exact heapMass_rename _ _

theorem graphWeightHeap_eval (G : IndexedGraph n m) (weights : Fin m → Nat)
    (a : Assignment (m+n)) :
    heapValue (G.graphWeightHeap weights) (G.generalCircuit.eval a) =
      edgeWeight weights (leftAssignment a) := by
  rw [graphWeightHeap, heapValue_rename]
  simp only [Circuit.eval_inputWire, edgeWeight]
  rfl

theorem graphWeightHeap_join (G : IndexedGraph n m) (weights : Fin m → Nat)
    (s : Assignment m) (colors : Assignment n) :
    heapValue (G.graphWeightHeap weights) (G.generalCircuit.eval (joinAssignment s colors)) =
      edgeWeight weights s := by rw [G.graphWeightHeap_eval, left_join]

theorem graphWeightHeap_palette (G : IndexedGraph n m) (weights : Fin m → Nat)
    (d : Nat) (h : ∀ e, weights e < d) : ∀ z ∈ G.graphWeightHeap weights, z.1 < d := by
  intro z hz
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hz
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hy
  exact h e

end IndexedGraph
end HamParity
