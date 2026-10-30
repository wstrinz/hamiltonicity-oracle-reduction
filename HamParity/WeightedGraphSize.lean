module

public import HamParity.WeightedGraphCNF

@[expose] public section
namespace HamParity.IndexedGraph
variable {n m : Nat}

abbrev graphWeightSteps (G : IndexedGraph n m) (weights : Fin m → Nat) :=
  (normalizeHeap (G.graphWeightHeap weights)).steps
abbrev graphWeightWidth (G : IndexedGraph n m) (weights : Fin m → Nat) :=
  massWidth (heapMass (G.graphWeightHeap weights))

theorem graphWeightSteps_le (G : IndexedGraph n m) (weights : Fin m → Nat) :
    G.graphWeightSteps weights ≤ m := by
  have h := normalizeHeap_steps_le (G.graphWeightHeap weights)
  rwa [G.graphWeightHeap_length] at h

theorem graphWeightWidth_palette (G : IndexedGraph n m) (weights : Fin m → Nat)
    (d : Nat) (h : ∀ e, weights e<d) :
    G.graphWeightWidth weights ≤ d+(m+1).log2+1 := by
  have hw := heapWidth_palette_bound (G.graphWeightHeap weights) d (G.graphWeightHeap_palette weights d h)
  rwa [G.graphWeightHeap_length] at hw

theorem weightedGraph_variables (G : IndexedGraph n m) (weights : Fin m → Nat) :
    (G.graphArithmetic weights).wires =
      23*m+2*n+5*G.graphWeightSteps weights+2+5*G.graphWeightWidth weights := by
  have h := buildWeighted_variables (G.graphWeightHeap weights)
  have hg := G.generalCNF_variables
  change (G.graphArithmetic weights).wires =
    G.generalWires+5*G.graphWeightSteps weights+2+5*G.graphWeightWidth weights at h
  omega

theorem weightedGraph_helpers (G : IndexedGraph n m) (weights : Fin m → Nat) :
    (G.weightedGraphCircuit weights).gates =
      n+22*m+5*G.graphWeightSteps weights+2+5*G.graphWeightWidth weights := by
  rw [weightedGraphCircuit, Circuit.gates_compose, G.generalCNF_helpers, buildWeighted_gates]
  simp only [graphWeightSteps, graphWeightWidth, Nat.add_assoc]

theorem weightedGraphCNF_width (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) : WidthAtMost 3 (G.weightedGraphCNF root weights t) := by
  apply width_append (G.weightedGraphCircuit weights).width
  apply width_append
  · apply width_rename
    exact width_append (buildRows_constraints_width G.generalRows)
      (width_rename _ _ (rootedCutClauses_width _ _))
  · exact bucketPins_width _ _

theorem weightedGraphCNF_length (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    (G.weightedGraphCNF root weights t).length =
      (G.generalCNF root).length + (G.graphArithmetic weights).circuit.clauses.length +
        (bucketPins (G.graphArithmetic weights).output t).length := by
  simp only [weightedGraphCNF, weightedGraphCircuit, weightedGraphConstraints,
    generalCNF, batchCNF, Circuit.clauses_length_compose, List.length_append, length_rename,
    generalCircuit]
  omega

theorem weightedGraphCNF_clause_bound (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    (G.weightedGraphCNF root weights t).length ≤
      90*m+6*n+18*G.graphWeightSteps weights+19*G.graphWeightWidth weights+4 := by
  have hg := G.generalCNF_clause_bound root
  have ha := buildWeighted_clauses (G.graphWeightHeap weights)
  have hp := bucketPins_length_le (G.graphArithmetic weights).output t
    (by rw [buildWeighted_output_length]; omega)
  rw [buildWeighted_output_length] at hp
  rw [G.weightedGraphCNF_length]
  change (G.graphArithmetic weights).circuit.clauses.length =
    18*G.graphWeightSteps weights+2+18*G.graphWeightWidth weights at ha
  change (bucketPins (G.graphArithmetic weights).output t).length ≤ G.graphWeightWidth weights+1 at hp
  omega

theorem weightedGraph_palette_variables (G : IndexedGraph n m) (weights : Fin m → Nat)
    (d : Nat) (h : ∀ e, weights e<d) :
    (G.graphArithmetic weights).wires ≤ 28*m+2*n+2+5*(d+(m+1).log2+1) := by
  rw [G.weightedGraph_variables]
  have hs := G.graphWeightSteps_le weights
  have hw := G.graphWeightWidth_palette weights d h
  omega

theorem weightedGraph_palette_clauses (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t d : Nat) (h : ∀ e, weights e<d) :
    (G.weightedGraphCNF root weights t).length ≤
      108*m+6*n+19*(d+(m+1).log2+1)+4 := by
  have hc := G.weightedGraphCNF_clause_bound root weights t
  have hs := G.graphWeightSteps_le weights
  have hw := G.graphWeightWidth_palette weights d h
  omega

end HamParity.IndexedGraph
