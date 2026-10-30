module

public import HamParity.CycleSelection

@[expose] public section

namespace HamParity.IndexedGraph

variable {n m : Nat} (G : IndexedGraph n m)

/-- The missing graph bridge, in both directions. This is a statement about a
connected selected witness, not parity of the unfiltered sum over witnesses. -/
theorem input_cyclicOrder_iff_connected_degree_two_selection (hs : G.Simple)
    (root : Fin n) :
    Nonempty G.inputGraph.CyclicOrder ↔
      ∃ s : Assignment m, G.degreeTwoB s = true ∧
        ∀ u v, (G.selectedGraph s).Reach u v := by
  constructor
  · rintro ⟨C⟩
    exact ⟨G.cycleSelection C, G.cycleSelection_degreeTwoB C hs,
      G.cycleSelection_connected C⟩
  · rintro ⟨s, hd, hc⟩
    have hd' : ∀ v, (G.selectedGraph s).incidenceDegree v = 2 := by
      intro v
      rw [← G.selectedDegree_eq_graph_degree]
      exact (G.degreeTwoB_iff s).mp hd v
    obtain ⟨C⟩ := (G.selectedGraph s).cyclicOrder_of_connected_degree_two
      (G.selected_simple hs s) root hd' hc
    exact G.selectedCyclicOrder_input s C

/-- The actual emitted CNF accepts a cycle's selected edges and all-false rooted
colors with exactly one deterministic helper extension. No desired bijection or
count is assumed; degree-two selection was constructed from the input order. -/
theorem input_cycle_generalCNF_unique_extension (hs : G.Simple) (root : Fin n)
    (C : G.inputGraph.CyclicOrder) :
    ∃ a : Assignment G.generalWires,
      (G.generalCNF root).eval a = true ∧
      G.generalCircuit.inputs a = joinAssignment (G.cycleSelection C) (fun _ => false) ∧
      ∀ b, (G.generalCNF root).eval b = true →
        G.generalCircuit.inputs b = joinAssignment (G.cycleSelection C) (fun _ => false) →
        b = a := by
  apply G.generalCNF_unique_extension root (G.cycleSelection C) (fun _ => false)
    (G.cycleSelection_degreeTwoB C hs)
  rw [EdgeGraph.rootedValidB_iff]
  exact ⟨rfl, fun _ _ => rfl⟩

/-- A single extracted cycle contributes one model after deterministic helper
elimination. The total formula sums over all edge selections and can be even. -/
theorem input_cycle_generalFiber_one (hs : G.Simple) (root : Fin n)
    (C : G.inputGraph.CyclicOrder) :
    G.generalFiber root (G.cycleSelection C) = 1 := by
  rw [G.generalFiber_count, G.cycleSelection_degreeTwoB C hs]
  exact (G.selectedGraph (G.cycleSelection C)).rooted_color_count_connected root
    (G.cycleSelection_connected C)

/-- The cycle convention requires at least three distinct vertices. -/
theorem no_input_cyclicOrder_small (hn : n < 3) : ¬Nonempty G.inputGraph.CyclicOrder := by
  rintro ⟨C⟩
  have := C.n_at_least_three
  omega

end HamParity.IndexedGraph
