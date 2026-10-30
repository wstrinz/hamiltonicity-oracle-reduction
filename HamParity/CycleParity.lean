module

public import HamParity.CycleOrder

@[expose] public section

namespace HamParity.IndexedGraph

variable {n m : Nat}

/-- Counts edge selections, not cyclic orderings/orientations of a selected cycle. -/
noncomputable def cyclicSelectionB (G : IndexedGraph n m) (s : Assignment m) : Bool := by
  classical
  exact G.degreeTwoB s && decide (Nonempty (G.selectedGraph s).CyclicOrder)

theorem cyclicSelectionB_iff (G : IndexedGraph n m) (s : Assignment m) :
    G.cyclicSelectionB s = true ↔
      (∀ v, G.selectedDegree s v = 2) ∧ Nonempty (G.selectedGraph s).CyclicOrder := by
  classical
  simp [cyclicSelectionB, G.degreeTwoB_iff]

theorem connectedDegreeTwoB_eq_cyclicSelectionB (G : IndexedGraph n m)
    (hs : G.Simple) (root : Fin n) (s : Assignment m) :
    G.connectedDegreeTwoB s = G.cyclicSelectionB s := by
  apply Bool.eq_iff_iff.mpr
  rw [G.connectedDegreeTwoB_iff, G.cyclicSelectionB_iff]
  constructor
  · rintro ⟨hd, hc⟩
    have hd' : ∀ v, (G.selectedGraph s).incidenceDegree v = 2 := by
      intro v
      rw [← G.selectedDegree_eq_graph_degree s v]
      exact hd v
    exact ⟨hd, (G.selectedGraph s).cyclicOrder_of_connected_degree_two
      (G.selected_simple hs s) root hd' hc⟩
  · rintro ⟨hd, ⟨C⟩⟩
    exact ⟨hd, C.connected⟩

theorem selectionCNF_cyclic_parity (G : IndexedGraph n m)
    (hsub : G.Subcubic) (hs : G.Simple) (root : Fin n) :
    modelCount (G.selectionCNF root) % 2 =
      (assignments m).countP G.cyclicSelectionB % 2 := by
  rw [G.selectionCNF_parity hsub root]
  congr 1
  apply List.countP_congr
  intro s _
  rw [G.connectedDegreeTwoB_eq_cyclicSelectionB hs root s]

end HamParity.IndexedGraph
