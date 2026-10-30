module

public import HamParity.WeightedGraphCounting

@[expose] public section
namespace HamParity.IndexedGraph
variable {n m : Nat}

theorem odd_weightedGraphFiber (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) (s : Assignment m)
    (h : G.weightedGraphFiber root weights t s % 2=1) :
    edgeWeight weights s=t ∧ G.degreeTwoB s=true ∧ ∀ u v, (G.selectedGraph s).Reach u v := by
  rw [G.weightedGraphFiber_eq] at h
  by_cases ht : edgeWeight weights s=t
  · have hg : G.generalFiber root s % 2=1 := by simpa [ht] using h
    exact ⟨ht,G.odd_generalFiber root s hg⟩
  · simp [ht] at h

theorem odd_weightedGraphCNF_cyclicOrder (G : IndexedGraph n m) (hs : G.Simple)
    (root : Fin n) (weights : Fin m → Nat) (t : Nat)
    (h : modelCount (G.weightedGraphCNF root weights t) % 2=1) :
    ∃ s : Assignment m, edgeWeight weights s=t ∧ Nonempty (G.selectedGraph s).CyclicOrder := by
  rw [G.weightedGraphCNF_sum_fibers] at h
  obtain ⟨s,_,ho⟩ := exists_odd_of_sum_odd (assignments m) (G.weightedGraphFiber root weights t) h
  obtain ⟨ht,hd,hc⟩ := G.odd_weightedGraphFiber root weights t s ho
  have hd' : ∀ v, (G.selectedGraph s).incidenceDegree v=2 := by
    intro v
    rw [← G.selectedDegree_eq_graph_degree s v]
    exact (G.degreeTwoB_iff s).mp hd v
  exact ⟨s,ht,(G.selectedGraph s).cyclicOrder_of_connected_degree_two (G.selected_simple hs s) root hd' hc⟩

theorem odd_weightedGraphCNF_input_cyclicOrder (G : IndexedGraph n m) (hs : G.Simple)
    (root : Fin n) (weights : Fin m → Nat) (t : Nat)
    (h : modelCount (G.weightedGraphCNF root weights t) % 2=1) :
    Nonempty G.inputGraph.CyclicOrder := by
  obtain ⟨s,_,⟨C⟩⟩ := G.odd_weightedGraphCNF_cyclicOrder hs root weights t h
  exact G.selectedCyclicOrder_input s C

/-- Witness-specific completeness at the witness's own weight, not an odd-count
claim for the total sum over all witnesses in that bucket. -/
theorem input_cycle_weightedGraphCNF_unique_extension (G : IndexedGraph n m) (hs : G.Simple)
    (root : Fin n) (weights : Fin m → Nat) (C : G.inputGraph.CyclicOrder) :
    ∃ a : Assignment (G.graphArithmetic weights).wires,
      (G.weightedGraphCNF root weights (edgeWeight weights (G.cycleSelection C))).eval a=true ∧
      (G.weightedGraphCircuit weights).inputs a=joinAssignment (G.cycleSelection C) (fun _ => false) ∧
      ∀ b, (G.weightedGraphCNF root weights (edgeWeight weights (G.cycleSelection C))).eval b=true →
        (G.weightedGraphCircuit weights).inputs b=joinAssignment (G.cycleSelection C) (fun _ => false) → b=a := by
  apply G.weightedGraphCNF_unique_extension root weights _ (G.cycleSelection C) (fun _ => false)
    (G.cycleSelection_degreeTwoB C hs)
  · rw [EdgeGraph.rootedValidB_iff]
    exact ⟨rfl,fun _ _ => rfl⟩
  · rfl

theorem input_cycle_weightedGraphFiber_one (G : IndexedGraph n m) (hs : G.Simple)
    (root : Fin n) (weights : Fin m → Nat) (C : G.inputGraph.CyclicOrder) :
    G.weightedGraphFiber root weights (edgeWeight weights (G.cycleSelection C)) (G.cycleSelection C)=1 := by
  rw [G.weightedGraphFiber_eq, if_pos rfl]
  exact G.input_cycle_generalFiber_one hs root C

end HamParity.IndexedGraph
