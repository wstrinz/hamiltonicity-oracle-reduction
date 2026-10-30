module

public import HamParity.GeneralGraphCounting

@[expose] public section

namespace HamParity.IndexedGraph

variable {n m : Nat}

theorem generalFiber_mod_two (G : IndexedGraph n m) (root : Fin n) (s : Assignment m) :
    G.generalFiber root s % 2 = if G.connectedDegreeTwoB s then 1 else 0 := by
  classical
  rw [G.generalFiber_count]
  by_cases hd : G.degreeTwoB s = true
  · by_cases hc : ∀ u v, (G.selectedGraph s).Reach u v
    · have hb : (G.selectedGraph s).connectedB = true :=
        (EdgeGraph.connectedB_iff _).mpr hc
      simp [hd, connectedDegreeTwoB, hb,
        EdgeGraph.rooted_color_count_connected _ root hc]
    · have hb : (G.selectedGraph s).connectedB = false := by
        simp [EdgeGraph.connectedB, hc]
      obtain ⟨u, hu⟩ := Classical.not_forall.mp hc
      obtain ⟨v, hv⟩ := Classical.not_forall.mp hu
      have hz := (G.selectedGraph s).colorCNF_disconnected_even_all_graphs root ⟨u, v, hv⟩
      rw [EdgeGraph.colorCNF_count] at hz
      simp [hd, connectedDegreeTwoB, hb, hz]
  · simp [hd, connectedDegreeTwoB]

theorem generalCNF_parity (G : IndexedGraph n m) (root : Fin n) :
    modelCount (G.generalCNF root) % 2 =
      (assignments m).countP G.connectedDegreeTwoB % 2 := by
  rw [G.generalCNF_sum_fibers]
  exact sum_mod_two_eq_countP (assignments m) (G.generalFiber root)
    G.connectedDegreeTwoB (G.generalFiber_mod_two root)

theorem generalCNF_cyclic_parity (G : IndexedGraph n m) (hs : G.Simple) (root : Fin n) :
    modelCount (G.generalCNF root) % 2 =
      (assignments m).countP G.cyclicSelectionB % 2 := by
  rw [G.generalCNF_parity]
  congr 1
  apply List.countP_congr
  intro s _
  rw [G.connectedDegreeTwoB_eq_cyclicSelectionB hs root s]

theorem odd_generalCNF_cyclicOrder (G : IndexedGraph n m) (hs : G.Simple) (root : Fin n)
    (hodd : modelCount (G.generalCNF root) % 2 = 1) :
    ∃ s : Assignment m, Nonempty (G.selectedGraph s).CyclicOrder := by
  obtain ⟨s, hd, hc⟩ := G.odd_generalCNF_connected_degree_two root hodd
  have hd' : ∀ v, (G.selectedGraph s).incidenceDegree v = 2 := by
    intro v
    rw [← G.selectedDegree_eq_graph_degree s v]
    exact hd v
  exact ⟨s, (G.selectedGraph s).cyclicOrder_of_connected_degree_two
    (G.selected_simple hs s) root hd' hc⟩

theorem selectedCyclicOrder_input (G : IndexedGraph n m) (s : Assignment m)
    (C : (G.selectedGraph s).CyclicOrder) : Nonempty G.inputGraph.CyclicOrder := by
  refine ⟨⟨C.vertices, C.nodup, C.covers, C.length_at_least_three, ?_, ?_⟩⟩
  · have hmono : ∀ xs, CyclePaths.Chain (G.selectedGraph s).Adj xs →
        CyclePaths.Chain G.inputGraph.Adj xs := by
      intro xs hx
      induction xs with
      | nil => trivial
      | cons a xs ih =>
          cases xs with
          | nil => trivial
          | cons b ys => exact ⟨G.selected_adj_input s hx.1, ih hx.2⟩
    exact hmono _ C.chain
  · intro a b ha hb
    exact G.selected_adj_input s (C.closes a b ha hb)

/-- Soundness for arbitrary simple indexed inputs, without a degree cap. -/
theorem odd_generalCNF_input_cyclicOrder (G : IndexedGraph n m) (hs : G.Simple)
    (root : Fin n) (hodd : modelCount (G.generalCNF root) % 2 = 1) :
    Nonempty G.inputGraph.CyclicOrder := by
  obtain ⟨s, ⟨C⟩⟩ := G.odd_generalCNF_cyclicOrder hs root hodd
  exact G.selectedCyclicOrder_input s C

theorem generalCNF_sparse_variables (G : IndexedGraph n m) (d : Nat) (hm : m ≤ d*n) :
    G.generalWires ≤ (23*d + 2)*n := by
  rw [G.generalCNF_variables]
  calc
    23*m + 2*n ≤ 23*(d*n) + 2*n := Nat.add_le_add_right (Nat.mul_le_mul_left 23 hm) _
    _ = (23*d + 2)*n := by simp [Nat.add_mul, Nat.mul_assoc]

theorem generalCNF_sparse_clauses (G : IndexedGraph n m) (root : Fin n)
    (d : Nat) (hm : m ≤ d*n) : (G.generalCNF root).length ≤ (90*d + 6)*n + 1 := by
  calc
    (G.generalCNF root).length ≤ 90*m + 6*n + 1 := G.generalCNF_clause_bound root
    _ ≤ 90*(d*n) + 6*n + 1 := by have := Nat.mul_le_mul_left 90 hm; omega
    _ = (90*d + 6)*n + 1 := by simp [Nat.add_mul, Nat.mul_assoc]

end HamParity.IndexedGraph
