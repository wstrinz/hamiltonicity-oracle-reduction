module

public import HamParity.GeneralGraphCNF

@[expose] public section

namespace HamParity.IndexedGraph

variable {n m : Nat}

theorem generalCNF_eval_extension (G : IndexedGraph n m) (root : Fin n)
    (x : Assignment (m+n)) :
    (G.generalCNF root).eval (G.generalCircuit.eval x) = G.generalPrimaryValid root x := by
  simp only [generalCNF, generalCircuit, batchCNF, eval_append, Circuit.eval_satisfies,
    Bool.true_and, batchConstraints_eval, generalPrimaryValid]

/-- Colors are counted, but helpers are the uniquely determined circuit extension. -/
def generalFiber (G : IndexedGraph n m) (root : Fin n) (s : Assignment m) : Nat :=
  (assignments n).countP (fun colors =>
    (G.generalCNF root).eval (G.generalCircuit.eval (joinAssignment s colors)))

theorem generalFiber_count (G : IndexedGraph n m) (root : Fin n) (s : Assignment m) :
    G.generalFiber root s =
      if G.degreeTwoB s then (assignments n).countP ((G.selectedGraph s).rootedValidB root)
      else 0 := by
  unfold generalFiber
  simp only [G.generalCNF_eval_extension, G.generalPrimaryValid_join]
  cases hd : G.degreeTwoB s <;> simp

theorem generalFiber_power (G : IndexedGraph n m) (root : Fin n) (s : Assignment m) :
    G.generalFiber root s =
      if G.degreeTwoB s then 2 ^ ((G.selectedGraph s).componentCount - 1) else 0 := by
  rw [G.generalFiber_count, EdgeGraph.rooted_color_count_all_graphs]

theorem generalCNF_sum_fibers (G : IndexedGraph n m) (root : Fin n) :
    modelCount (G.generalCNF root) =
      ((assignments m).map (G.generalFiber root)).sum := by
  rw [G.generalCNF_count_primary]
  unfold generalFiber
  simp only [G.generalCNF_eval_extension]
  exact count_split_assignments (G.generalPrimaryValid root)

/-- End-to-end exact count for the emitted CNF: no subcubic assumption. -/
theorem generalCNF_exact_count (G : IndexedGraph n m) (root : Fin n) :
    modelCount (G.generalCNF root) =
      ((assignments m).map (fun s =>
        if G.degreeTwoB s then 2 ^ ((G.selectedGraph s).componentCount - 1) else 0)).sum := by
  rw [G.generalCNF_sum_fibers]
  apply congrArg List.sum
  apply congrArg (fun f => (assignments m).map f)
  funext s
  exact G.generalFiber_power root s

theorem odd_generalFiber (G : IndexedGraph n m) (root : Fin n) (s : Assignment m)
    (h : G.generalFiber root s % 2 = 1) :
    G.degreeTwoB s = true ∧ ∀ u v, (G.selectedGraph s).Reach u v := by
  rw [G.generalFiber_count] at h
  by_cases hd : G.degreeTwoB s = true
  · refine ⟨hd, ?_⟩
    have hc : modelCount ((G.selectedGraph s).colorCNF root) % 2 = 1 := by
      rw [EdgeGraph.colorCNF_count]
      simpa [hd] using h
    exact (G.selectedGraph s).colorCNF_odd_connected_all_graphs root hc
  · simp [hd] at h

theorem odd_generalCNF_connected_degree_two (G : IndexedGraph n m) (root : Fin n)
    (h : modelCount (G.generalCNF root) % 2 = 1) :
    ∃ s : Assignment m, (∀ v, G.selectedDegree s v = 2) ∧
      ∀ u v, (G.selectedGraph s).Reach u v := by
  rw [G.generalCNF_sum_fibers] at h
  obtain ⟨s, _, hs⟩ := exists_odd_of_sum_odd (assignments m) (G.generalFiber root) h
  obtain ⟨hd, hc⟩ := G.odd_generalFiber root s hs
  exact ⟨s, (G.degreeTwoB_iff s).mp hd, hc⟩

end HamParity.IndexedGraph
