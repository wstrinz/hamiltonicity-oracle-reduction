module

public import HamParity.WeightedGraphSize

@[expose] public section
namespace HamParity.IndexedGraph
variable {n m : Nat}

def weightedGraphFiber (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) (s : Assignment m) : Nat :=
  (assignments n).countP (fun colors => (G.weightedGraphCNF root weights t).eval
    ((G.weightedGraphCircuit weights).eval (joinAssignment s colors)))

/-- The arithmetic predicate is constant across the whole counted color fiber. -/
theorem weightedGraphFiber_eq (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) (s : Assignment m) :
    G.weightedGraphFiber root weights t s =
      if edgeWeight weights s=t then G.generalFiber root s else 0 := by
  unfold weightedGraphFiber generalFiber
  simp only [G.weightedGraphCNF_eval_extension, G.generalCNF_eval_extension,
    weightedGraphValid, left_join]
  by_cases ht : edgeWeight weights s=t <;> simp [ht]

theorem weightedGraphFiber_power (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) (s : Assignment m) :
    G.weightedGraphFiber root weights t s =
      if G.degreeTwoB s && decide (edgeWeight weights s=t)
      then 2^((G.selectedGraph s).componentCount-1) else 0 := by
  rw [G.weightedGraphFiber_eq, G.generalFiber_power]
  by_cases ht : edgeWeight weights s=t <;> cases hd : G.degreeTwoB s <;> simp [ht,hd]

theorem weightedGraphCNF_sum_fibers (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    modelCount (G.weightedGraphCNF root weights t) =
      ((assignments m).map (G.weightedGraphFiber root weights t)).sum := by
  rw [G.weightedGraphCNF_count_primary]
  unfold weightedGraphFiber
  simp only [G.weightedGraphCNF_eval_extension]
  exact count_split_assignments (G.weightedGraphValid root weights t)

theorem weightedGraphCNF_exact_count (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    modelCount (G.weightedGraphCNF root weights t) =
      ((assignments m).map (fun s =>
        if G.degreeTwoB s && decide (edgeWeight weights s=t)
        then 2^((G.selectedGraph s).componentCount-1) else 0)).sum := by
  rw [G.weightedGraphCNF_sum_fibers]
  apply congrArg List.sum
  apply congrArg (fun f => (assignments m).map f)
  funext s
  exact G.weightedGraphFiber_power root weights t s

theorem weightedGraphFiber_mod_two (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) (s : Assignment m) :
    G.weightedGraphFiber root weights t s % 2 =
      if G.connectedDegreeTwoB s && decide (edgeWeight weights s=t) then 1 else 0 := by
  rw [G.weightedGraphFiber_eq]
  by_cases ht : edgeWeight weights s=t
  · simp only [ht, ite_true, decide_true, Bool.and_true]
    exact G.generalFiber_mod_two root s
  · simp [ht]

theorem weightedGraphCNF_parity (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    modelCount (G.weightedGraphCNF root weights t) % 2 =
      (assignments m).countP (fun s => G.connectedDegreeTwoB s && decide (edgeWeight weights s=t)) % 2 := by
  rw [G.weightedGraphCNF_sum_fibers]
  exact sum_mod_two_eq_countP (assignments m) (G.weightedGraphFiber root weights t)
    (fun s => G.connectedDegreeTwoB s && decide (edgeWeight weights s=t))
    (G.weightedGraphFiber_mod_two root weights t)

theorem weightedGraphCNF_cyclic_parity (G : IndexedGraph n m) (hs : G.Simple) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    modelCount (G.weightedGraphCNF root weights t) % 2 =
      (assignments m).countP (fun s => G.cyclicSelectionB s && decide (edgeWeight weights s=t)) % 2 := by
  rw [G.weightedGraphCNF_parity]
  congr 1
  apply List.countP_congr
  intro s _
  rw [G.connectedDegreeTwoB_eq_cyclicSelectionB hs root s]

end HamParity.IndexedGraph
