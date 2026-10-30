module

public import HamParity.IncidenceSize

@[expose] public section

namespace HamParity.IndexedGraph

variable {n m : Nat}

abbrev generalWires (G : IndexedGraph n m) : Nat := (buildRows G.generalRows).wires

def generalCircuit (G : IndexedGraph n m) : Circuit (m+n) G.generalWires :=
  (buildRows G.generalRows).circuit

/-- Shared m edge bits and n counted colors; fresh deterministic row helpers. -/
def generalCNF (G : IndexedGraph n m) (root : Fin n) : CNF G.generalWires :=
  batchCNF G.generalRows (G.selectionCutCNF root)

def generalPrimaryValid (G : IndexedGraph n m) (root : Fin n)
    (x : Assignment (m+n)) : Bool :=
  rowsValid G.generalRows x && (G.selectionCutCNF root).eval x

theorem generalPrimaryValid_join (G : IndexedGraph n m) (root : Fin n)
    (s : Assignment m) (a : Assignment n) :
    G.generalPrimaryValid root (joinAssignment s a) =
      (G.degreeTwoB s && (G.selectedGraph s).rootedValidB root a) := by
  rw [generalPrimaryValid, G.generalRows_valid, G.selectionCutCNF_eval]

theorem generalCNF_count_primary (G : IndexedGraph n m) (root : Fin n) :
    modelCount (G.generalCNF root) =
      (assignments (m+n)).countP (G.generalPrimaryValid root) := by
  exact batchCNF_count G.generalRows (G.selectionCutCNF root)

theorem generalCNF_satisfies_iff (G : IndexedGraph n m) (root : Fin n)
    (a : Assignment G.generalWires) :
    (G.generalCNF root).eval a = true ↔
      a = G.generalCircuit.eval (G.generalCircuit.inputs a) ∧
      G.generalPrimaryValid root (G.generalCircuit.inputs a) = true := by
  unfold generalCNF generalCircuit generalPrimaryValid
  rw [Bool.and_eq_true]
  exact batchCNF_satisfies_iff G.generalRows (G.selectionCutCNF root) a

theorem generalCNF_unique_extension (G : IndexedGraph n m) (root : Fin n)
    (s : Assignment m) (colors : Assignment n) (hd : G.degreeTwoB s = true)
    (hc : (G.selectedGraph s).rootedValidB root colors = true) :
    ∃ a : Assignment G.generalWires,
      (G.generalCNF root).eval a = true ∧
      G.generalCircuit.inputs a = joinAssignment s colors ∧
      ∀ b, (G.generalCNF root).eval b = true →
        G.generalCircuit.inputs b = joinAssignment s colors → b = a := by
  exact batchCNF_unique_extension G.generalRows (G.selectionCutCNF root)
    (joinAssignment s colors) (by rwa [G.generalRows_valid])
    (by rwa [G.selectionCutCNF_eval])

theorem generalCNF_width (G : IndexedGraph n m) (root : Fin n) :
    WidthAtMost 3 (G.generalCNF root) :=
  batchCNF_width _ _ (rootedCutClauses_width _ _)

/-- No bounded-degree or sparsity premise: sizes are linear in n+m. -/
theorem generalCNF_variables (G : IndexedGraph n m) : G.generalWires = 23*m + 2*n := by
  have h := buildRows_variables G.generalRows
  rw [G.generalRows_length, G.generalRows_size] at h
  change (buildRows G.generalRows).wires = _
  omega

theorem generalCNF_clause_bound (G : IndexedGraph n m) (root : Fin n) :
    (G.generalCNF root).length ≤ 90*m + 6*n + 1 := by
  have h := batchCNF_clause_bound G.generalRows (G.selectionCutCNF root)
  rw [G.generalRows_length, G.generalRows_size, G.selectionCutCNF_length] at h
  change (batchCNF G.generalRows (G.selectionCutCNF root)).length ≤ _
  omega

theorem generalCNF_helpers (G : IndexedGraph n m) :
    G.generalCircuit.gates = n + 22*m := by
  have h := buildRows_gates G.generalRows
  rw [G.generalRows_length, G.generalRows_size] at h
  change (buildRows G.generalRows).circuit.gates = _
  omega

end HamParity.IndexedGraph
