module

public import HamParity.BatchWires

@[expose] public section

namespace HamParity

structure BatchState (n : Nat) where
  wires : Nat
  circuit : Circuit n wires
  constraints : CNF wires

namespace BatchState

def empty (n : Nat) : BatchState n := ⟨n, .nil, []⟩

abbrev rowCounter {n : Nat} (s : BatchState n) (row : List (Fin n)) : CounterState s.wires :=
  buildCounter (row.map s.circuit.inputWire)

def addRow {n : Nat} (s : BatchState n) (row : List (Fin n)) : BatchState n :=
  let p := s.rowCounter row
  ⟨p.wires, s.circuit.compose p.circuit,
    s.constraints.rename p.circuit.inputWire ++
      counterConstraints (row.map s.circuit.inputWire)⟩

/-- Every old wire (including all previous helpers) is injected into the new
row's input block and disjoint from every newly allocated helper. -/
theorem addRow_old_new_disjoint {n : Nat} (s : BatchState n) (row : List (Fin n)) :
    ∀ i j, (s.rowCounter row).circuit.inputWire i ≠
      (s.rowCounter row).circuit.helperWire j :=
  (s.rowCounter row).circuit.input_helper_disjoint

theorem addRow_eval {n : Nat} (s : BatchState n) (row : List (Fin n)) (a : Assignment n) :
    (s.addRow row).constraints.eval ((s.addRow row).circuit.eval a) =
      (s.constraints.eval (s.circuit.eval a) && (row.countP a == 2)) := by
  simp only [addRow, rowCounter, Circuit.eval_compose, eval_append, eval_rename,
    Circuit.eval_inputWire, counterConstraints_eval, List.countP_map, Function.comp_def]

theorem addRow_gates {n : Nat} (s : BatchState n) (row : List (Fin n)) :
    (s.addRow row).circuit.gates = s.circuit.gates + (1 + 11 * row.length) := by
  simp [addRow, rowCounter, Circuit.gates_compose, buildCounter_gates]

theorem addRow_constraints_length {n : Nat} (s : BatchState n) (row : List (Fin n)) :
    (s.addRow row).constraints.length = s.constraints.length + 2 := by
  simp [addRow, counterConstraints]

theorem addRow_width {n : Nat} (s : BatchState n) (row : List (Fin n))
    (hq : WidthAtMost 3 s.constraints) : WidthAtMost 3 (s.addRow row).constraints := by
  apply width_append (width_rename _ _ hq)
  intro c hc
  exact exactTwoCounterCNF_width _ c (List.mem_append.mpr (Or.inr hc))

end BatchState

def buildRows {n : Nat} : List (List (Fin n)) → BatchState n
  | [] => .empty n
  | row :: rows => (buildRows rows).addRow row

def rowsSize {n : Nat} (rows : List (List (Fin n))) : Nat := (rows.map List.length).sum

def rowsValid {n : Nat} (rows : List (List (Fin n))) (a : Assignment n) : Bool :=
  rows.all (fun row => row.countP a == 2)

theorem buildRows_eval {n : Nat} (rows : List (List (Fin n))) (a : Assignment n) :
    (buildRows rows).constraints.eval ((buildRows rows).circuit.eval a) = rowsValid rows a := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simpa only [buildRows, BatchState.addRow_eval, ih, rowsValid, List.all_cons,
        Bool.and_comm]

theorem buildRows_gates {n : Nat} (rows : List (List (Fin n))) :
    (buildRows rows).circuit.gates = rows.length + 11 * rowsSize rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [buildRows, BatchState.addRow_gates, ih, rowsSize, List.map_cons,
        List.sum_cons, List.length_cons]
      omega

theorem buildRows_variables {n : Nat} (rows : List (List (Fin n))) :
    (buildRows rows).wires = n + rows.length + 11 * rowsSize rows := by
  have h := (buildRows rows).circuit.variable_count
  rw [buildRows_gates] at h
  omega

theorem buildRows_constraints_length {n : Nat} (rows : List (List (Fin n))) :
    (buildRows rows).constraints.length = 2 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [buildRows, BatchState.addRow_constraints_length, ih, List.length_cons]
      omega

theorem buildRows_constraints_width {n : Nat} (rows : List (List (Fin n))) :
    WidthAtMost 3 (buildRows rows).constraints := by
  induction rows with
  | nil => intro c hc; cases hc
  | cons row rows ih => exact BatchState.addRow_width _ _ ih

end HamParity
