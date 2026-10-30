module

public import HamParity.BinaryBucket

@[expose] public section

namespace HamParity

/-- Two little-endian rows using shared wire references. A repeated reference
changes the arithmetic coefficient, never the counted primary domain. -/
def rowPairValue {n : Nat} (rows : List (Fin n × Fin n)) (a : Assignment n) : Nat :=
  match rows with
  | [] => 0
  | p :: ps => bitValue (a p.1) + bitValue (a p.2) + 2 * rowPairValue ps a

theorem rowPairValue_rename {n v : Nat} (rows : List (Fin n × Fin n))
    (r : Fin n → Fin v) (a : Assignment v) :
    rowPairValue (rows.map (fun p => (r p.1, r p.2))) a =
      rowPairValue rows (fun i => a (r i)) := by
  induction rows with
  | nil => rfl
  | cons p ps ih => simp only [List.map_cons, rowPairValue, ih]

theorem rowPairValue_two_rows {n : Nat} (rows : List (Fin n × Fin n)) (a : Assignment n) :
    rowPairValue rows a = binaryValue (rows.map (fun p => a p.1)) +
      binaryValue (rows.map (fun p => a p.2)) := by
  induction rows with
  | nil => rfl
  | cons p ps ih =>
      simp only [rowPairValue, List.map_cons, binaryValue, ih]
      omega

theorem fullAdder_preserves_wire {v : Nat} (x y z i : Fin v) (a : Assignment v) :
    (fullAdder x y z).eval a (shiftWire 5 i) = a i := by rfl

theorem Circuit.clauses_length_compose {n v w : Nat} (p : Circuit n v) (q : Circuit v w) :
    (p.compose q).clauses.length = p.clauses.length + q.clauses.length := by
  induction q with
  | nil => simp [Circuit.compose, Circuit.clauses]
  | snoc q g ih =>
      simp only [Circuit.compose, Circuit.clauses, List.length_append, length_rename, ih]
      omega

structure ArithmeticResult (n : Nat) where
  wires : Nat
  circuit : Circuit n wires
  output : List (Fin wires)

/-- A real ripple circuit with a supplied initial carry. Recursive calls receive
renamed rows; earlier sum wires are transported through the suffix input map. -/
def rippleCore {n : Nat} (carry : Fin n) (rows : List (Fin n × Fin n)) : ArithmeticResult n :=
  match rows with
  | [] => ⟨n, .nil, [carry]⟩
  | p :: ps =>
      let first := fullAdder p.1 p.2 carry
      let rest := rippleCore (n := n+5) 0
        (ps.map (fun q => (shiftWire 5 q.1, shiftWire 5 q.2)))
      ⟨rest.wires, first.compose rest.circuit,
        rest.circuit.inputWire (fullAdderSum n) :: rest.output⟩
termination_by rows.length
decreasing_by simp_wf

theorem rippleCore_output_length {n : Nat} (carry : Fin n) (rows : List (Fin n × Fin n)) :
    (rippleCore carry rows).output.length = rows.length + 1 := by
  cases rows with
  | nil => rw [rippleCore.eq_1]; rfl
  | cons p ps =>
      rw [rippleCore.eq_2]
      simp only [List.length_cons]
      rw [rippleCore_output_length]
      simp
termination_by rows.length
decreasing_by simp_wf

theorem rippleCore_gates {n : Nat} (carry : Fin n) (rows : List (Fin n × Fin n)) :
    (rippleCore carry rows).circuit.gates = 5 * rows.length := by
  cases rows with
  | nil => rw [rippleCore.eq_1]; rfl
  | cons p ps =>
      rw [rippleCore.eq_2]
      simp only [Circuit.gates_compose, fullAdder_gates]
      rw [rippleCore_gates]
      simp [Nat.mul_add, Nat.add_comm]
termination_by rows.length
decreasing_by simp_wf

theorem rippleCore_clause_count {n : Nat} (carry : Fin n) (rows : List (Fin n × Fin n)) :
    (rippleCore carry rows).circuit.clauses.length = 18 * rows.length := by
  cases rows with
  | nil => rw [rippleCore.eq_1]; rfl
  | cons p ps =>
      rw [rippleCore.eq_2]
      simp only [Circuit.clauses_length_compose, fullAdder_clauses]
      rw [rippleCore_clause_count]
      simp [Nat.mul_add, Nat.add_comm]
termination_by rows.length
decreasing_by simp_wf

theorem rippleCore_value {n : Nat} (carry : Fin n) (rows : List (Fin n × Fin n))
    (a : Assignment n) :
    binaryValue ((rippleCore carry rows).output.map ((rippleCore carry rows).circuit.eval a)) =
      bitValue (a carry) + rowPairValue rows a := by
  cases rows with
  | nil =>
      rw [rippleCore.eq_1]
      simp [Circuit.eval, binaryValue, rowPairValue]
  | cons p ps =>
      rw [rippleCore.eq_2]
      let first := fullAdder p.1 p.2 carry
      let mapped := ps.map (fun q => (shiftWire 5 q.1, shiftWire 5 q.2))
      let rest := rippleCore (n := n+5) 0 mapped
      change bitValue ((first.compose rest.circuit).eval a
          (rest.circuit.inputWire (fullAdderSum n))) +
        2 * binaryValue (rest.output.map ((first.compose rest.circuit).eval a)) =
          bitValue (a carry) + rowPairValue (p :: ps) a
      rw [Circuit.eval_compose]
      rw [Circuit.eval_inputWire]
      have hi := rippleCore_value (n := n+5) 0 mapped (first.eval a)
      have hr : rowPairValue mapped (first.eval a) = rowPairValue ps a := by
        rw [rowPairValue_rename]
        congr 1
      have hf := fullAdder_value p.1 p.2 carry a
      change binaryValue (rest.output.map (rest.circuit.eval (first.eval a))) = _ at hi
      rw [hi, hr]
      simp only [rowPairValue]
      change bitValue ((fullAdder p.1 p.2 carry).eval a (fullAdderSum n)) +
        2 * (bitValue ((fullAdder p.1 p.2 carry).eval a 0) + rowPairValue ps a) = _
      omega
termination_by rows.length
decreasing_by simp_wf

/-- Supply one constrained-false helper as initial carry, then retain the final
carry output. No separately allocated dense row per weighted edge is introduced. -/
def buildRipple {n : Nat} (rows : List (Fin n × Fin n)) : ArithmeticResult n :=
  let initial : Circuit n (n+1) := .snoc .nil (.constant false)
  let rest := rippleCore (n := n+1) 0 (rows.map (fun p => (p.1.succ, p.2.succ)))
  ⟨rest.wires, initial.compose rest.circuit, rest.output⟩

theorem buildRipple_output_length {n : Nat} (rows : List (Fin n × Fin n)) :
    (buildRipple rows).output.length = rows.length + 1 := by
  simp [buildRipple, rippleCore_output_length]

theorem buildRipple_gates {n : Nat} (rows : List (Fin n × Fin n)) :
    (buildRipple rows).circuit.gates = 1 + 5 * rows.length := by
  simp [buildRipple, Circuit.gates_compose, rippleCore_gates, Circuit.gates]

theorem buildRipple_variables {n : Nat} (rows : List (Fin n × Fin n)) :
    (buildRipple rows).wires = n + 1 + 5 * rows.length := by
  have h := (buildRipple rows).circuit.variable_count
  rw [buildRipple_gates] at h
  omega

theorem buildRipple_clause_count {n : Nat} (rows : List (Fin n × Fin n)) :
    (buildRipple rows).circuit.clauses.length = 1 + 18 * rows.length := by
  simp [buildRipple, Circuit.clauses_length_compose, rippleCore_clause_count,
    Circuit.clauses, Gate.clauses, CNF.rename]

theorem buildRipple_value {n : Nat} (rows : List (Fin n × Fin n)) (a : Assignment n) :
    binaryValue ((buildRipple rows).output.map ((buildRipple rows).circuit.eval a)) =
      rowPairValue rows a := by
  simp only [buildRipple, Circuit.eval_compose]
  rw [rippleCore_value, rowPairValue_rename]
  simp [Circuit.eval, Gate.eval, bitValue]

end HamParity
