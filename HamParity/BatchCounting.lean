module

public import HamParity.BatchRows

@[expose] public section

namespace HamParity

def batchConstraints {n : Nat} (rows : List (List (Fin n))) (q : CNF n) :
    CNF (buildRows rows).wires :=
  (buildRows rows).constraints ++ q.rename (buildRows rows).circuit.inputWire

def batchCNF {n : Nat} (rows : List (List (Fin n))) (q : CNF n) :
    CNF (buildRows rows).wires :=
  (buildRows rows).circuit.clauses ++ batchConstraints rows q

theorem batchConstraints_eval {n : Nat} (rows : List (List (Fin n))) (q : CNF n)
    (a : Assignment n) :
    (batchConstraints rows q).eval ((buildRows rows).circuit.eval a) =
      (rowsValid rows a && q.eval a) := by
  simp only [batchConstraints, eval_append, eval_rename, Circuit.eval_inputWire, buildRows_eval]

theorem batchCNF_count {n : Nat} (rows : List (List (Fin n))) (q : CNF n) :
    modelCount (batchCNF rows q) =
      (assignments n).countP (fun a => rowsValid rows a && q.eval a) := by
  rw [batchCNF, Circuit.constrained_model_count]
  apply List.countP_congr
  intro a _
  rw [batchConstraints_eval]

theorem batchCNF_satisfies_iff {n : Nat} (rows : List (List (Fin n))) (q : CNF n)
    (a : Assignment (buildRows rows).wires) :
    (batchCNF rows q).eval a = true ↔
      a = (buildRows rows).circuit.eval ((buildRows rows).circuit.inputs a) ∧
      rowsValid rows ((buildRows rows).circuit.inputs a) = true ∧
      q.eval ((buildRows rows).circuit.inputs a) = true := by
  rw [batchCNF, Circuit.with_constraints]
  constructor
  · rintro ⟨he, hq⟩
    rw [he, batchConstraints_eval, Bool.and_eq_true] at hq
    exact ⟨he, hq⟩
  · rintro ⟨he, hrows, hq⟩
    refine ⟨he, ?_⟩
    rw [he, batchConstraints_eval, Bool.and_eq_true]
    exact ⟨hrows, hq⟩

theorem batchCNF_unique_extension {n : Nat} (rows : List (List (Fin n))) (q : CNF n)
    (x : Assignment n) (hr : rowsValid rows x = true) (hq : q.eval x = true) :
    ∃ a : Assignment (buildRows rows).wires,
      (batchCNF rows q).eval a = true ∧ (buildRows rows).circuit.inputs a = x ∧
      ∀ b, (batchCNF rows q).eval b = true →
        (buildRows rows).circuit.inputs b = x → b = a := by
  refine ⟨(buildRows rows).circuit.eval x, ?_, Circuit.inputs_eval _ _, ?_⟩
  · rw [batchCNF_satisfies_iff, Circuit.inputs_eval]
    exact ⟨rfl, hr, hq⟩
  · intro b hb hi
    have he := ((batchCNF_satisfies_iff rows q b).mp hb).1
    simpa [hi] using he

theorem batchCNF_width {n : Nat} (rows : List (List (Fin n))) (q : CNF n)
    (hq : WidthAtMost 3 q) : WidthAtMost 3 (batchCNF rows q) :=
  width_append (buildRows rows).circuit.width
    (width_append (buildRows_constraints_width rows) (width_rename _ q hq))

theorem batchCNF_clause_bound {n : Nat} (rows : List (List (Fin n))) (q : CNF n) :
    (batchCNF rows q).length ≤ 6 * rows.length + 44 * rowsSize rows + q.length := by
  have h := (buildRows rows).circuit.clause_count
  rw [buildRows_gates] at h
  simp only [batchCNF, batchConstraints, List.length_append, length_rename,
    buildRows_constraints_length]
  omega

end HamParity
