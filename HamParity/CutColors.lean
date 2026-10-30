module

public import HamParity.Counting

/-! Concrete binary cut-color constraints. All selected-edge and color wires are
ordinary variables; this module does not existentially forget colors. Each edge
contributes two width-three clauses and the root contributes one unit clause. -/

@[expose] public section

namespace HamParity

structure CutEdge (v : Nat) where
  selected : Fin v
  leftColor : Fin v
  rightColor : Fin v

def CutEdge.clauses {v : Nat} (e : CutEdge v) : CNF v :=
  [[⟨e.selected, false⟩, ⟨e.leftColor, false⟩, ⟨e.rightColor, true⟩],
   [⟨e.selected, false⟩, ⟨e.leftColor, true⟩, ⟨e.rightColor, false⟩]]

theorem CutEdge.correct {v : Nat} (e : CutEdge v) (a : Assignment v) :
    e.clauses.eval a = true ↔
      (a e.selected = true → a e.leftColor = a e.rightColor) := by
  cases hx : a e.selected <;> cases hu : a e.leftColor <;> cases hv : a e.rightColor <;>
    simp [CutEdge.clauses, CNF.eval, Clause.eval, Literal.eval, hx, hu, hv]

def edgeCutClauses {v : Nat} (edges : List (CutEdge v)) : CNF v :=
  edges.flatMap CutEdge.clauses

theorem edgeCutClauses_correct {v : Nat} (edges : List (CutEdge v)) (a : Assignment v) :
    (edgeCutClauses edges).eval a = true ↔
      ∀ e ∈ edges, a e.selected = true → a e.leftColor = a e.rightColor := by
  induction edges with
  | nil => simp [edgeCutClauses, CNF.eval]
  | cons e es ih =>
      simp only [edgeCutClauses, List.flatMap_cons, eval_append, Bool.and_eq_true]
      rw [e.correct]
      change _ ∧ (edgeCutClauses es).eval a = true ↔ _
      rw [ih]
      simp

theorem edgeCutClauses_length {v : Nat} (edges : List (CutEdge v)) :
    (edgeCutClauses edges).length = 2 * edges.length := by
  induction edges with
  | nil => rfl
  | cons e es ih =>
      simp only [edgeCutClauses, List.flatMap_cons, List.length_append,
        CutEdge.clauses, List.length_cons, List.length_nil]
      change 2 + (edgeCutClauses es).length = 2 * (es.length + 1)
      rw [ih]
      omega

theorem edgeCutClauses_width {v : Nat} (edges : List (CutEdge v)) :
    WidthAtMost 3 (edgeCutClauses edges) := by
  induction edges with
  | nil => simp [WidthAtMost, edgeCutClauses]
  | cons e es ih =>
      apply width_append
      · simp [WidthAtMost, CutEdge.clauses]
      · exact ih

def rootedCutClauses {v : Nat} (rootColor : Fin v) (edges : List (CutEdge v)) : CNF v :=
  [[⟨rootColor, false⟩]] ++ edgeCutClauses edges

theorem rootedCutClauses_correct {v : Nat} (rootColor : Fin v)
    (edges : List (CutEdge v)) (a : Assignment v) :
    (rootedCutClauses rootColor edges).eval a = true ↔
      a rootColor = false ∧
        ∀ e ∈ edges, a e.selected = true → a e.leftColor = a e.rightColor := by
  unfold rootedCutClauses
  rw [eval_append]
  simp only [Bool.and_eq_true]
  rw [edgeCutClauses_correct]
  have hu : CNF.eval ([[⟨rootColor, false⟩]] : CNF v) a = true ↔ a rootColor = false := by
    cases h : a rootColor <;> simp [CNF.eval, Clause.eval, Literal.eval, h]
  exact and_congr hu Iff.rfl

theorem rootedCutClauses_length {v : Nat} (rootColor : Fin v) (edges : List (CutEdge v)) :
    (rootedCutClauses rootColor edges).length = 1 + 2 * edges.length := by
  simp [rootedCutClauses, edgeCutClauses_length, Nat.add_comm]

theorem rootedCutClauses_width {v : Nat} (rootColor : Fin v) (edges : List (CutEdge v)) :
    WidthAtMost 3 (rootedCutClauses rootColor edges) := by
  apply width_append
  · simp [WidthAtMost]
  · exact edgeCutClauses_width edges

end HamParity
