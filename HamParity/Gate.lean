module

public import HamParity.CNF

/-! Each gate adds exactly one fresh output variable at index zero. Older wires
are shifted with Fin.succ. Clauses enforce full equivalence, not implication. -/

@[expose] public section

namespace HamParity

inductive Gate (v : Nat) where
  | constant (value : Bool)
  | neg (input : Fin v)
  | conj (left right : Fin v)
  | xor (left right : Fin v)
  deriving Repr

def Gate.eval {v : Nat} (g : Gate v) (a : Assignment v) : Bool :=
  match g with
  | .constant b => b
  | .neg x => !a x
  | .conj x y => a x && a y
  | .xor x y => Bool.xor (a x) (a y)

def Gate.clauses {v : Nat} (g : Gate v) : CNF (v+1) :=
  match g with
  | .constant b => [[⟨0, b⟩]]
  | .neg x => [[⟨x.succ, true⟩, ⟨0, true⟩],
               [⟨x.succ, false⟩, ⟨0, false⟩]]
  | .conj x y => [[⟨x.succ, false⟩, ⟨y.succ, false⟩, ⟨0, true⟩],
                  [⟨x.succ, true⟩, ⟨0, false⟩],
                  [⟨y.succ, true⟩, ⟨0, false⟩]]
  | .xor x y => [[⟨x.succ, true⟩, ⟨y.succ, true⟩, ⟨0, false⟩],
                 [⟨x.succ, true⟩, ⟨y.succ, false⟩, ⟨0, true⟩],
                 [⟨x.succ, false⟩, ⟨y.succ, true⟩, ⟨0, true⟩],
                 [⟨x.succ, false⟩, ⟨y.succ, false⟩, ⟨0, false⟩]]

theorem Gate.eval_clauses {v : Nat} (g : Gate v) (a : Assignment (v+1)) :
    g.clauses.eval a = (a 0 == g.eval (tailAssignment a)) := by
  cases g with
  | constant b =>
      cases b <;> cases h : a 0 <;>
        simp [Gate.clauses, CNF.eval, Clause.eval, Literal.eval, Gate.eval, h]
  | neg x =>
      cases hx : a x.succ <;> cases hz : a 0 <;>
        simp [Gate.clauses, CNF.eval, Clause.eval, Literal.eval, Gate.eval,
          tailAssignment, hx, hz]
  | conj x y =>
      cases hx : a x.succ <;> cases hy : a y.succ <;> cases hz : a 0 <;>
        simp [Gate.clauses, CNF.eval, Clause.eval, Literal.eval, Gate.eval,
          tailAssignment, hx, hy, hz]
  | xor x y =>
      cases hx : a x.succ <;> cases hy : a y.succ <;> cases hz : a 0 <;>
        simp [Gate.clauses, CNF.eval, Clause.eval, Literal.eval, Gate.eval,
          tailAssignment, hx, hy, hz]

theorem Gate.width {v : Nat} (g : Gate v) : WidthAtMost 3 g.clauses := by
  cases g <;> simp [WidthAtMost, Gate.clauses]

theorem Gate.clause_count {v : Nat} (g : Gate v) : g.clauses.length ≤ 4 := by
  cases g <;> simp [Gate.clauses]

end HamParity
