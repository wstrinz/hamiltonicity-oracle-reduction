module

public import HamParity.Gate

/-! A topologically ordered circuit whose wire types prevent forward references.
Primary inputs are arbitrary counted bits. Every added helper is a gate output. -/

@[expose] public section

namespace HamParity

inductive Circuit (n : Nat) : Nat → Type where
  | nil : Circuit n n
  | snoc {v : Nat} (previous : Circuit n v) (gate : Gate v) : Circuit n (v+1)

def Circuit.gates {n v : Nat} (c : Circuit n v) : Nat :=
  match c with
  | .nil => 0
  | .snoc p _ => p.gates + 1

def Circuit.eval {n v : Nat} (c : Circuit n v) (x : Assignment n) : Assignment v :=
  match c with
  | .nil => x
  | .snoc p g => consAssignment (g.eval (p.eval x)) (p.eval x)

def Circuit.inputs {n v : Nat} (c : Circuit n v) (a : Assignment v) : Assignment n :=
  match c with
  | .nil => a
  | .snoc p _ => p.inputs (tailAssignment a)

def Circuit.clauses {n v : Nat} (c : Circuit n v) : CNF v :=
  match c with
  | .nil => []
  | .snoc p g => p.clauses.rename Fin.succ ++ g.clauses

@[simp] theorem Circuit.inputs_eval {n v : Nat} (c : Circuit n v) (x : Assignment n) :
    c.inputs (c.eval x) = x := by
  induction c with
  | nil => rfl
  | snoc p g ih => simpa [Circuit.inputs, Circuit.eval] using ih

theorem Circuit.satisfies_iff {n v : Nat} (c : Circuit n v) (a : Assignment v) :
    c.clauses.eval a = true ↔ a = c.eval (c.inputs a) := by
  induction c with
  | nil => simp [Circuit.clauses, CNF.eval, Circuit.eval, Circuit.inputs]
  | @snoc v p g ih =>
      simp only [Circuit.clauses, eval_append, eval_rename, Gate.eval_clauses,
        Bool.and_eq_true, beq_iff_eq]
      change (p.clauses.eval (tailAssignment a) = true ∧
        a 0 = g.eval (tailAssignment a)) ↔ _
      rw [ih]
      constructor
      · rintro ⟨ht, hz⟩
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · change a 0 = g.eval (p.eval (p.inputs (tailAssignment a)))
          rw [← ht]
          exact hz
        · change a j.succ = p.eval (p.inputs (tailAssignment a)) j
          exact congrFun ht j
      · intro h
        have ht : tailAssignment a = p.eval (p.inputs (tailAssignment a)) := by
          funext j
          exact congrFun h j.succ
        refine ⟨ht, ?_⟩
        have hz := congrFun h 0
        change a 0 = g.eval (p.eval (p.inputs (tailAssignment a))) at hz
        rwa [← ht] at hz

theorem Circuit.eval_satisfies {n v : Nat} (c : Circuit n v) (x : Assignment n) :
    c.clauses.eval (c.eval x) = true := by
  rw [c.satisfies_iff, c.inputs_eval]

theorem Circuit.unique_extension {n v : Nat} (c : Circuit n v) (x : Assignment n) :
    ∃ a : Assignment v, c.clauses.eval a = true ∧ c.inputs a = x ∧
      ∀ b : Assignment v, c.clauses.eval b = true → c.inputs b = x → b = a := by
  refine ⟨c.eval x, c.eval_satisfies x, c.inputs_eval x, ?_⟩
  intro b hb hx
  simpa [hx] using (c.satisfies_iff b).mp hb

theorem Circuit.width {n v : Nat} (c : Circuit n v) : WidthAtMost 3 c.clauses := by
  induction c with
  | nil => simp [WidthAtMost, Circuit.clauses]
  | snoc p g ih => exact width_append (width_rename Fin.succ p.clauses ih) g.width

theorem Circuit.clause_count {n v : Nat} (c : Circuit n v) :
    c.clauses.length ≤ 4 * c.gates := by
  induction c with
  | nil => simp [Circuit.clauses, Circuit.gates]
  | snoc p g ih =>
      simpa [Circuit.clauses, Circuit.gates, Nat.mul_add] using
        Nat.add_le_add ih g.clause_count

theorem Circuit.variable_count {n v : Nat} (c : Circuit n v) : v = n + c.gates := by
  induction c with
  | nil => simp [Circuit.gates]
  | snoc p g ih => simpa [Circuit.gates, Nat.add_assoc] using congrArg Nat.succ ih

theorem Circuit.with_constraints {n v : Nat} (c : Circuit n v) (q : CNF v)
    (a : Assignment v) :
    (c.clauses ++ q).eval a = true ↔
      a = c.eval (c.inputs a) ∧ q.eval a = true := by
  simp only [eval_append, Bool.and_eq_true, c.satisfies_iff]

end HamParity
