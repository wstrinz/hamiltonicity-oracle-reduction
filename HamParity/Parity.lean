module

public import HamParity.Counting

/-! Parity consequences for the implemented circuit compiler. The witness is a
primary assignment satisfying the supplied constraints. This is not yet a graph
or Hamiltonian-cycle soundness theorem. -/

@[expose] public section

namespace HamParity

theorem Circuit.constrained_parity {n v : Nat} (c : Circuit n v) (q : CNF v) :
    modelCount (c.clauses ++ q) % 2 =
      (assignments n).countP (fun x => q.eval (c.eval x)) % 2 := by
  exact congrArg (fun k => k % 2) (c.constrained_model_count q)

theorem Circuit.odd_count_sound {n v : Nat} (c : Circuit n v) (q : CNF v)
    (h : modelCount (c.clauses ++ q) % 2 = 1) :
    ∃ x : Assignment n, q.eval (c.eval x) = true := by
  have hpos : 0 < (assignments n).countP (fun x => q.eval (c.eval x)) := by
    rw [← c.constrained_model_count q]
    omega
  obtain ⟨x, _, hx⟩ := List.countP_pos_iff.mp hpos
  exact ⟨x, hx⟩

end HamParity
