module

public import HamParity.Counting

/-! An actual five-gate full adder, compiled by the circuit compiler.
The XOR of the two carry terms equals their OR because the terms are disjoint. -/

@[expose] public section

namespace HamParity

def fullAdder {v : Nat} (x y z : Fin v) : Circuit v (v+5) :=
  let c1 := Circuit.snoc Circuit.nil (Gate.xor x y)
  let c2 := Circuit.snoc c1 (Gate.xor 0 z.succ)
  let c3 := Circuit.snoc c2 (Gate.conj x.succ.succ y.succ.succ)
  let c4 := Circuit.snoc c3
    (Gate.conj (Fin.succ (Fin.succ (0 : Fin (v+1)))) z.succ.succ.succ)
  Circuit.snoc c4 (Gate.xor (Fin.succ (0 : Fin (v+3))) 0)

def fullAdderSum (v : Nat) : Fin (v+5) :=
  Fin.succ (Fin.succ (Fin.succ (0 : Fin (v+2))))

theorem fullAdder_sum {v : Nat} (x y z : Fin v) (a : Assignment v) :
    (fullAdder x y z).eval a (fullAdderSum v) =
      Bool.xor (Bool.xor (a x) (a y)) (a z) := by
  rfl

theorem fullAdder_carry {v : Nat} (x y z : Fin v) (a : Assignment v) :
    (fullAdder x y z).eval a 0 =
      Bool.xor (a x && a y) (Bool.xor (a x) (a y) && a z) := by
  rfl

def bitValue (b : Bool) : Nat := if b then 1 else 0

theorem fullAdder_value {v : Nat} (x y z : Fin v) (a : Assignment v) :
    bitValue (a x) + bitValue (a y) + bitValue (a z) =
      bitValue ((fullAdder x y z).eval a (fullAdderSum v)) +
        2 * bitValue ((fullAdder x y z).eval a 0) := by
  rw [fullAdder_sum, fullAdder_carry]
  cases hx : a x <;> cases hy : a y <;> cases hz : a z <;>
    simp [bitValue, hx, hy, hz]

theorem fullAdder_gates {v : Nat} (x y z : Fin v) : (fullAdder x y z).gates = 5 := rfl

theorem fullAdder_clauses {v : Nat} (x y z : Fin v) :
    (fullAdder x y z).clauses.length = 18 := by
  simp [fullAdder, Circuit.clauses, Gate.clauses, CNF.rename]

end HamParity
