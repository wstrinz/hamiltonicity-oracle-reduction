module

public import HamParity.CycleParity

@[expose] public section

namespace HamParity

def Circuit.compose {n v w : Nat} (p : Circuit n v) (q : Circuit v w) : Circuit n w :=
  match q with
  | .nil => p
  | .snoc q g => .snoc (p.compose q) g

theorem Circuit.eval_compose {n v w : Nat} (p : Circuit n v) (q : Circuit v w)
    (x : Assignment n) : (p.compose q).eval x = q.eval (p.eval x) := by
  induction q with
  | nil => rfl
  | snoc q g ih => simp [Circuit.compose, Circuit.eval, ih]

theorem Circuit.gates_compose {n v w : Nat} (p : Circuit n v) (q : Circuit v w) :
    (p.compose q).gates = p.gates + q.gates := by
  induction q with
  | nil => simp [Circuit.compose, Circuit.gates]
  | snoc q g ih => simp [Circuit.compose, Circuit.gates, ih, Nat.add_assoc]

def shiftWire {v : Nat} : (k : Nat) → Fin v → Fin (v+k)
  | 0, i => i
  | k+1, i => (shiftWire k i).succ

/-- Three threshold flags, updated by eleven deterministic gates. OR is built
from XOR and AND with full equivalence clauses inherited from Gate. -/
def counterStep {v : Nat} (one two three x : Fin v) : Circuit v (v+11) :=
  let c1 := Circuit.snoc Circuit.nil (.xor one x)
  let c2 := Circuit.snoc c1 (.conj one.succ x.succ)
  let c3 := Circuit.snoc c2 (.xor 0 (Fin.succ (0 : Fin (v+1))))
  let c4 := Circuit.snoc c3 (.conj (shiftWire 3 one) (shiftWire 3 x))
  let c5 := Circuit.snoc c4 (.xor (shiftWire 4 two) 0)
  let c6 := Circuit.snoc c5 (.conj (shiftWire 5 two) (Fin.succ (0 : Fin (v+4))))
  let c7 := Circuit.snoc c6 (.xor 0 (Fin.succ (0 : Fin (v+5))))
  let c8 := Circuit.snoc c7 (.conj (shiftWire 7 two) (shiftWire 7 x))
  let c9 := Circuit.snoc c8 (.xor (shiftWire 8 three) 0)
  let c10 := Circuit.snoc c9 (.conj (shiftWire 9 three) (Fin.succ (0 : Fin (v+8))))
  Circuit.snoc c10 (.xor 0 (Fin.succ (0 : Fin (v+9))))

def counterOne (v : Nat) : Fin (v+11) := shiftWire 8 (0 : Fin (v+3))
def counterTwo (v : Nat) : Fin (v+11) := shiftWire 4 (0 : Fin (v+7))

theorem counterStep_old {v : Nat} (one two three x i : Fin v) (a : Assignment v) :
    (counterStep one two three x).eval a (shiftWire 11 i) = a i := by rfl

theorem counterStep_one {v : Nat} (one two three x : Fin v) (a : Assignment v) :
    (counterStep one two three x).eval a (counterOne v) = (a one || a x) := by
  change Bool.xor (a one && a x) (Bool.xor (a one) (a x)) = _
  cases a one <;> cases a x <;> rfl

theorem counterStep_two {v : Nat} (one two three x : Fin v) (a : Assignment v) :
    (counterStep one two three x).eval a (counterTwo v) =
      (a two || (a one && a x)) := by
  change Bool.xor (a two && (a one && a x)) (Bool.xor (a two) (a one && a x)) = _
  cases a one <;> cases a two <;> cases a x <;> rfl

theorem counterStep_three {v : Nat} (one two three x : Fin v) (a : Assignment v) :
    (counterStep one two three x).eval a 0 = (a three || (a two && a x)) := by
  change Bool.xor (a three && (a two && a x)) (Bool.xor (a three) (a two && a x)) = _
  cases a two <;> cases a three <;> cases a x <;> rfl

theorem counterStep_gates {v : Nat} (one two three x : Fin v) :
    (counterStep one two three x).gates = 11 := rfl

end HamParity
