module

public import HamParity.CounterStep

@[expose] public section

namespace HamParity

structure CounterState (n : Nat) where
  wires : Nat
  circuit : Circuit n wires
  inputs : Fin n → Fin wires
  one : Fin wires
  two : Fin wires
  three : Fin wires

namespace CounterState

def initial (n : Nat) : CounterState n :=
  ⟨n+1, .snoc .nil (.constant false), Fin.succ, 0, 0, 0⟩

def advance {n : Nat} (s : CounterState n) (i : Fin n) : CounterState n :=
  ⟨s.wires+11, s.circuit.compose (counterStep s.one s.two s.three (s.inputs i)),
    fun j => shiftWire 11 (s.inputs j), counterOne s.wires, counterTwo s.wires, 0⟩

def valueOne {n : Nat} (s : CounterState n) (a : Assignment n) : Bool :=
  s.circuit.eval a s.one
def valueTwo {n : Nat} (s : CounterState n) (a : Assignment n) : Bool :=
  s.circuit.eval a s.two
def valueThree {n : Nat} (s : CounterState n) (a : Assignment n) : Bool :=
  s.circuit.eval a s.three

theorem advance_inputs {n : Nat} (s : CounterState n) (i j : Fin n) (a : Assignment n) :
    (s.advance i).circuit.eval a ((s.advance i).inputs j) = s.circuit.eval a (s.inputs j) := by
  simp only [advance, Circuit.eval_compose, counterStep_old]

theorem advance_one {n : Nat} (s : CounterState n) (i : Fin n) (a : Assignment n) :
    (s.advance i).valueOne a = (s.valueOne a || s.circuit.eval a (s.inputs i)) := by
  simp only [valueOne, advance, Circuit.eval_compose, counterStep_one]

theorem advance_two {n : Nat} (s : CounterState n) (i : Fin n) (a : Assignment n) :
    (s.advance i).valueTwo a =
      (s.valueTwo a || (s.valueOne a && s.circuit.eval a (s.inputs i))) := by
  simp only [valueOne, valueTwo, advance, Circuit.eval_compose, counterStep_two]

theorem advance_three {n : Nat} (s : CounterState n) (i : Fin n) (a : Assignment n) :
    (s.advance i).valueThree a =
      (s.valueThree a || (s.valueTwo a && s.circuit.eval a (s.inputs i))) := by
  simp only [valueTwo, valueThree, advance, Circuit.eval_compose, counterStep_three]

end CounterState

def buildCounter {n : Nat} : List (Fin n) → CounterState n
  | [] => .initial n
  | i :: xs => (buildCounter xs).advance i

theorem buildCounter_inputs {n : Nat} (xs : List (Fin n)) (a : Assignment n) (i : Fin n) :
    (buildCounter xs).circuit.eval a ((buildCounter xs).inputs i) = a i := by
  induction xs with
  | nil => rfl
  | cons j xs ih => simpa only [buildCounter, CounterState.advance_inputs] using ih

theorem threshold_one_step (c : Nat) (b : Bool) :
    (decide (1 ≤ c) || b) = decide (1 ≤ c + if b then 1 else 0) := by
  cases b <;> apply Bool.eq_iff_iff.mpr <;> simp <;> omega

theorem threshold_two_step (c : Nat) (b : Bool) :
    (decide (2 ≤ c) || (decide (1 ≤ c) && b)) =
      decide (2 ≤ c + if b then 1 else 0) := by
  cases b <;> apply Bool.eq_iff_iff.mpr <;> simp <;> omega

theorem threshold_three_step (c : Nat) (b : Bool) :
    (decide (3 ≤ c) || (decide (2 ≤ c) && b)) =
      decide (3 ≤ c + if b then 1 else 0) := by
  cases b <;> apply Bool.eq_iff_iff.mpr <;> simp <;> omega

theorem buildCounter_flags {n : Nat} (xs : List (Fin n)) (a : Assignment n) :
    (buildCounter xs).valueOne a = decide (1 ≤ xs.countP a) ∧
    (buildCounter xs).valueTwo a = decide (2 ≤ xs.countP a) ∧
    (buildCounter xs).valueThree a = decide (3 ≤ xs.countP a) := by
  induction xs with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons i xs ih =>
      simp only [buildCounter, CounterState.advance_one, CounterState.advance_two,
        CounterState.advance_three, buildCounter_inputs, ih.1, ih.2.1, ih.2.2,
        threshold_one_step, threshold_two_step, threshold_three_step, List.countP_cons]
      simp

theorem buildCounter_gates {n : Nat} (xs : List (Fin n)) :
    (buildCounter xs).circuit.gates = 1 + 11 * xs.length := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      simp [buildCounter, CounterState.advance, Circuit.gates_compose,
        counterStep_gates, ih, Nat.mul_add]
      omega

theorem buildCounter_variables {n : Nat} (xs : List (Fin n)) :
    (buildCounter xs).wires = n + 1 + 11 * xs.length := by
  have h := (buildCounter xs).circuit.variable_count
  rw [buildCounter_gates] at h
  omega

end HamParity
