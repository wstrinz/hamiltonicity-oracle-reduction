module

public import HamParity.DenseHeapRows

/-! Unelaborated draft: actual normalizer, shared padding zero, then ripple. -/
@[expose] public section
namespace HamParity

def heapPadding {p : Nat} (xs : List (WeightedWire p)) :
    Circuit (normalizeHeap xs).wires ((normalizeHeap xs).wires+1) :=
  .snoc .nil (.constant false)

def weightedRows {p : Nat} (xs : List (WeightedWire p)) :
    List (Fin ((normalizeHeap xs).wires+1) × Fin ((normalizeHeap xs).wires+1)) :=
  denseHeapRows 0 (renameHeap Fin.succ (normalizeHeap xs).heap) (massWidth (heapMass xs))

theorem weightedRows_length {p : Nat} (xs : List (WeightedWire p)) :
    (weightedRows xs).length = massWidth (heapMass xs) := denseHeapRows_length ..

theorem weightedRows_value {p : Nat} (xs : List (WeightedWire p)) (a : Assignment p) :
    rowPairValue (weightedRows xs) ((heapPadding xs).eval ((normalizeHeap xs).circuit.eval a)) =
      heapValue xs a := by
  rw [weightedRows, denseHeapRows_value]
  · rw [heapValue_rename]
    change heapValue (normalizeHeap xs).heap ((normalizeHeap xs).circuit.eval a) = _
    exact normalizeHeap_value xs a
  · rfl
  · intro k
    rw [columnCount_rename]
    exact normalizeHeap_shape xs k
  · intro z hz
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hz
    exact normalizeHeap_width xs y hy

def buildWeighted {p : Nat} (xs : List (WeightedWire p)) : ArithmeticResult p :=
  let r := normalizeHeap xs
  let pad := heapPadding xs
  let tail := buildRipple (weightedRows xs)
  ⟨tail.wires, (r.circuit.compose pad).compose tail.circuit, tail.output⟩

theorem buildWeighted_value {p : Nat} (xs : List (WeightedWire p)) (a : Assignment p) :
    binaryValue ((buildWeighted xs).output.map ((buildWeighted xs).circuit.eval a)) =
      heapValue xs a := by
  simp only [buildWeighted, Circuit.eval_compose]
  rw [buildRipple_value, weightedRows_value]

theorem buildWeighted_output_length {p : Nat} (xs : List (WeightedWire p)) :
    (buildWeighted xs).output.length = massWidth (heapMass xs)+1 := by
  simp [buildWeighted, buildRipple_output_length, weightedRows_length]

theorem buildWeighted_gates {p : Nat} (xs : List (WeightedWire p)) :
    (buildWeighted xs).circuit.gates =
      5*(normalizeHeap xs).steps + 2 + 5*massWidth (heapMass xs) := by
  simp [buildWeighted, Circuit.gates_compose, normalizeHeap_gates, heapPadding,
    Circuit.gates, buildRipple_gates, weightedRows_length, Nat.add_assoc]
  omega

theorem buildWeighted_variables {p : Nat} (xs : List (WeightedWire p)) :
    (buildWeighted xs).wires =
      p + 5*(normalizeHeap xs).steps + 2 + 5*massWidth (heapMass xs) := by
  have h := (buildWeighted xs).circuit.variable_count
  rw [buildWeighted_gates] at h
  omega

theorem buildWeighted_clauses {p : Nat} (xs : List (WeightedWire p)) :
    (buildWeighted xs).circuit.clauses.length =
      18*(normalizeHeap xs).steps + 2 + 18*massWidth (heapMass xs) := by
  simp [buildWeighted, Circuit.clauses_length_compose, normalizeHeap_clauses,
    heapPadding, Circuit.clauses, Gate.clauses, CNF.rename,
    buildRipple_clause_count, weightedRows_length, Nat.add_assoc]
  omega

end HamParity
