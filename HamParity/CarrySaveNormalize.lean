module

public import HamParity.HeapCompression

@[expose] public section

namespace HamParity

structure HeapResult (p : Nat) where
  wires : Nat
  circuit : Circuit p wires
  heap : List (WeightedWire wires)
  steps : Nat

/-- Total, deterministic normalization. Each recursive call removes one live
occurrence while composing a real five-gate compressor. No schedule certificate
or assumed width/count identity is supplied as an input. -/
def normalizeHeap {p : Nat} (xs : List (WeightedWire p)) : HeapResult p :=
  match h : findHeapTriple xs with
  | none => ⟨p, .nil, xs, 0⟩
  | some t =>
      let rest := normalizeHeap t.compressed
      ⟨rest.wires, t.compressor.compose rest.circuit, rest.heap, rest.steps+1⟩
termination_by xs.length
decreasing_by exact compression_length_lt xs t h

theorem normalizeHeap_shape {p : Nat} (xs : List (WeightedWire p)) :
    ∀ k, columnCount k (normalizeHeap xs).heap ≤ 2 := by
  cases h : findHeapTriple xs with
  | none =>
      rw [normalizeHeap.eq_def, h]
      exact findHeapTriple_none_shape xs h
  | some t =>
      rw [normalizeHeap.eq_def, h]
      exact normalizeHeap_shape t.compressed
termination_by xs.length
decreasing_by exact compression_length_lt xs t h

theorem normalizeHeap_length_steps {p : Nat} (xs : List (WeightedWire p)) :
    (normalizeHeap xs).heap.length + (normalizeHeap xs).steps = xs.length := by
  cases h : findHeapTriple xs with
  | none => rw [normalizeHeap.eq_def, h]; simp
  | some t =>
      rw [normalizeHeap.eq_def, h]
      have hi := normalizeHeap_length_steps t.compressed
      have hl := compression_length_step xs t h
      change (normalizeHeap t.compressed).heap.length +
        ((normalizeHeap t.compressed).steps+1) = xs.length
      omega
termination_by xs.length
decreasing_by exact compression_length_lt xs t h

theorem normalizeHeap_steps_le {p : Nat} (xs : List (WeightedWire p)) :
    (normalizeHeap xs).steps ≤ xs.length := by
  have h := normalizeHeap_length_steps xs
  omega

theorem normalizeHeap_mass {p : Nat} (xs : List (WeightedWire p)) :
    heapMass (normalizeHeap xs).heap = heapMass xs := by
  cases h : findHeapTriple xs with
  | none => rw [normalizeHeap.eq_def, h]
  | some t =>
      rw [normalizeHeap.eq_def, h]
      change heapMass (normalizeHeap t.compressed).heap = heapMass xs
      rw [normalizeHeap_mass, t.compressed_mass]
      exact (heapMass_perm (findHeapTriple_perm xs t h)).symm
termination_by xs.length
decreasing_by exact compression_length_lt xs t h

theorem normalizeHeap_value {p : Nat} (xs : List (WeightedWire p)) (a : Assignment p) :
    heapValue (normalizeHeap xs).heap ((normalizeHeap xs).circuit.eval a) = heapValue xs a := by
  cases h : findHeapTriple xs with
  | none => rw [normalizeHeap.eq_def, h]; rfl
  | some t =>
      rw [normalizeHeap.eq_def, h]
      change heapValue (normalizeHeap t.compressed).heap
        ((t.compressor.compose (normalizeHeap t.compressed).circuit).eval a) = heapValue xs a
      rw [Circuit.eval_compose, normalizeHeap_value, t.compressed_value]
      exact (heapValue_perm (findHeapTriple_perm xs t h) a).symm
termination_by xs.length
decreasing_by exact compression_length_lt xs t h

theorem normalizeHeap_gates {p : Nat} (xs : List (WeightedWire p)) :
    (normalizeHeap xs).circuit.gates = 5 * (normalizeHeap xs).steps := by
  cases h : findHeapTriple xs with
  | none => rw [normalizeHeap.eq_def, h]; rfl
  | some t =>
      rw [normalizeHeap.eq_def, h]
      simp only [Circuit.gates_compose, HeapTriple.compressor, fullAdder_gates]
      rw [normalizeHeap_gates]
      omega
termination_by xs.length
decreasing_by exact compression_length_lt xs t h

theorem normalizeHeap_clauses {p : Nat} (xs : List (WeightedWire p)) :
    (normalizeHeap xs).circuit.clauses.length = 18 * (normalizeHeap xs).steps := by
  cases h : findHeapTriple xs with
  | none => rw [normalizeHeap.eq_def, h]; rfl
  | some t =>
      rw [normalizeHeap.eq_def, h]
      simp only [Circuit.clauses_length_compose, HeapTriple.compressor, fullAdder_clauses]
      rw [normalizeHeap_clauses]
      omega
termination_by xs.length
decreasing_by exact compression_length_lt xs t h

theorem normalizeHeap_variables {p : Nat} (xs : List (WeightedWire p)) :
    (normalizeHeap xs).wires = p + 5 * (normalizeHeap xs).steps := by
  have h := (normalizeHeap xs).circuit.variable_count
  rwa [normalizeHeap_gates] at h

theorem normalizeHeap_gate_bound {p : Nat} (xs : List (WeightedWire p)) :
    (normalizeHeap xs).circuit.gates ≤ 5 * xs.length := by
  rw [normalizeHeap_gates]
  exact Nat.mul_le_mul_left 5 (normalizeHeap_steps_le xs)

theorem normalizeHeap_clause_bound {p : Nat} (xs : List (WeightedWire p)) :
    (normalizeHeap xs).circuit.clauses.length ≤ 18 * xs.length := by
  rw [normalizeHeap_clauses]
  exact Nat.mul_le_mul_left 18 (normalizeHeap_steps_le xs)

theorem normalizeHeap_column_bound {p : Nat} (xs : List (WeightedWire p))
    (z : WeightedWire (normalizeHeap xs).wires) (hz : z ∈ (normalizeHeap xs).heap) :
    2^z.1 ≤ heapMass xs := by
  have h := power_le_heapMass (normalizeHeap xs).heap z hz
  rwa [normalizeHeap_mass] at h

theorem normalizeHeap_unique_extension {p : Nat} (xs : List (WeightedWire p))
    (a : Assignment p) :
    ∃ b : Assignment (normalizeHeap xs).wires,
      (normalizeHeap xs).circuit.clauses.eval b = true ∧
      (normalizeHeap xs).circuit.inputs b = a ∧
      ∀ c, (normalizeHeap xs).circuit.clauses.eval c = true →
        (normalizeHeap xs).circuit.inputs c = a → c = b :=
  (normalizeHeap xs).circuit.unique_extension a

end HamParity
