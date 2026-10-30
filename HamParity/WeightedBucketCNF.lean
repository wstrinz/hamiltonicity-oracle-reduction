module

public import HamParity.WeightedArithmetic

/-! Unelaborated draft. Actual clauses and bucket pins; no assumed q semantics. -/
@[expose] public section
namespace HamParity

def weightedBucketCNF {p : Nat} (xs : List (WeightedWire p)) (t : Nat) :
    CNF (buildWeighted xs).wires :=
  (buildWeighted xs).circuit.clauses ++ bucketPins (buildWeighted xs).output t

theorem weightedBucketCNF_eval_extension_iff {p : Nat} (xs : List (WeightedWire p))
    (t : Nat) (a : Assignment p) :
    (weightedBucketCNF xs t).eval ((buildWeighted xs).circuit.eval a) = true ↔
      heapValue xs a = t := by
  simp only [weightedBucketCNF, eval_append, Circuit.eval_satisfies, Bool.true_and]
  rw [bucketPins_eval_iff, buildWeighted_value]

theorem weightedBucketCNF_satisfies_iff {p : Nat} (xs : List (WeightedWire p))
    (t : Nat) (a : Assignment (buildWeighted xs).wires) :
    (weightedBucketCNF xs t).eval a = true ↔
      a = (buildWeighted xs).circuit.eval ((buildWeighted xs).circuit.inputs a) ∧
      heapValue xs ((buildWeighted xs).circuit.inputs a) = t := by
  rw [weightedBucketCNF, Circuit.with_constraints]
  constructor
  · rintro ⟨ha,hq⟩
    refine ⟨ha,?_⟩
    have hv := (bucketPins_eval_iff (buildWeighted xs).output t a).mp hq
    rwa [ha, buildWeighted_value] at hv
  · rintro ⟨ha,ht⟩
    refine ⟨ha,?_⟩
    apply (bucketPins_eval_iff (buildWeighted xs).output t a).mpr
    rwa [ha, buildWeighted_value]

theorem weightedBucketCNF_count {p : Nat} (xs : List (WeightedWire p)) (t : Nat) :
    modelCount (weightedBucketCNF xs t) =
      (assignments p).countP (fun a => decide (heapValue xs a = t)) := by
  rw [weightedBucketCNF, Circuit.constrained_model_count]
  apply List.countP_congr
  intro a _
  rw [bucketPins_eval_iff, buildWeighted_value]
  simp

theorem weightedBucketCNF_unique_extension {p : Nat} (xs : List (WeightedWire p))
    (t : Nat) (a : Assignment p) (ht : heapValue xs a = t) :
    ∃ b : Assignment (buildWeighted xs).wires,
      (weightedBucketCNF xs t).eval b = true ∧ (buildWeighted xs).circuit.inputs b = a ∧
      ∀ c, (weightedBucketCNF xs t).eval c = true →
        (buildWeighted xs).circuit.inputs c = a → c=b := by
  refine ⟨(buildWeighted xs).circuit.eval a,
    (weightedBucketCNF_eval_extension_iff xs t a).mpr ht,
    (buildWeighted xs).circuit.inputs_eval a,?_⟩
  intro c hc ha
  have he := ((weightedBucketCNF_satisfies_iff xs t c).mp hc).1
  simpa only [ha] using he

theorem weightedBucketCNF_width {p : Nat} (xs : List (WeightedWire p)) (t : Nat) :
    WidthAtMost 3 (weightedBucketCNF xs t) :=
  width_append (buildWeighted xs).circuit.width (bucketPins_width _ _)

theorem weightedBucketCNF_clause_bound {p : Nat} (xs : List (WeightedWire p)) (t : Nat) :
    (weightedBucketCNF xs t).length ≤
      18*(normalizeHeap xs).steps + 19*massWidth (heapMass xs) + 3 := by
  have hp := bucketPins_length_le (buildWeighted xs).output t
    (by rw [buildWeighted_output_length]; omega)
  rw [buildWeighted_output_length] at hp
  rw [weightedBucketCNF, List.length_append, buildWeighted_clauses]
  omega

theorem weightedBucketCNF_clause_count_of_inRange {p : Nat} (xs : List (WeightedWire p))
    (t : Nat) (ht : t < 2^(massWidth (heapMass xs)+1)) :
    (weightedBucketCNF xs t).length =
      18*(normalizeHeap xs).steps + 19*massWidth (heapMass xs) + 3 := by
  have ht' : t < 2^(buildWeighted xs).output.length := by
    simpa only [buildWeighted_output_length] using ht
  simp only [weightedBucketCNF, List.length_append, buildWeighted_clauses]
  rw [bucketPins, ite_eq_left ht', binaryPins_length, buildWeighted_output_length]
  omega

theorem buildWeighted_palette_variables {p : Nat} (xs : List (WeightedWire p)) (d : Nat)
    (h : ∀ z ∈ xs, z.1 < d) :
    (buildWeighted xs).wires ≤ p + 5*xs.length + 2 + 5*(d+(xs.length+1).log2+1) := by
  rw [buildWeighted_variables]
  have hs := normalizeHeap_steps_le xs
  have hw := heapWidth_palette_bound xs d h
  omega

theorem weightedBucketCNF_palette_clauses {p : Nat} (xs : List (WeightedWire p))
    (t d : Nat) (h : ∀ z ∈ xs, z.1 < d) :
    (weightedBucketCNF xs t).length ≤
      18*xs.length + 19*(d+(xs.length+1).log2+1) + 3 := by
  have hc := weightedBucketCNF_clause_bound xs t
  have hs := normalizeHeap_steps_le xs
  have hw := heapWidth_palette_bound xs d h
  omega

end HamParity
