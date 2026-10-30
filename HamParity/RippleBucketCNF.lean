module

public import HamParity.RippleArithmetic

@[expose] public section

namespace HamParity

/-- The actual arithmetic clauses followed by concrete range-safe bucket pins. -/
def rippleCNF {n : Nat} (rows : List (Fin n × Fin n)) (t : Nat) :
    CNF (buildRipple rows).wires :=
  (buildRipple rows).circuit.clauses ++ bucketPins (buildRipple rows).output t

theorem rippleCNF_eval_extension_iff {n : Nat} (rows : List (Fin n × Fin n))
    (t : Nat) (x : Assignment n) :
    (rippleCNF rows t).eval ((buildRipple rows).circuit.eval x) = true ↔
      rowPairValue rows x = t := by
  simp only [rippleCNF, eval_append, Circuit.eval_satisfies, Bool.true_and]
  rw [bucketPins_eval_iff, buildRipple_value]

theorem rippleCNF_satisfies_iff {n : Nat} (rows : List (Fin n × Fin n))
    (t : Nat) (a : Assignment (buildRipple rows).wires) :
    (rippleCNF rows t).eval a = true ↔
      a = (buildRipple rows).circuit.eval ((buildRipple rows).circuit.inputs a) ∧
      rowPairValue rows ((buildRipple rows).circuit.inputs a) = t := by
  rw [rippleCNF, Circuit.with_constraints]
  constructor
  · rintro ⟨ha, hq⟩
    refine ⟨ha, ?_⟩
    have hv := (bucketPins_eval_iff (buildRipple rows).output t a).mp hq
    rw [ha, buildRipple_value] at hv
    exact hv
  · rintro ⟨ha, ht⟩
    refine ⟨ha, ?_⟩
    apply (bucketPins_eval_iff (buildRipple rows).output t a).mpr
    rw [ha, buildRipple_value]
    exact ht

/-- Counts every declared primary assignment, including unused bits; all helpers
are deterministic. No predicate-correctness premise is assumed. -/
theorem rippleCNF_count {n : Nat} (rows : List (Fin n × Fin n)) (t : Nat) :
    modelCount (rippleCNF rows t) =
      (assignments n).countP (fun x => decide (rowPairValue rows x = t)) := by
  rw [rippleCNF, Circuit.constrained_model_count]
  apply List.countP_congr
  intro x _
  rw [bucketPins_eval_iff, buildRipple_value]
  simp

theorem rippleCNF_unique_extension {n : Nat} (rows : List (Fin n × Fin n))
    (t : Nat) (x : Assignment n) (ht : rowPairValue rows x = t) :
    ∃ a : Assignment (buildRipple rows).wires,
      (rippleCNF rows t).eval a = true ∧ (buildRipple rows).circuit.inputs a = x ∧
      ∀ b, (rippleCNF rows t).eval b = true →
        (buildRipple rows).circuit.inputs b = x → b = a := by
  refine ⟨(buildRipple rows).circuit.eval x,
    (rippleCNF_eval_extension_iff rows t x).mpr ht,
    (buildRipple rows).circuit.inputs_eval x, ?_⟩
  intro b hb hx
  have he := ((rippleCNF_satisfies_iff rows t b).mp hb).1
  simpa only [hx] using he

theorem rippleCNF_width {n : Nat} (rows : List (Fin n × Fin n)) (t : Nat) :
    WidthAtMost 3 (rippleCNF rows t) :=
  width_append (buildRipple rows).circuit.width (bucketPins_width _ _)

theorem rippleCNF_clause_bound {n : Nat} (rows : List (Fin n × Fin n)) (t : Nat) :
    (rippleCNF rows t).length ≤ 19 * rows.length + 2 := by
  have hp := bucketPins_length_le (buildRipple rows).output t
    (by rw [buildRipple_output_length]; omega)
  rw [buildRipple_output_length] at hp
  rw [rippleCNF, List.length_append, buildRipple_clause_count]
  omega

theorem rippleCNF_clause_count_of_inRange {n : Nat} (rows : List (Fin n × Fin n))
    (t : Nat) (ht : t < 2 ^ (rows.length + 1)) :
    (rippleCNF rows t).length = 19 * rows.length + 2 := by
  have ht' : t < 2 ^ (buildRipple rows).output.length := by
    simpa only [buildRipple_output_length] using ht
  simp only [rippleCNF, List.length_append, buildRipple_clause_count]
  rw [bucketPins, ite_eq_left ht', binaryPins_length, buildRipple_output_length]
  omega

end HamParity
