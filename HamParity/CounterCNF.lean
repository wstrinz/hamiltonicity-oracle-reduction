module

public import HamParity.CounterBuild

@[expose] public section

namespace HamParity

def counterConstraints {n : Nat} (xs : List (Fin n)) : CNF (buildCounter xs).wires :=
  [[⟨(buildCounter xs).two, true⟩], [⟨(buildCounter xs).three, false⟩]]

def exactTwoCounterCNF {n : Nat} (xs : List (Fin n)) : CNF (buildCounter xs).wires :=
  (buildCounter xs).circuit.clauses ++ counterConstraints xs

theorem counterConstraints_eval {n : Nat} (xs : List (Fin n)) (a : Assignment n) :
    (counterConstraints xs).eval ((buildCounter xs).circuit.eval a) =
      (xs.countP a == 2) := by
  simp only [counterConstraints, CNF.eval, Clause.eval, Literal.eval,
    List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.and_true]
  change (((buildCounter xs).valueTwo a == true) &&
    ((buildCounter xs).valueThree a == false)) = _
  rw [(buildCounter_flags xs a).2.1, (buildCounter_flags xs a).2.2]
  apply Bool.eq_iff_iff.mpr
  simp
  omega

/-- Counts all original primary assignments; repeated row wires count repeated
incidences. Every added counter wire is a deterministic gate helper. -/
theorem exactTwoCounterCNF_count {n : Nat} (xs : List (Fin n)) :
    modelCount (exactTwoCounterCNF xs) =
      (assignments n).countP (fun a => xs.countP a == 2) := by
  rw [exactTwoCounterCNF, Circuit.constrained_model_count]
  apply List.countP_congr
  intro a _
  rw [counterConstraints_eval]

theorem exactTwoCounterCNF_satisfies_iff {n : Nat} (xs : List (Fin n))
    (a : Assignment (buildCounter xs).wires) :
    (exactTwoCounterCNF xs).eval a = true ↔
      a = (buildCounter xs).circuit.eval ((buildCounter xs).circuit.inputs a) ∧
      xs.countP ((buildCounter xs).circuit.inputs a) = 2 := by
  rw [exactTwoCounterCNF, Circuit.with_constraints]
  constructor
  · rintro ⟨he, hq⟩
    refine ⟨he, ?_⟩
    rw [he, counterConstraints_eval] at hq
    exact beq_iff_eq.mp hq
  · rintro ⟨he, hx⟩
    refine ⟨he, ?_⟩
    rw [he, counterConstraints_eval]
    exact beq_iff_eq.mpr hx

theorem exactTwoCounterCNF_unique_extension {n : Nat} (xs : List (Fin n))
    (x : Assignment n) (hx : xs.countP x = 2) :
    ∃ a : Assignment (buildCounter xs).wires,
      (exactTwoCounterCNF xs).eval a = true ∧ (buildCounter xs).circuit.inputs a = x ∧
      ∀ b, (exactTwoCounterCNF xs).eval b = true →
        (buildCounter xs).circuit.inputs b = x → b = a := by
  refine ⟨(buildCounter xs).circuit.eval x, ?_, Circuit.inputs_eval _ _, ?_⟩
  · rw [exactTwoCounterCNF_satisfies_iff, Circuit.inputs_eval]
    exact ⟨rfl, hx⟩
  · intro b hb hi
    have he := ((exactTwoCounterCNF_satisfies_iff xs b).mp hb).1
    simpa [hi] using he

theorem exactTwoCounterCNF_width {n : Nat} (xs : List (Fin n)) :
    WidthAtMost 3 (exactTwoCounterCNF xs) := by
  apply width_append (buildCounter xs).circuit.width
  simp [counterConstraints, WidthAtMost]

theorem exactTwoCounterCNF_clause_bound {n : Nat} (xs : List (Fin n)) :
    (exactTwoCounterCNF xs).length ≤ 44 * xs.length + 6 := by
  have h := (buildCounter xs).circuit.clause_count
  rw [buildCounter_gates] at h
  simp only [exactTwoCounterCNF, List.length_append, counterConstraints,
    List.length_cons, List.length_nil]
  omega

theorem exactTwoCounter_four_count :
    modelCount (exactTwoCounterCNF (List.finRange 4)) = 6 := by
  rw [exactTwoCounterCNF_count]
  decide

theorem exactTwoCounter_repeated_count :
    modelCount (exactTwoCounterCNF ([0, 0, 1, 1] : List (Fin 2))) = 2 := by
  rw [exactTwoCounterCNF_count]
  decide

theorem exactTwoCounter_empty_count :
    modelCount (exactTwoCounterCNF ([] : List (Fin 2))) = 0 := by
  rw [exactTwoCounterCNF_count]
  decide

end HamParity
