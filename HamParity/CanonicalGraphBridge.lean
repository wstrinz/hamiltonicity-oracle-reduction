module

public import HamParity.CanonicalLength

@[expose] public section
namespace HamParity.Canonical

abbrev CanonicalOracle := Input → Nat
def ExactCanonicalOracle (counter : CanonicalOracle) : Prop :=
  ∀ F, F.WellFormed → counter F=F.count
def liftOracle (counter : CanonicalOracle) : CountOracle := fun f => counter (adapt f)

/-- Interface theorem only: correctness of the external counter remains an
explicit oracle premise, not an imported machine theorem. -/
theorem liftOracle_exact (counter : CanonicalOracle) (hc : ExactCanonicalOracle counter) :
    ExactCountOracle (liftOracle counter) := by
  intro v f
  exact (hc (adapt f) (adapt_wellFormed f)).trans (adapt_count f)

end HamParity.Canonical

namespace HamParity.IndexedGraph
open Canonical
variable {n m : Nat}

/-- Canonical numeric finite-set representative, not an external Finset import. -/
def canonicalQuery (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) : Canonical.Input :=
  adapt (G.weightedGraphCNF root weights t)

theorem canonicalQuery_variables (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    (G.canonicalQuery root weights t).variables =
      23*m+2*n+5*G.graphWeightSteps weights+2+5*G.graphWeightWidth weights :=
  G.weightedGraph_variables weights

theorem canonicalQuery_wellFormed (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    (G.canonicalQuery root weights t).WellFormed := adapt_wellFormed _

theorem canonicalQuery_width (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    (G.canonicalQuery root weights t).WidthAtMost 3 :=
  adapt_width _ (G.weightedGraphCNF_width root weights t)

theorem canonicalQuery_eval (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) (a : Assignment (G.graphArithmetic weights).wires) :
    (G.canonicalQuery root weights t).eval a=(G.weightedGraphCNF root weights t).eval a :=
  adapt_eval _ _

theorem canonicalQuery_count (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    (G.canonicalQuery root weights t).count = modelCount (G.weightedGraphCNF root weights t) :=
  adapt_count _

theorem canonicalQuery_exact_count (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    (G.canonicalQuery root weights t).count =
      ((assignments m).map (fun s =>
        if G.degreeTwoB s && decide (edgeWeight weights s=t)
        then 2^((G.selectedGraph s).componentCount-1) else 0)).sum := by
  rw [G.canonicalQuery_count]
  exact G.weightedGraphCNF_exact_count root weights t

theorem canonicalQuery_cyclic_parity (G : IndexedGraph n m) (hs : G.Simple) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    (G.canonicalQuery root weights t).count % 2 =
      (assignments m).countP (fun s => G.cyclicSelectionB s && decide (edgeWeight weights s=t)) % 2 := by
  rw [G.canonicalQuery_count]
  exact G.weightedGraphCNF_cyclic_parity hs root weights t

theorem canonicalQuery_odd_sound (G : IndexedGraph n m) (hs : G.Simple) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) (h : (G.canonicalQuery root weights t).count % 2=1) :
    Nonempty G.inputGraph.CyclicOrder := by
  rw [G.canonicalQuery_count] at h
  exact G.odd_weightedGraphCNF_input_cyclicOrder hs root weights t h

theorem canonicalQuery_clause_bound (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    (G.canonicalQuery root weights t).clauses.length ≤
      90*m+6*n+18*G.graphWeightSteps weights+19*G.graphWeightWidth weights+4 :=
  Nat.le_trans (adapt_clause_count _) (G.weightedGraphCNF_clause_bound root weights t)

theorem canonicalQuery_encode_length (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    (G.canonicalQuery root weights t).encode.length ≤
      (G.graphArithmetic weights).wires+2+(24*(G.graphArithmetic weights).wires+16)*
      (90*m+6*n+18*G.graphWeightSteps weights+19*G.graphWeightWidth weights+4) := by
  exact Nat.le_trans (adapt_three_encode_length _ (G.weightedGraphCNF_width root weights t))
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (G.weightedGraphCNF_clause_bound root weights t)) _)

theorem canonicalQuery_encoded_header (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    readNat (G.canonicalQuery root weights t).encode =
      some ((G.graphArithmetic weights).wires,
        encodeList (encodeList encodeNat) (G.canonicalQuery root weights t).clauses) :=
  readNat_encode _

end HamParity.IndexedGraph
