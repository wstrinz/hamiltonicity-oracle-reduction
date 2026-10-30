module

public import HamParity.GraphWeightInputs

@[expose] public section
namespace HamParity.IndexedGraph
variable {n m : Nat}

abbrev graphArithmetic (G : IndexedGraph n m) (weights : Fin m → Nat) :=
  buildWeighted (G.graphWeightHeap weights)

def weightedGraphCircuit (G : IndexedGraph n m) (weights : Fin m → Nat) :
    Circuit (m+n) (G.graphArithmetic weights).wires :=
  G.generalCircuit.compose (G.graphArithmetic weights).circuit

def weightedGraphConstraints (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) : CNF (G.graphArithmetic weights).wires :=
  (batchConstraints G.generalRows (G.selectionCutCNF root)).rename
    (G.graphArithmetic weights).circuit.inputWire ++
    bucketPins (G.graphArithmetic weights).output t

/-- Actual composed clauses; old graph constraints are transported to the same
final wire space, while edge and color primaries retain their identity. -/
def weightedGraphCNF (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) : CNF (G.graphArithmetic weights).wires :=
  (G.weightedGraphCircuit weights).clauses ++ G.weightedGraphConstraints root weights t

def weightedGraphValid (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) (a : Assignment (m+n)) : Bool :=
  G.generalPrimaryValid root a && decide (edgeWeight weights (leftAssignment a)=t)

theorem weightedGraphValid_join (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) (s : Assignment m) (colors : Assignment n) :
    G.weightedGraphValid root weights t (joinAssignment s colors) =
      ((G.degreeTwoB s && (G.selectedGraph s).rootedValidB root colors) &&
        decide (edgeWeight weights s=t)) := by
  rw [weightedGraphValid, G.generalPrimaryValid_join, left_join]

theorem weightedGraphConstraints_eval (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) (a : Assignment (m+n)) :
    (G.weightedGraphConstraints root weights t).eval ((G.weightedGraphCircuit weights).eval a) =
      G.weightedGraphValid root weights t a := by
  have hp : (bucketPins (G.graphArithmetic weights).output t).eval
      ((G.graphArithmetic weights).circuit.eval (G.generalCircuit.eval a)) =
        decide (edgeWeight weights (leftAssignment a)=t) := by
    apply Bool.eq_iff_iff.mpr
    rw [bucketPins_eval_iff, buildWeighted_value, G.graphWeightHeap_eval]
    simp
  simp only [weightedGraphConstraints, weightedGraphCircuit, Circuit.eval_compose,
    eval_append, eval_rename, Circuit.eval_inputWire, hp]
  change ((batchConstraints G.generalRows (G.selectionCutCNF root)).eval
    ((buildRows G.generalRows).circuit.eval a) && _) = _
  rw [batchConstraints_eval]
  rfl

theorem weightedGraphCNF_eval_extension (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) (a : Assignment (m+n)) :
    (G.weightedGraphCNF root weights t).eval ((G.weightedGraphCircuit weights).eval a) =
      G.weightedGraphValid root weights t a := by
  simp only [weightedGraphCNF, eval_append, Circuit.eval_satisfies,
    Bool.true_and, G.weightedGraphConstraints_eval]

theorem weightedGraphCNF_satisfies_iff (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) (a : Assignment (G.graphArithmetic weights).wires) :
    (G.weightedGraphCNF root weights t).eval a = true ↔
      a = (G.weightedGraphCircuit weights).eval ((G.weightedGraphCircuit weights).inputs a) ∧
      G.weightedGraphValid root weights t ((G.weightedGraphCircuit weights).inputs a) = true := by
  rw [weightedGraphCNF, Circuit.with_constraints]
  constructor
  · rintro ⟨he,hq⟩
    refine ⟨he,?_⟩
    rwa [he, G.weightedGraphConstraints_eval] at hq
  · rintro ⟨he,hv⟩
    refine ⟨he,?_⟩
    rwa [he, G.weightedGraphConstraints_eval]

theorem weightedGraphCNF_count_primary (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) :
    modelCount (G.weightedGraphCNF root weights t) =
      (assignments (m+n)).countP (G.weightedGraphValid root weights t) := by
  rw [weightedGraphCNF, Circuit.constrained_model_count]
  apply List.countP_congr
  intro a _
  rw [G.weightedGraphConstraints_eval]

theorem weightedGraphCNF_unique_extension (G : IndexedGraph n m) (root : Fin n)
    (weights : Fin m → Nat) (t : Nat) (s : Assignment m) (colors : Assignment n)
    (hd : G.degreeTwoB s=true) (hc : (G.selectedGraph s).rootedValidB root colors=true)
    (ht : edgeWeight weights s=t) :
    ∃ a : Assignment (G.graphArithmetic weights).wires,
      (G.weightedGraphCNF root weights t).eval a=true ∧
      (G.weightedGraphCircuit weights).inputs a=joinAssignment s colors ∧
      ∀ b, (G.weightedGraphCNF root weights t).eval b=true →
        (G.weightedGraphCircuit weights).inputs b=joinAssignment s colors → b=a := by
  refine ⟨(G.weightedGraphCircuit weights).eval (joinAssignment s colors),?_,
    Circuit.inputs_eval _ _,?_⟩
  · rw [G.weightedGraphCNF_eval_extension, G.weightedGraphValid_join]
    simp [hd,hc,ht]
  · intro b hb hx
    have he := ((G.weightedGraphCNF_satisfies_iff root weights t b).mp hb).1
    simpa only [hx] using he

/-- All old graph wires, including graph helpers and colors, are disjoint from
all newly allocated arithmetic helpers. -/
theorem weightedGraph_old_new_disjoint (G : IndexedGraph n m) (weights : Fin m → Nat) :
    ∀ i j, (G.graphArithmetic weights).circuit.inputWire i ≠
      (G.graphArithmetic weights).circuit.helperWire j :=
  (G.graphArithmetic weights).circuit.input_helper_disjoint

end HamParity.IndexedGraph
