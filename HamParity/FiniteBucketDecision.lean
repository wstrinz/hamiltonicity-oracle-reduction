module

public import HamParity.FiniteProbability

@[expose] public section
namespace HamParity

abbrev CountOracle := {v : Nat} → CNF v → Nat
def ExactCountOracle (oracle : CountOracle) : Prop := ∀ {v} (f : CNF v), oracle f=modelCount f
def exactModelOracle : CountOracle := fun f => modelCount f
theorem exactModelOracle_correct : ExactCountOracle exactModelOracle := fun _ => rfl

structure OracleQuery where
  variables : Nat
  formula : CNF variables

structure OracleTranscript where
  answers : List Nat
  accepted : Bool
  calls : Nat

/-- Instrumented full scan: one charged oracle query and one recorded answer
per input formula, regardless of an earlier odd answer. This is an abstract
oracle cost model, not a statement about a compiled machine's execution. -/
def scanOracle (oracle : CountOracle) : List OracleQuery → OracleTranscript
  | [] => ⟨[],false,0⟩
  | q::qs =>
      let answer := oracle q.formula
      let tail := scanOracle oracle qs
      ⟨answer::tail.answers,decide (answer%2=1) || tail.accepted,tail.calls+1⟩

theorem scanOracle_calls (oracle : CountOracle) (qs : List OracleQuery) :
    (scanOracle oracle qs).calls=qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [scanOracle,ih]

theorem scanOracle_answers (oracle : CountOracle) (qs : List OracleQuery) :
    (scanOracle oracle qs).answers=qs.map (fun q => oracle q.formula) := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [scanOracle,ih]

theorem scanOracle_accepted (oracle : CountOracle) (qs : List OracleQuery) :
    (scanOracle oracle qs).accepted=qs.any (fun q => decide (oracle q.formula%2=1)) := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [scanOracle,ih]

namespace IndexedGraph
variable {n m : Nat}

def bucketQueries (G : IndexedGraph n m) (root : Fin n) (D : Nat) (w : Fin m → Fin D) :
    List OracleQuery := (List.range (n*2^(D-1)+1)).map (fun t =>
      ⟨(G.graphArithmetic (fun e => (w e).val)).wires,
        G.weightedGraphCNF root (fun e => (w e).val) t⟩)

def trialRun (G : IndexedGraph n m) (root : Fin n) (D : Nat) (oracle : CountOracle)
    (w : Fin m → Fin D) : OracleTranscript := scanOracle oracle (G.bucketQueries root D w)

theorem trialRun_calls (G : IndexedGraph n m) (root : Fin n) (D : Nat)
    (oracle : CountOracle) (w : Fin m → Fin D) :
    (G.trialRun root D oracle w).calls=n*2^(D-1)+1 := by
  simp [trialRun,scanOracle_calls,bucketQueries]

theorem trialRun_eq_bucket (G : IndexedGraph n m) (root : Fin n) (D : Nat)
    (oracle : CountOracle) (ho : ExactCountOracle oracle) (w : Fin m → Fin D) :
    (G.trialRun root D oracle w).accepted=G.boundedOddBucketB root D w := by
  unfold ExactCountOracle at ho
  simp [trialRun,scanOracle_accepted,bucketQueries,List.any_map,boundedOddBucketB,ho,Function.comp_def]

theorem trialRun_no_false_positive (G : IndexedGraph n m) (hs : G.Simple) (root : Fin n)
    (D : Nat) (oracle : CountOracle) (ho : ExactCountOracle oracle) (w : Fin m → Fin D)
    (ha : (G.trialRun root D oracle w).accepted=true) : Nonempty G.inputGraph.CyclicOrder := by
  rw [G.trialRun_eq_bucket root D oracle ho w] at ha
  obtain ⟨t,_,ht⟩ := (G.boundedOddBucketB_iff root D w).mp ha
  exact G.odd_weightedGraphCNF_input_cyclicOrder hs root _ t ht

theorem trialRun_success_probability (G : IndexedGraph n m) (hs : G.Simple) (root : Fin n)
    (hC : Nonempty G.inputGraph.CyclicOrder) (D : Nat) (hD : 2≤D)
    (oracle : CountOracle) (ho : ExactCountOracle oracle) :
    natRatio ((D-1)^n) (D^n) ≤
      uniformProbability (paletteGrid D m) (fun w => (G.trialRun root D oracle w).accepted) := by
  have he : (fun w => (G.trialRun root D oracle w).accepted)=G.boundedOddBucketB root D := by
    funext w; exact G.trialRun_eq_bucket root D oracle ho w
  rw [he,uniformProbability,paletteGrid_length]
  apply natRatio_le (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  simpa [Nat.mul_comm] using G.hamiltonian_bounded_odd_bucket_survival hs root hC D hD

end IndexedGraph
end HamParity
