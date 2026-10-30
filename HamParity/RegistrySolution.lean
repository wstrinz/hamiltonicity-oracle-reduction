module
public import HamParity.RegistryBridge

@[expose] public section
namespace HamiltonicityOracle


def toQuery {v : Nat} (f : HamParity.CNF v) : Query := ⟨v,translate f⟩
def liftOracle (oracle : Oracle) : HamParity.CountOracle := fun f => oracle (toQuery f)
theorem liftOracle_exact (oracle : Oracle) (ho : Exact oracle) :
    HamParity.ExactCountOracle (liftOracle oracle) := by
  intro v f
  exact (ho (toQuery f)).trans (translate_count f)

def query {n m : Nat} (E : Edges n m) (root : Fin n) (w : Fin m → Nat) (t : Nat) : Query :=
  toQuery ((graph E).weightedGraphCNF root w t)

/-- Finite disjunction over prescribed queries, including both bucket endpoints. No execution-cost claim. -/
abbrev run {n m : Nat} (E : Edges n m) (root : Fin n) (oracle : Oracle)
    (xs : List (TrialBits (bits n) m)) : Bool :=
  xs.any (fun b => (List.range (n*2^(palette n-1)+1)).any (fun t =>
    decide (oracle (query E root (fun e => digit (bits n) (b e)) t)%2=1)))
/-- Prescribed full-scan query slots; short-circuit evaluation may use fewer. -/
def calls (n : Nat) {m : Nat} (xs : List (TrialBits (bits n) m)) : Nat :=
  xs.length*(n*2^(palette n-1)+1)

theorem run_eq {n m : Nat} (E : Edges n m) (root : Fin n) (oracle : Oracle)
    (xs : List (TrialBits (bits n) m)) :
    run E root oracle xs = ((graph E).scheduledBitRun root (liftOracle oracle) xs).accepted := by
  have h := (graph E).repeatedRun_accepted root (palette n) (liftOracle oracle)
    (HamParity.FairBits.decodeTrials (bits n) xs)
  let dec := HamParity.FairBits.decodeTrial (bits n) (m:=m)
  let pred := fun w => ((graph E).trialRun root (palette n) (liftOracle oracle) w).accepted
  have hm : (xs.map dec).any pred=xs.any (fun b => pred (dec b)) := List.any_map
  apply Eq.trans ?_ (hm.symm.trans h.symm)
  apply List.any_congr rfl
  intro b
  have ht := HamParity.scanOracle_accepted (liftOracle oracle)
    ((graph E).bucketQueries root (palette n) (dec b))
  have hm' := @List.any_map Nat HamParity.OracleQuery
    (fun t => ⟨((graph E).graphArithmetic (fun e => (dec b e).val)).wires,
      (graph E).weightedGraphCNF root (fun e => (dec b e).val) t⟩)
    (List.range (n*2^(palette n-1)+1))
    (fun q => decide (liftOracle oracle q.formula%2=1))
  apply Eq.trans ?_ (hm'.symm.trans ht.symm)
  apply List.any_congr rfl
  intro t
  have hw : (fun e => digit (bits n) (b e))=(fun e => (dec b e).val) :=
    funext (fun e => digit_eq _ _)
  exact congrArg (fun w => decide (oracle (query E root w t)%2=1)) hw

theorem calls_eq {n m : Nat} (E : Edges n m) (root : Fin n) (oracle : Oracle)
    (xs : List (TrialBits (bits n) m)) :
    calls n xs=((graph E).scheduledBitRun root (liftOracle oracle) xs).calls := by
  have h := (graph E).repeatedRun_calls root (palette n) (liftOracle oracle)
    (HamParity.FairBits.decodeTrials (bits n) xs)
  have hl := List.length_map (as:=xs) (HamParity.FairBits.decodeTrial (bits n))
  exact (congrArg (fun k => k*(n*2^(palette n-1)+1)) hl).symm.trans h.symm

theorem query_exact_count {n m : Nat} (E : Edges n m) (root : Fin n)
    (w : Fin m → Nat) (t : Nat) : count (query E root w t).formula=filteredCount E root w t := by
  exact (translate_count _).trans (filtered_eq E root w t).symm

theorem query_size {n m : Nat} (E : Edges n m) (root : Fin n)
    (w : Fin m → Nat) (hw : ∀ e, w e<palette n) (t : Nat) :
    (query E root w t).variables≤variableBound n m ∧
    (query E root w t).formula.length≤clauseBound n m ∧
    (∀ c∈(query E root w t).formula, c.length≤3) := by
  let wf : Fin m → Fin (HamParity.Schedule.palette n) := fun e => ⟨w e,hw e⟩
  refine ⟨(graph E).scheduled_variables wf, ?_, translate_width _ ((graph E).weightedGraphCNF_width root w t)⟩
  change (translate ((graph E).weightedGraphCNF root w t)).length≤clauseBound n m
  rw [translate_length]
  exact (graph E).scheduled_clauses root wf t

theorem fair_sample_space (n m : Nat) :
    (samples n m).Nodup ∧ (samples n m).length=2^(trials n*m*bits n) ∧
    (∀ xs : List (TrialBits (bits n) m), xs∈samples n m ↔ xs.length=trials n) := by
  rw [samples_eq]
  refine ⟨HamParity.repeatGrid_nodup _ (HamParity.FairBits.grid_nodup _ _) _,
    HamParity.FairBits.fair_sample_count _ _ _, ?_⟩
  intro xs
  constructor
  · exact HamParity.repeatGrid_member_length _ _ xs
  · exact repeatGrid_complete _ (HamParity.FairBits.grid_complete _) _ xs

theorem finite_oracle_reduction {n m : Nat} (E : Edges n m)
    (hs : Simple E) (root : Fin n) (hn : 3≤n) (oracle : Oracle) (ho : Exact oracle) :
    (∀ xs, run E root oracle xs=true → Hamiltonian E) ∧
    (Hamiltonian E → probability (samples n m) (fun xs => !(run E root oracle xs))≤mkRat 1 3) ∧
    (∀ xs∈samples n m, calls n xs=trials n*(n*2^(palette n-1)+1) ∧
      calls n xs≤(n+1)*2^(6*((n-1).sqrt)+7)) := by
  have hs' : (graph E).Simple := hs
  have ho' : HamParity.ExactCountOracle (liftOracle oracle) := liftOracle_exact oracle ho
  refine ⟨?_,?_,?_⟩
  · intro xs ha
    rw [run_eq] at ha
    exact (hamiltonian_iff E).mpr ((graph E).scheduledBitRun_no_false_positive hs' root _ ho' xs ha)
  · intro hH
    have h := (graph E).scheduledBitRun_failure hs' root ((hamiltonian_iff E).mp hH) _ ho'
    have hone : HamParity.natRatio 1 3=mkRat 1 3 := by decide
    rw [hone] at h
    have he : (fun xs : List (TrialBits (bits n) m) => !(run E root oracle xs)) =
        (fun xs => !((graph E).scheduledBitRun root (liftOracle oracle) xs).accepted) :=
      funext (fun xs => congrArg Bool.not (run_eq E root oracle xs))
    have hp : probability (samples n m) (fun xs => !(run E root oracle xs)) =
        HamParity.uniformProbability
          (HamParity.repeatGrid (HamParity.FairBits.grid (HamParity.Schedule.bits n) m)
            (HamParity.Schedule.trials n))
          (fun xs => !((graph E).scheduledBitRun root (liftOracle oracle) xs).accepted) := by
      exact (congrArg (probability (samples n m)) he).trans
        (congrArg (fun ss => probability ss
          (fun xs => !((graph E).scheduledBitRun root (liftOracle oracle) xs).accepted)) (samples_eq n m))
    exact hp ▸ h

  · intro xs hx
    rw [samples_eq] at hx
    rw [calls_eq E root oracle xs]
    exact ⟨(graph E).scheduledBitRun_calls root _ xs hx,
      (graph E).scheduledBitRun_query_bound root _ xs hx⟩

end HamiltonicityOracle
