module
public import HamParity.FairBitGrid

@[expose] public section
namespace HamParity.Schedule

theorem paletteWidth_power (L : Nat) (hL : 0<L) : paletteWidth (2^L)=L := by
  have hp : 0<2^L := Nat.pow_pos (by decide)
  have hu := massWidth_le_of_lt_pow (s:=2^L-1) (w:=L) (by omega)
  have he : 2^(L-1)<2^L := Nat.pow_lt_pow_right (by decide) (by omega)
  have hl := column_lt_massWidth (s:=2^L-1) (k:=L-1) (by omega)
  unfold paletteWidth
  omega

theorem scheduled_paletteWidth (n : Nat) : paletteWidth (palette n)=bits n :=
  paletteWidth_power _ (bits_pos n)

end HamParity.Schedule

namespace HamParity.IndexedGraph
variable {n m : Nat}

/-- Finite fair-bit semantics; no implementation or machine-cost claim. -/
def scheduledBitRun (G : IndexedGraph n m) (root : Fin n) (oracle : CountOracle)
    (xs : List (FairBits.TrialBits (Schedule.bits n) m)) : OracleTranscript :=
  G.repeatedRun root (Schedule.palette n) oracle (FairBits.decodeTrials (Schedule.bits n) xs)

theorem scheduledBitRun_no_false_positive (G : IndexedGraph n m) (hs : G.Simple) (root : Fin n)
    (oracle : CountOracle) (ho : ExactCountOracle oracle)
    (xs : List (FairBits.TrialBits (Schedule.bits n) m))
    (ha : (G.scheduledBitRun root oracle xs).accepted=true) : Nonempty G.inputGraph.CyclicOrder :=
  G.repeatedRun_no_false_positive hs root _ oracle ho _ ha

theorem scheduledBitRun_failure (G : IndexedGraph n m) (hs : G.Simple) (root : Fin n)
    (hC : Nonempty G.inputGraph.CyclicOrder) (oracle : CountOracle) (ho : ExactCountOracle oracle) :
    uniformProbability (repeatGrid (FairBits.grid (Schedule.bits n) m) (Schedule.trials n))
      (fun xs => !(G.scheduledBitRun root oracle xs).accepted)≤natRatio 1 3 := by
  have he := FairBits.repeated_event_probability (Schedule.bits n) m (Schedule.trials n)
    (fun ws => !(G.repeatedRun root (Schedule.palette n) oracle ws).accepted)
  change uniformProbability (repeatGrid (FairBits.grid (Schedule.bits n) m) (Schedule.trials n))
      (fun xs => !(G.scheduledBitRun root oracle xs).accepted)=_ at he
  rw [he]
  exact G.scheduled_failure_bound hs root hC oracle ho

theorem scheduledBitRun_calls (G : IndexedGraph n m) (root : Fin n) (oracle : CountOracle)
    (xs : List (FairBits.TrialBits (Schedule.bits n) m))
    (hx : xs∈repeatGrid (FairBits.grid (Schedule.bits n) m) (Schedule.trials n)) :
    (G.scheduledBitRun root oracle xs).calls=Schedule.trials n*(n*2^(Schedule.palette n-1)+1) := by
  have h := G.repeatedRun_calls root (2^(Schedule.bits n)) oracle (FairBits.decodeTrials (Schedule.bits n) xs)
  simp only [FairBits.decodeTrials,List.length_map,repeatGrid_member_length _ _ xs hx] at h
  simpa only [scheduledBitRun,Schedule.palette,FairBits.decodeTrials] using h

theorem scheduledBitRun_query_bound (G : IndexedGraph n m) (root : Fin n) (oracle : CountOracle)
    (xs : List (FairBits.TrialBits (Schedule.bits n) m))
    (hx : xs∈repeatGrid (FairBits.grid (Schedule.bits n) m) (Schedule.trials n)) :
    (G.scheduledBitRun root oracle xs).calls≤(n+1)*2^(6*((n-1).sqrt)+7) := by
  rw [G.scheduledBitRun_calls root oracle xs hx]
  exact Schedule.query_sqrt_bound n

theorem scheduled_fair_sample_count (n m : Nat) :
    (repeatGrid (FairBits.grid (Schedule.bits n) m) (Schedule.trials n)).length=
      2^(Schedule.trials n*m*Schedule.bits n) := FairBits.fair_sample_count _ _ _

theorem scheduled_variables (G : IndexedGraph n m) (w : Fin m → Fin (Schedule.palette n)) :
    (G.graphArithmetic (fun e => (w e).val)).wires≤
      28*m+2*n+2+5*(2*((n-1).sqrt+1)+(m+1).log2+1) := by
  have h := G.weightedGraph_palette_variables (fun e => (w e).val) (Schedule.palette n) (fun e => (w e).isLt)
  have hd := Schedule.palette_root_upper n
  omega

theorem scheduled_clauses (G : IndexedGraph n m) (root : Fin n)
    (w : Fin m → Fin (Schedule.palette n)) (t : Nat) :
    (G.weightedGraphCNF root (fun e => (w e).val) t).length≤
      108*m+6*n+19*(2*((n-1).sqrt+1)+(m+1).log2+1)+4 := by
  have h := G.weightedGraph_palette_clauses root (fun e => (w e).val) t (Schedule.palette n) (fun e => (w e).isLt)
  have hd := Schedule.palette_root_upper n
  omega

end HamParity.IndexedGraph
