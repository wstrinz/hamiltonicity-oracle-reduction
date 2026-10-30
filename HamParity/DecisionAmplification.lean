module

public import HamParity.IndependentTrials

@[expose] public section
namespace HamParity

theorem failure_cross_bound {α : Type} (xs : List α) (p : α → Bool) (a b : Nat)
    (h : xs.length*a≤xs.countP p*b) :
    xs.countP (fun x => !p x)*b≤xs.length*(b-a) := by
  have hp := countP_complement xs p
  have he : xs.countP p*b+xs.countP (fun x => !p x)*b=xs.length*b := by
    rw [← Nat.add_mul,hp]
  rw [Nat.mul_sub]
  omega

theorem repeated_failure_probability {α : Type} (xs : List α) (p : α → Bool) (k : Nat) :
    uniformProbability (repeatGrid xs k) (fun ys => !ys.any p)=
      (uniformProbability xs (fun x => !p x))^k := by
  rw [uniformProbability,repeatGrid_failure_count,repeatGrid_length]
  exact (natRatio_pow _ _ _).symm

theorem amplified_failure_bound {α : Type} (xs : List α) (p : α → Bool) (a b k : Nat)
    (hN : 0<xs.length) (hb : 0<b) (h : xs.length*a≤xs.countP p*b) :
    uniformProbability (repeatGrid xs k) (fun ys => !ys.any p)≤(natRatio (b-a) b)^k := by
  have hf := failure_cross_bound xs p a b h
  have hk := Nat.pow_le_pow_left hf k
  rw [uniformProbability,repeatGrid_failure_count,repeatGrid_length,natRatio_pow]
  apply natRatio_le (Nat.pow_pos hN) (Nat.pow_pos hb)
  simpa only [Nat.mul_pow,Nat.mul_comm] using hk

namespace IndexedGraph
variable {n m : Nat}

def repeatedQueries (G : IndexedGraph n m) (root : Fin n) (D : Nat)
    (ws : List (Fin m → Fin D)) : List OracleQuery := ws.flatMap (G.bucketQueries root D)

def repeatedRun (G : IndexedGraph n m) (root : Fin n) (D : Nat) (oracle : CountOracle)
    (ws : List (Fin m → Fin D)) : OracleTranscript := scanOracle oracle (G.repeatedQueries root D ws)

theorem repeatedRun_calls (G : IndexedGraph n m) (root : Fin n) (D : Nat) (oracle : CountOracle)
    (ws : List (Fin m → Fin D)) :
    (G.repeatedRun root D oracle ws).calls=ws.length*(n*2^(D-1)+1) := by
  simp [repeatedRun,repeatedQueries,scanOracle_calls,List.length_flatMap,
    bucketQueries,Function.comp_def,sum_map_constant]

theorem repeatedRun_accepted (G : IndexedGraph n m) (root : Fin n) (D : Nat)
    (oracle : CountOracle) (ws : List (Fin m → Fin D)) :
    (G.repeatedRun root D oracle ws).accepted=ws.any (fun w => (G.trialRun root D oracle w).accepted) := by
  simp [repeatedRun,repeatedQueries,trialRun,scanOracle_accepted,List.any_flatMap,Function.comp_def]

theorem repeatedRun_no_false_positive (G : IndexedGraph n m) (hs : G.Simple) (root : Fin n)
    (D : Nat) (oracle : CountOracle) (ho : ExactCountOracle oracle) (ws : List (Fin m → Fin D))
    (ha : (G.repeatedRun root D oracle ws).accepted=true) : Nonempty G.inputGraph.CyclicOrder := by
  rw [G.repeatedRun_accepted,List.any_eq_true] at ha
  obtain ⟨w,_,hw⟩ := ha
  exact G.trialRun_no_false_positive hs root D oracle ho w hw

theorem repeatedRun_query_count (G : IndexedGraph n m) (root : Fin n) (D k : Nat)
    (oracle : CountOracle) (ws : List (Fin m → Fin D)) (hw : ws∈repeatGrid (paletteGrid D m) k) :
    (G.repeatedRun root D oracle ws).calls=k*(n*2^(D-1)+1) := by
  rw [G.repeatedRun_calls,repeatGrid_member_length _ k ws hw]

theorem repeatedRun_failure_exact (G : IndexedGraph n m) (root : Fin n) (D k : Nat)
    (oracle : CountOracle) :
    uniformProbability (repeatGrid (paletteGrid D m) k)
      (fun ws => !(G.repeatedRun root D oracle ws).accepted)=
      (uniformProbability (paletteGrid D m) (fun w => !(G.trialRun root D oracle w).accepted))^k := by
  simp only [G.repeatedRun_accepted]
  exact repeated_failure_probability _ _ k

/-- Independent repetition in the complete finite product sample space.
The bound is (1 - ((D-1)/D)^n)^k, represented by exact rational powers. -/
theorem repeatedRun_failure_bound (G : IndexedGraph n m) (hs : G.Simple) (root : Fin n)
    (hC : Nonempty G.inputGraph.CyclicOrder) (D k : Nat) (hD : 2≤D)
    (oracle : CountOracle) (ho : ExactCountOracle oracle) :
    uniformProbability (repeatGrid (paletteGrid D m) k)
      (fun ws => !(G.repeatedRun root D oracle ws).accepted)≤
      (natRatio (D^n-(D-1)^n) (D^n))^k := by
  simp only [G.repeatedRun_accepted]
  apply amplified_failure_bound _ _ ((D-1)^n) (D^n) k
  · rw [paletteGrid_length]; exact Nat.pow_pos (by omega)
  · exact Nat.pow_pos (by omega)
  · have he : (fun w => (G.trialRun root D oracle w).accepted)=G.boundedOddBucketB root D := by
      funext w; exact G.trialRun_eq_bucket root D oracle ho w
    rw [he,paletteGrid_length]
    exact G.hamiltonian_bounded_odd_bucket_survival hs root hC D hD

end IndexedGraph
end HamParity
