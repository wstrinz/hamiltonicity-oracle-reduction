module
public import HamParity.ScheduleBounds

@[expose] public section
namespace HamParity.Schedule

theorem reciprocal_decay (q a k : Nat) :
    q^k*(q+a+k*a)≤(q+a)^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 := Nat.mul_le_mul_right q ih
      have h2 := Nat.mul_le_mul_right a (Nat.pow_le_pow_left (Nat.le_add_right q a) (k+1))
      calc
        q^(k+1)*(q+a+(k+1)*a) = (q^k*(q+a+k*a))*q+q^(k+1)*a := by
          simp only [Nat.pow_succ,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul]
          ac_rfl
        _ ≤ (q+a)^(k+1)*q+(q+a)^(k+1)*a := Nat.add_le_add h1 h2
        _ = (q+a)^(k+1+1) := by simp only [← Nat.mul_add,Nat.pow_succ]

theorem fixed_error_integer (a b C : Nat) (hb : 0<b) (hab : a≤b) (hC : b≤C*a) :
    3*(b-a)^(2*C)≤b^(2*C) := by
  have he : b-a+a=b := by omega
  have h := reciprocal_decay (b-a) a (2*C)
  rw [he] at h
  have hl : 3*b≤b+(2*C)*a := by
    simp only [Nat.mul_assoc]; omega
  have hm := Nat.mul_le_mul_left ((b-a)^(2*C)) hl
  have ht := Nat.le_trans hm h
  apply Nat.le_of_mul_le_mul_right (c:=b) _ hb
  simpa only [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using ht

theorem fixed_error_ratio (a b C : Nat) (hb : 0<b) (hab : a≤b) (hC : b≤C*a) :
    (natRatio (b-a) b)^(2*C)≤natRatio 1 3 := by
  rw [natRatio_pow]
  apply natRatio_le (Nat.pow_pos hb) (by decide)
  have h := fixed_error_integer a b C hb hab hC
  simpa only [Nat.mul_comm,Nat.one_mul] using h

theorem scheduled_failure_ratio (n : Nat) :
    (natRatio ((palette n)^n-(palette n-1)^n) ((palette n)^n))^(trials n)≤natRatio 1 3 := by
  apply fixed_error_ratio _ _ _ (Nat.pow_pos (by have := palette_ge_two n; omega))
    (Nat.pow_le_pow_left (Nat.sub_le _ _) n) (survival_denominator_bound n)

end HamParity.Schedule

namespace HamParity.IndexedGraph
variable {n m : Nat}

theorem scheduled_failure_bound (G : IndexedGraph n m) (hs : G.Simple) (root : Fin n)
    (hC : Nonempty G.inputGraph.CyclicOrder) (oracle : CountOracle) (ho : ExactCountOracle oracle) :
    uniformProbability (repeatGrid (paletteGrid (Schedule.palette n) m) (Schedule.trials n))
      (fun ws => !(G.repeatedRun root (Schedule.palette n) oracle ws).accepted)≤natRatio 1 3 := by
  exact Rat.le_trans (G.repeatedRun_failure_bound hs root hC _ _ (Schedule.palette_ge_two n) oracle ho)
    (Schedule.scheduled_failure_ratio n)

theorem scheduled_query_bound (G : IndexedGraph n m) (root : Fin n)
    (oracle : CountOracle) (ws : List (Fin m → Fin (Schedule.palette n)))
    (hw : ws∈repeatGrid (paletteGrid (Schedule.palette n) m) (Schedule.trials n)) :
    (G.repeatedRun root (Schedule.palette n) oracle ws).calls≤
      (n+1)*2^(6*((n-1).sqrt)+7) := by
  rw [G.repeatedRun_query_count root _ _ oracle ws hw]
  exact Schedule.query_sqrt_bound n

end HamParity.IndexedGraph
