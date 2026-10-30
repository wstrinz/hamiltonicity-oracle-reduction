module
public import HamParity.CanonicalGraphBridge
public import HamParity.RandomnessDescription
public import Init.Data.Nat.Sqrt

@[expose] public section
namespace HamParity.Schedule

def bits (n : Nat) : Nat := max 1 (massWidth ((n-1).sqrt))
def palette (n : Nat) : Nat := 2^(bits n)
def trials (n : Nat) : Nat := 2*4^(palette n)

theorem bits_pos (n : Nat) : 0<bits n := by unfold bits; omega
theorem palette_ge_two (n : Nat) : 2≤palette n := by
  change 2^1≤2^(bits n)
  exact Nat.pow_le_pow_right (by decide) (bits_pos n)
theorem palette_even (n : Nat) : palette n=2*(2^(bits n-1)) := by
  have h := bits_pos n
  change 2^(bits n)=2*(2^(bits n-1))
  calc
    2^(bits n)=2^((bits n-1)+1) := congrArg (fun k => 2^k) (by omega)
    _ = _ := by rw [Nat.pow_succ,Nat.mul_comm]

theorem massWidth_power_lower (s : Nat) : s<2^(massWidth s) := by
  by_cases h : s=0
  · simp [h,massWidth]
  · simpa [massWidth,h] using (Nat.lt_log2_self (n:=s))

theorem massWidth_power_upper (s : Nat) : 2^(massWidth s)≤2*(s+1) := by
  by_cases h : s=0
  · simp [h,massWidth]
  · have hs := Nat.log2_self_le h
    simp only [massWidth,if_neg h,Nat.pow_succ]
    omega

theorem palette_root_lower (n : Nat) : (n-1).sqrt+1≤palette n := by
  have h := massWidth_power_lower ((n-1).sqrt)
  have he := Nat.pow_le_pow_right (n:=2) (by decide) (Nat.le_max_right 1 (massWidth ((n-1).sqrt)))
  change 2^(massWidth ((n-1).sqrt))≤palette n at he
  omega

theorem palette_root_upper (n : Nat) : palette n≤2*((n-1).sqrt+1) := by
  by_cases h : massWidth ((n-1).sqrt)≤1
  · have he : bits n=1 := by unfold bits; omega
    simp only [palette,he]; omega
  · have he : bits n=massWidth ((n-1).sqrt) := by unfold bits; omega
    rw [palette,he]
    exact massWidth_power_upper _

theorem vertex_square_bound (n : Nat) : n≤palette n*palette n := by
  have hs := Nat.lt_succ_sqrt (n-1)
  simp only [Nat.succ_eq_add_one] at hs
  have hp := Nat.mul_le_mul (palette_root_lower n) (palette_root_lower n)
  omega

/-- Denominator-cleared Bernoulli bound, valid also at exponent zero. -/
theorem bernoulli_scaled (d k : Nat) (hd : 1≤d) :
    d^k*d≤(d-1)^k*d+k*d^k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hm := Nat.mul_le_mul_right (d-1) ih
      have ht := Nat.mul_le_mul_left (k*d^k) (Nat.sub_le d 1)
      have he : d=(d-1)+1 := by omega
      calc
        d^(k+1)*d = (d^k*d)*(d-1)+d^k*d := by
          rw [Nat.pow_succ]
          calc
            (d^k*d)*d=(d^k*d)*((d-1)+1) := congrArg (fun z => (d^k*d)*z) he
            _ = _ := by rw [Nat.mul_add,Nat.mul_one]
        _ ≤ ((d-1)^k*d+k*d^k)*(d-1)+d^k*d := Nat.add_le_add_right hm _
        _ ≤ (d-1)^(k+1)*d+(k+1)*d^(k+1) := by
          have hsum := Nat.add_le_add_right (Nat.add_le_add_left ht ((d-1)^k*d*(d-1))) (d^k*d)
          simpa only [Nat.add_mul,Nat.mul_add,Nat.pow_succ,Nat.mul_one,Nat.one_mul,
            Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc] using hsum

theorem half_block (a : Nat) (ha : 0<a) : (2*a)^a≤2*(2*a-1)^a := by
  have h := bernoulli_scaled (2*a) a (by omega)
  apply Nat.le_of_mul_le_mul_left (c:=a) _ ha
  have he1 : (2*a)^a*(2*a)=2*(a*(2*a)^a) := by ac_rfl
  have he2 : (2*a-1)^a*(2*a)=2*(a*(2*a-1)^a) := by ac_rfl
  have he3 : a*(2*(2*a-1)^a)=2*(a*(2*a-1)^a) := by ac_rfl
  rw [he1,he2] at h
  rw [he3]
  omega

theorem even_block (a : Nat) (ha : 0<a) : (2*a)^(2*a)≤4*(2*a-1)^(2*a) := by
  have h := Nat.pow_le_pow_left (half_block a ha) 2
  simpa only [Nat.mul_pow,← Nat.pow_mul,Nat.mul_comm a 2] using h

theorem ratio_power_down (a b K M n : Nat) (hb : 0<b) (hba : b≤a) (hn : n≤M)
    (h : a^M≤K*b^M) : a^n≤K*b^n := by
  have he : n+(M-n)=M := by omega
  have hs := Nat.mul_le_mul_left (a^n) (Nat.pow_le_pow_left hba (M-n))
  rw [← Nat.pow_add,he] at hs
  have ht := Nat.le_trans hs h
  have hbpow : b^M=b^n*b^(M-n) := by rw [← Nat.pow_add,he]
  rw [hbpow] at ht
  exact Nat.le_of_mul_le_mul_right (c:=b^(M-n)) (by simpa only [Nat.mul_assoc] using ht) (Nat.pow_pos hb)

theorem survival_denominator_bound (n : Nat) :
    (palette n)^n≤4^(palette n)*(palette n-1)^n := by
  let a := 2^(bits n-1)
  have ha : 0<a := Nat.pow_pos (by decide)
  have he : palette n=2*a := palette_even n
  have hblock : (palette n)^(palette n)≤4*(palette n-1)^(palette n) := by
    simpa only [he] using even_block a ha
  have h := Nat.pow_le_pow_left hblock (palette n)
  simp only [Nat.mul_pow,← Nat.pow_mul] at h
  exact ratio_power_down _ _ _ _ _ (by have := palette_ge_two n; omega)
    (Nat.sub_le _ _) (vertex_square_bound n) h

theorem trials_power (n : Nat) : trials n=2^(2*palette n+1) := by
  simp [trials,Nat.pow_add,Nat.pow_mul,Nat.mul_comm]

theorem query_bound (n : Nat) : trials n*(n*2^(palette n-1)+1)≤(n+1)*2^(3*palette n+1) := by
  have hp : 1≤2^(palette n) := Nat.one_le_pow _ _ (by decide)
  have he : 2^(palette n-1)≤2^(palette n) := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hb : n*2^(palette n-1)+1≤(n+1)*2^(palette n) := by
    have hm := Nat.mul_le_mul_left n he
    simp only [Nat.add_mul,Nat.one_mul]; omega
  have h := Nat.mul_le_mul_left (trials n) hb
  rw [trials_power] at h
  have hx : 2^(2*palette n+1)*((n+1)*2^(palette n))=(n+1)*2^(3*palette n+1) := by
    rw [Nat.mul_left_comm,← Nat.pow_add]
    congr 2; omega
  rw [hx] at h
  simpa only [trials_power] using h

theorem query_sqrt_bound (n : Nat) :
    trials n*(n*2^(palette n-1)+1)≤(n+1)*2^(6*((n-1).sqrt)+7) := by
  apply Nat.le_trans (query_bound n)
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by decide)
  have h := palette_root_upper n
  omega

end HamParity.Schedule
