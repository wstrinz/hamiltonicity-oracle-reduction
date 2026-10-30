module

public import HamParity.CycleSurvival
public import Init.Data.Rat

@[expose] public section
namespace HamParity

/-- Exact rational ratio; probability uses it only with a positive denominator. -/
def natRatio (a b : Nat) : Rat := mkRat a b

theorem natRatio_eq_div (a b : Nat) : natRatio a b=(a : Rat)/(b : Rat) := by
  exact Rat.mkRat_eq_div _ _

theorem natRatio_le {a b c d : Nat} (hb : 0<b) (hd : 0<d)
    (h : a*d≤c*b) : natRatio a b≤natRatio c d := by
  have hb' : (0 : Rat)<(b : Rat) := Rat.natCast_lt_natCast.mpr hb
  have hd' : (0 : Rat)<(d : Rat) := Rat.natCast_lt_natCast.mpr hd
  rw [natRatio_eq_div,natRatio_eq_div]
  apply Rat.le_of_mul_le_mul_right (c := (b : Rat)) _ hb'
  apply Rat.le_of_mul_le_mul_right (c := (d : Rat)) _ hd'
  calc
    ((a : Rat)/(b : Rat)*(b : Rat))*(d : Rat) = (a : Rat)*(d : Rat) := by
      rw [Rat.div_mul_cancel (Rat.ne_of_gt hb')]
    _ ≤ (c : Rat)*(b : Rat) := by
      simpa only [Rat.natCast_mul] using Rat.natCast_le_natCast.mpr h
    _ = ((c : Rat)/(d : Rat)*(b : Rat))*(d : Rat) := by
      rw [Rat.mul_assoc,Rat.mul_comm (b : Rat) (d : Rat),← Rat.mul_assoc,
        Rat.div_mul_cancel (Rat.ne_of_gt hd')]

theorem natRatio_mul (a b c d : Nat) : natRatio a b*natRatio c d=natRatio (a*c) (b*d) := by
  simp only [natRatio,Rat.mkRat_mul_mkRat,Int.natCast_mul]

theorem natRatio_pow (a b k : Nat) : (natRatio a b)^k=natRatio (a^k) (b^k) := by
  induction k with
  | zero => simp only [Rat.pow_zero,Nat.pow_zero]; decide
  | succ k ih => rw [Rat.pow_succ,ih,natRatio_mul,Nat.pow_succ,Nat.pow_succ]

theorem natRatio_self {b : Nat} (hb : 0<b) : natRatio b b=1 := by
  simpa only [natRatio,← Rat.divInt_ofNat] using
    Rat.divInt_self' (Int.ne_of_gt (Int.natCast_pos.mpr hb))

theorem natRatio_zero (b : Nat) : natRatio 0 b=0 := by
  simp [natRatio]

/-- Uniform probability on an explicit finite sample list. No claim of uniformity
on an executable bit sampler is made. Applications prove positive length and Nodup. -/
def uniformProbability {α : Type} (samples : List α) (event : α → Bool) : Rat :=
  natRatio (samples.countP event) samples.length

theorem uniformProbability_true {α : Type} (samples : List α) (hn : 0<samples.length) :
    uniformProbability samples (fun _ => true)=1 := by
  simpa [uniformProbability] using natRatio_self hn

theorem uniformProbability_false {α : Type} (samples : List α) :
    uniformProbability samples (fun _ => false)=0 := by simp [uniformProbability,natRatio_zero]

theorem uniformProbability_bounds {α : Type} (samples : List α) (event : α → Bool)
    (hn : 0<samples.length) :
    0≤uniformProbability samples event ∧ uniformProbability samples event≤1 := by
  constructor
  · have h := natRatio_le (a:=0) (b:=1) (c:=samples.countP event) (d:=samples.length)
      (by decide) hn (by omega)
    simpa [uniformProbability,natRatio_zero] using h
  · have h := natRatio_le (b:=samples.length) (d:=1) hn (by decide)
      (a:=samples.countP event) (c:=1) (by simpa using List.countP_le_length (p:=event) (l:=samples))
    rw [natRatio_self (by decide : 0<1)] at h
    exact h

theorem countP_complement {α : Type} (samples : List α) (event : α → Bool) :
    samples.countP event+samples.countP (fun x => !event x)=samples.length := by
  have h := List.length_eq_countP_add_countP event (l:=samples)
  have he : samples.countP (fun x => decide (¬event x=true))=samples.countP (fun x => !event x) := by
    apply List.countP_congr
    intro x hx
    cases he : event x <;> simp [he]
  rw [he] at h
  exact h.symm

end HamParity
