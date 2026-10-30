module

public import HamParity.BinaryPolynomial

@[expose] public section
namespace HamParity

theorem countP_le_one_of_unique {α : Type} (xs : List α) (p : α → Bool)
    (hn : xs.Nodup) (hu : ∀ x ∈ xs, ∀ y ∈ xs, p x=true → p y=true → x=y) :
    xs.countP p ≤ 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      obtain ⟨hx,ht⟩ := List.nodup_cons.mp hn
      cases hp : p x with
      | false =>
          simp only [List.countP_cons,hp,Bool.false_eq_true,ite_false,Nat.zero_add]
          exact ih ht (fun a ha b hb => hu a (by simp [ha]) b (by simp [hb]))
      | true =>
          have hz : xs.countP p=0 := List.countP_eq_zero.mpr (by
            intro y hy hpy
            have he := hu x (by simp) y (by simp [hy]) hp hpy
            exact hx (he ▸ hy))
          simp [List.countP_cons,hp,hz]

namespace BinaryPolynomial

/-- A concrete one-variable evaluation X*Q+R at X=z^(2^r). -/
def monomialTrial (q r : BinaryPolynomial) (j : Nat) : BinaryPolynomial :=
  (q.shift (2^j)).add r

theorem at_most_one_canceling_choice (q r : BinaryPolynomial) (hq : q.Nonzero)
    (a b : Nat) (ha : (monomialTrial q r a).nonzeroB=false)
    (hb : (monomialTrial q r b).nonzeroB=false) : a=b := by
  have hqa := (add_zero_iff _ _).mp ha
  have hqb := (add_zero_iff _ _).mp hb
  have hp : 2^a=2^b := q.shifts_distinct hq _ _ (fun i => (hqa i).trans (hqb i).symm)
  have hab : a≤b := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (Nat.le_of_eq hp)
  have hba : b≤a := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (Nat.le_of_eq hp.symm)
  omega

/-- Exact finite-grid version of the one-variable survival factor. For D>0,
division by D gives probability at least 1-1/D under uniform sampling. -/
theorem monomial_trial_survival_count (q r : BinaryPolynomial) (hq : q.Nonzero) (D : Nat) :
    D-1 ≤ (List.finRange D).countP (fun j => (monomialTrial q r j.val).nonzeroB) := by
  let good : Fin D → Bool := fun j => (monomialTrial q r j.val).nonzeroB
  have hb : (List.finRange D).countP (fun j => !good j) ≤ 1 := by
    apply countP_le_one_of_unique _ _ (List.nodup_finRange D)
    intro a _ b _ ha hb
    have ha' : (monomialTrial q r a.val).nonzeroB=false := by simpa [good] using ha
    have hb' : (monomialTrial q r b.val).nonzeroB=false := by simpa [good] using hb
    exact Fin.ext (at_most_one_canceling_choice q r hq _ _ ha' hb')
  have hc := List.length_eq_countP_add_countP good (l := List.finRange D)
  simp only [List.length_finRange] at hc
  have hn : (List.finRange D).countP (fun j => decide (¬good j=true)) =
      (List.finRange D).countP (fun j => !good j) := by
    apply List.countP_congr
    intro j _
    cases hj : good j <;> simp [hj]
  rw [hn] at hc
  change D-1 ≤ (List.finRange D).countP good
  omega

end BinaryPolynomial
end HamParity
