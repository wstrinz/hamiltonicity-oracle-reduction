module

public import HamParity.SurvivalStep

@[expose] public section
namespace HamParity

/-- A coefficient for each squarefree edge-set monomial, not a list of cycles. -/
abbrev MultilinearPolynomial (m : Nat) := Assignment m → Bool

namespace MultilinearPolynomial

def Nonzero {m : Nat} (p : MultilinearPolynomial m) : Prop := ∃ s, p s=true
def degreeLE {m : Nat} (p : MultilinearPolynomial m) (d : Nat) : Prop :=
  ∀ s, p s=true → (List.finRange m).countP s ≤ d
def part {m : Nat} (p : MultilinearPolynomial (m+1)) (b : Bool) : MultilinearPolynomial m :=
  fun s => p (consAssignment b s)

def eval : {m : Nat} → MultilinearPolynomial m → (Fin m → Nat) → BinaryPolynomial
  | 0,p,_ => if p Fin.elim0 then BinaryPolynomial.monomial 0 else BinaryPolynomial.zero
  | _+1,p,w => BinaryPolynomial.monomialTrial (eval (p.part true) (fun i => w i.succ))
      (eval (p.part false) (fun i => w i.succ)) (w 0)

theorem popcount_cons {m : Nat} (b : Bool) (s : Assignment m) :
    (List.finRange (m+1)).countP (consAssignment b s) =
      (if b then 1 else 0) + (List.finRange m).countP s := by
  cases b <;> simp [List.finRange_succ,List.countP_cons,List.countP_map,Function.comp_def,Nat.add_comm]

theorem part_false_degree {m d : Nat} (p : MultilinearPolynomial (m+1))
    (h : p.degreeLE d) : (p.part false).degreeLE d := by
  intro s hs
  simpa [popcount_cons] using h (consAssignment false s) hs

theorem part_true_degree {m d : Nat} (p : MultilinearPolynomial (m+1))
    (h : p.degreeLE (d+1)) : (p.part true).degreeLE d := by
  intro s hs
  have hh := h (consAssignment true s) hs
  rw [popcount_cons] at hh
  simp only [Bool.true_eq,ite_true] at hh
  omega

theorem degree_positive_of_part_true {m d : Nat} (p : MultilinearPolynomial (m+1))
    (h : p.degreeLE d) (hn : (p.part true).Nonzero) : 0<d := by
  obtain ⟨s,hs⟩ := hn
  have hh := h (consAssignment true s) hs
  rw [popcount_cons] at hh
  simp only [Bool.true_eq,ite_true] at hh
  omega

theorem part_false_nonzero {m : Nat} (p : MultilinearPolynomial (m+1))
    (hn : p.Nonzero) (hq : ¬ (p.part true).Nonzero) : (p.part false).Nonzero := by
  obtain ⟨s,hs⟩ := hn
  cases hz : s 0 with
  | false => exact ⟨tailAssignment s,by simpa [part,← hz] using hs⟩
  | true => exact False.elim (hq ⟨tailAssignment s,by simpa [part,← hz] using hs⟩)

theorem coeff_false_of_not_nonzero {m : Nat} (p : MultilinearPolynomial m)
    (h : ¬ p.Nonzero) (s : Assignment m) : p s=false := by
  cases hs : p s with
  | false => rfl
  | true => exact False.elim (h ⟨s,hs⟩)

theorem eval_zero {m : Nat} (p : MultilinearPolynomial m) (h : ¬p.Nonzero)
    (w : Fin m → Nat) : ∀ i, (p.eval w).coeff i=false := by
  induction m with
  | zero =>
      intro i
      simp [eval,coeff_false_of_not_nonzero p h]
      rfl
  | succ m ih =>
      have hp (b : Bool) : ¬ (p.part b).Nonzero := by
        rintro ⟨s,hs⟩
        exact h ⟨consAssignment b s,hs⟩
      have hq := ih (p.part true) (hp true) (fun j => w j.succ)
      have hr := ih (p.part false) (hp false) (fun j => w j.succ)
      intro i
      simp [eval,BinaryPolynomial.monomialTrial,BinaryPolynomial.add_coeff,
        BinaryPolynomial.shift,hq,hr]

theorem eval_ignore_zero_part {m : Nat} (p : MultilinearPolynomial (m+1))
    (hq : ¬ (p.part true).Nonzero) (w : Fin (m+1) → Nat) :
    (p.eval w).nonzeroB = ((p.part false).eval (fun i => w i.succ)).nonzeroB := by
  have hc (i : Nat) : (p.eval w).coeff i=((p.part false).eval (fun j => w j.succ)).coeff i := by
    simp [eval,BinaryPolynomial.monomialTrial,BinaryPolynomial.add_coeff,
      BinaryPolynomial.shift,eval_zero _ hq]
  apply Bool.eq_iff_iff.mpr
  rw [BinaryPolynomial.nonzeroB_iff,BinaryPolynomial.nonzeroB_iff]
  unfold BinaryPolynomial.Nonzero
  simp only [hc]

end MultilinearPolynomial
end HamParity
