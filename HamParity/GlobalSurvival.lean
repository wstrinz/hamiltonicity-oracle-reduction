module

public import HamParity.PaletteGrid

@[expose] public section
namespace HamParity.MultilinearPolynomial

def goodCount {m : Nat} (p : MultilinearPolynomial m) (D : Nat) : Nat :=
  (paletteGrid D m).countP (fun w => (p.eval (fun e => (w e).val)).nonzeroB)

theorem goodCount_step_lower {m : Nat} (p : MultilinearPolynomial (m+1)) (D : Nat) :
    (p.part true).goodCount D*(D-1) ≤ p.goodCount D := by
  unfold goodCount
  rw [paletteGrid,List.countP_flatMap]
  rw [← sum_map_mul_indicator]
  apply sum_map_le
  intro a ha
  simp only [Function.comp_apply]
  rw [List.countP_map]
  cases hq : ((p.part true).eval (fun e => (a e).val)).nonzeroB with
  | false => simp [hq]
  | true =>
      simp only [hq,ite_true]
      simpa only [Function.comp_def,eval,Fin.cases_zero,Fin.cases_succ] using
        BinaryPolynomial.monomial_trial_survival_count
          ((p.part true).eval (fun e => (a e).val))
          ((p.part false).eval (fun e => (a e).val))
          (BinaryPolynomial.nonzeroB_iff _ |>.mp hq) D

theorem goodCount_zero_part {m : Nat} (p : MultilinearPolynomial (m+1)) (D : Nat)
    (hq : ¬ (p.part true).Nonzero) : p.goodCount D=(p.part false).goodCount D*D := by
  unfold goodCount
  rw [paletteGrid,List.countP_flatMap]
  rw [← sum_map_mul_indicator]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  simp only [Function.comp_apply]
  rw [List.countP_map]
  have he : (fun j : Fin D => (p.eval (fun e => (Fin.cases (motive := fun _ => Fin D) j a e).val)).nonzeroB) =
      (fun _ : Fin D => ((p.part false).eval (fun e => (a e).val)).nonzeroB) := by
    funext j
    exact p.eval_ignore_zero_part hq _
  change (List.finRange D).countP (fun j => (p.eval (fun e => (Fin.cases (motive := fun _ => Fin D) j a e).val)).nonzeroB)=_
  rw [he]
  cases h : ((p.part false).eval (fun e => (a e).val)).nonzeroB <;> simp [h]

/-- Denominator-free form of the degree-sensitive survival probability.
The grid has D^m distinct complete assignments; dividing gives (1-1/D)^d.
No evaluated-nonzero premise is supplied: it is counted in the induction. -/
theorem global_survival_count {m : Nat} (p : MultilinearPolynomial m) (d D : Nat)
    (hD : 2≤D) (hn : p.Nonzero) (hd : p.degreeLE d) :
    D^m*(D-1)^d ≤ p.goodCount D*D^d := by
  induction m generalizing d with
  | zero =>
      obtain ⟨s,hs⟩ := hn
      have he : s=Fin.elim0 := by funext i; exact Fin.elim0 i
      have hp : p Fin.elim0=true := he ▸ hs
      have hg : p.goodCount D=1 := by
        simp [goodCount,paletteGrid,eval,hp,List.countP_cons,BinaryPolynomial.nonzeroB,
          BinaryPolynomial.monomial]
      rw [hg]
      simpa using Nat.pow_le_pow_left (by omega : D-1≤D) d
  | succ m ih =>
      by_cases hq : (p.part true).Nonzero
      · have hpos := p.degree_positive_of_part_true hd hq
        obtain ⟨k,rfl⟩ : ∃ k,d=k+1 := ⟨d-1,by omega⟩
        have hi := ih (p.part true) k hq (p.part_true_degree hd)
        have hl := p.goodCount_step_lower D
        calc
          D^(m+1)*(D-1)^(k+1) = (D^m*(D-1)^k)*(D*(D-1)) := by
            simp [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          _ ≤ ((p.part true).goodCount D*D^k)*(D*(D-1)) := Nat.mul_le_mul_right _ hi
          _ = ((p.part true).goodCount D*(D-1))*D^(k+1) := by
            simp [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          _ ≤ p.goodCount D*D^(k+1) := Nat.mul_le_mul_right _ hl
      · have hr := p.part_false_nonzero hn hq
        have hi := ih (p.part false) d hr (p.part_false_degree hd)
        rw [p.goodCount_zero_part D hq]
        calc
          D^(m+1)*(D-1)^d = (D^m*(D-1)^d)*D := by
            simp [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          _ ≤ ((p.part false).goodCount D*D^d)*D := Nat.mul_le_mul_right _ hi
          _ = ((p.part false).goodCount D*D)*D^d := by
            simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

end HamParity.MultilinearPolynomial
