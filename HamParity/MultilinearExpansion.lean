module

public import HamParity.GlobalSurvival

@[expose] public section
namespace HamParity

theorem heapValue_eq_sum {m : Nat} (xs : List (WeightedWire m)) (s : Assignment m) :
    heapValue xs s=(xs.map (fun z => 2^z.1*bitValue (s z.2))).sum := by
  induction xs with
  | nil => rfl
  | cons z xs ih => simp [heapValue,ih]

theorem edgeWeight_cons {m : Nat} (w : Fin (m+1) → Nat) (b : Bool) (s : Assignment m) :
    edgeWeight w (consAssignment b s) =
      (if b then 2^(w 0) else 0) + edgeWeight (fun i => w i.succ) s := by
  cases b <;> simp [edgeWeight,edgeWeightHeap,heapValue_eq_sum,List.finRange_succ,
    List.map_map,Function.comp_def,bitValue] <;> rfl

namespace MultilinearPolynomial

/-- Expansion into squarefree monomials, with concrete integer exponents. -/
theorem eval_coeff {m : Nat} (p : MultilinearPolynomial m) (w : Fin m → Nat) (t : Nat) :
    (p.eval w).coeff t = decide ((assignments m).countP
      (fun s => p s && decide (edgeWeight w s=t))%2=1) := by
  induction m generalizing t with
  | zero =>
      cases hp : p Fin.elim0 <;> by_cases ht : t=0 <;>
        simp [eval,hp,ht,assignments,List.countP_cons,edgeWeight,edgeWeightHeap,
          heapValue,BinaryPolynomial.monomial,BinaryPolynomial.zero,eq_comm]
  | succ m ih =>
      let wt : Fin m → Nat := fun i => w i.succ
      let q := p.part true
      let r := p.part false
      let k := 2^(w 0)
      have hr := ih r wt t
      have hq := ih q wt (t-k)
      have hf : (assignments m).countP (fun s => p (consAssignment false s) &&
          decide (edgeWeight w (consAssignment false s)=t)) =
          (assignments m).countP (fun s => r s && decide (edgeWeight wt s=t)) := by
        apply List.countP_congr
        intro s hs
        simp [r,part,edgeWeight_cons,wt]
      have ht : (assignments m).countP (fun s => p (consAssignment true s) &&
          decide (edgeWeight w (consAssignment true s)=t)) =
          if k≤t then (assignments m).countP (fun s => q s && decide (edgeWeight wt s=t-k)) else 0 := by
        by_cases hk : k≤t
        · rw [if_pos hk]
          apply List.countP_congr
          intro s hs
          have he : edgeWeight w (consAssignment true s)=t ↔ edgeWeight wt s=t-k := by
            rw [edgeWeight_cons]
            change k+edgeWeight wt s=t ↔ edgeWeight wt s=t-k
            omega
          simp only [he]
          rfl
        · rw [if_neg hk]
          apply List.countP_eq_zero.mpr
          intro s hs hh
          have he : edgeWeight w (consAssignment true s)=t := by
            exact of_decide_eq_true (Bool.and_eq_true_iff.mp hh).2
          rw [edgeWeight_cons] at he
          change k+edgeWeight wt s=t at he
          omega
      simp only [assignments,List.countP_append,List.countP_map,Function.comp_def]
      rw [hf,ht]
      change (((q.eval wt).shift k).add (r.eval wt)).coeff t=_
      rw [BinaryPolynomial.add_coeff,hr]
      by_cases hk : k≤t
      · simp only [BinaryPolynomial.shift,if_pos hk]
        rw [hq]
        simpa [Nat.add_comm] using BinaryPolynomial.parity_xor
          ((assignments m).countP (fun s => q s && decide (edgeWeight wt s=t-k)))
          ((assignments m).countP (fun s => r s && decide (edgeWeight wt s=t)))
      · simp [BinaryPolynomial.shift,hk]

end MultilinearPolynomial
end HamParity
