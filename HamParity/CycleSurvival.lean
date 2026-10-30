module

public import HamParity.MultilinearExpansion

@[expose] public section
namespace HamParity.IndexedGraph
variable {n m : Nat}

/-- One Boolean coefficient per edge subset, regardless of orientations/orders. -/
noncomputable def cyclePolynomial (G : IndexedGraph n m) : MultilinearPolynomial m :=
  G.cyclicSelectionB

theorem cyclePolynomial_nonzero (G : IndexedGraph n m) (hs : G.Simple) (root : Fin n)
    (hC : Nonempty G.inputGraph.CyclicOrder) : G.cyclePolynomial.Nonzero := by
  obtain ⟨s,hm⟩ := (G.cycleMonomials_nonempty_iff hs root).mpr hC
  exact ⟨s,(G.mem_cycleMonomials s).mp hm⟩

theorem cyclePolynomial_degree (G : IndexedGraph n m) : G.cyclePolynomial.degreeLE n := by
  intro s hs
  obtain ⟨hd,_⟩ := (G.cyclicSelectionB_iff s).mp hs
  exact Nat.le_of_eq (G.degreeTwo_selected_cardinality s ((G.degreeTwoB_iff s).mpr hd))

theorem cyclePolynomial_eval_coeff (G : IndexedGraph n m) (w : Fin m → Nat) (t : Nat) :
    (G.cyclePolynomial.eval w).coeff t=(G.cycleBucketPolynomial w).coeff t := by
  rw [MultilinearPolynomial.eval_coeff,G.cycleBucketPolynomial_coeff]
  rfl

theorem cyclePolynomial_eval_nonzero (G : IndexedGraph n m) (w : Fin m → Nat) :
    (G.cyclePolynomial.eval w).Nonzero ↔ (G.cycleBucketPolynomial w).Nonzero := by
  unfold BinaryPolynomial.Nonzero
  simp only [G.cyclePolynomial_eval_coeff]

/-- Finite search predicate on the same actual emitted weighted CNF formulas. -/
noncomputable def boundedOddBucketB (G : IndexedGraph n m) (root : Fin n)
    (D : Nat) (w : Fin m → Fin D) : Bool :=
  (List.range (n*2^(D-1)+1)).any (fun t =>
    decide (modelCount (G.weightedGraphCNF root (fun e => (w e).val) t)%2=1))

theorem boundedOddBucketB_iff (G : IndexedGraph n m) (root : Fin n)
    (D : Nat) (w : Fin m → Fin D) : G.boundedOddBucketB root D w=true ↔
      ∃ t, t≤n*2^(D-1) ∧ modelCount (G.weightedGraphCNF root (fun e => (w e).val) t)%2=1 := by
  simp only [boundedOddBucketB,List.any_eq_true,List.mem_range,decide_eq_true_eq]
  constructor <;> rintro ⟨t,ht,hc⟩ <;> exact ⟨t,by omega,hc⟩

theorem boundedOddBucketB_eq_eval (G : IndexedGraph n m) (hs : G.Simple) (root : Fin n)
    (D : Nat) (hD : 0<D) (w : Fin m → Fin D) :
    G.boundedOddBucketB root D w=(G.cyclePolynomial.eval (fun e => (w e).val)).nonzeroB := by
  apply Bool.eq_iff_iff.mpr
  rw [G.boundedOddBucketB_iff,BinaryPolynomial.nonzeroB_iff,G.cyclePolynomial_eval_nonzero]
  constructor
  · rintro ⟨t,_,ht⟩
    exact (G.cycleBucketPolynomial_nonzero_iff_odd_bucket hs root _).mpr ⟨t,ht⟩
  · intro hn
    exact G.nonzero_cyclePolynomial_has_bounded_odd_bucket hs root _ D hD
      (fun e => (w e).isLt) hn

/-- Exact finite counting form of Hamiltonian survival at least (1-1/D)^n.
The counted domain is all D^m independent edge-only exponent assignments.
No nonzero-after-substitution hypothesis occurs. -/
theorem hamiltonian_bounded_odd_bucket_survival (G : IndexedGraph n m) (hs : G.Simple)
    (root : Fin n) (hC : Nonempty G.inputGraph.CyclicOrder) (D : Nat) (hD : 2≤D) :
    D^m*(D-1)^n ≤ (paletteGrid D m).countP (G.boundedOddBucketB root D)*D^n := by
  have hg := MultilinearPolynomial.global_survival_count G.cyclePolynomial n D hD
    (G.cyclePolynomial_nonzero hs root hC) G.cyclePolynomial_degree
  have he : (paletteGrid D m).countP (G.boundedOddBucketB root D)=G.cyclePolynomial.goodCount D := by
    apply List.countP_congr
    intro w hw
    rw [G.boundedOddBucketB_eq_eval hs root D (by omega) w]
  rwa [he]

theorem hamiltonian_exists_bounded_odd_bucket (G : IndexedGraph n m) (hs : G.Simple)
    (root : Fin n) (hC : Nonempty G.inputGraph.CyclicOrder) (D : Nat) (hD : 2≤D) :
    ∃ w : Fin m → Fin D, ∃ t, t≤n*2^(D-1) ∧
      modelCount (G.weightedGraphCNF root (fun e => (w e).val) t)%2=1 := by
  have hb := G.hamiltonian_bounded_odd_bucket_survival hs root hC D hD
  have hp : 0<D^m*(D-1)^n := Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  have hc : 0<(paletteGrid D m).countP (G.boundedOddBucketB root D) := by
    by_cases h : (paletteGrid D m).countP (G.boundedOddBucketB root D)=0
    · simp [h] at hb
      omega
    · omega
  obtain ⟨w,_,hw⟩ := List.countP_pos_iff.mp hc
  exact ⟨w,(G.boundedOddBucketB_iff root D w).mp hw⟩

end HamParity.IndexedGraph
