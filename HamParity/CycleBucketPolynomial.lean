module

public import HamParity.CycleMonomials

@[expose] public section
namespace HamParity.IndexedGraph
variable {n m : Nat}

/-- Actual F2 sum of the univariate monomials z^(edgeWeight s), one per
duplicate-free cyclic edge selection. Equal weights cancel by coefficient XOR. -/
noncomputable def cycleBucketPolynomial (G : IndexedGraph n m) (weights : Fin m → Nat) :
    BinaryPolynomial := BinaryPolynomial.sumMonomials (G.cycleMonomials.map (edgeWeight weights))

theorem cycleBucketPolynomial_coeff (G : IndexedGraph n m) (weights : Fin m → Nat) (t : Nat) :
    (G.cycleBucketPolynomial weights).coeff t =
      decide ((assignments m).countP (fun s => G.cyclicSelectionB s && decide (edgeWeight weights s=t)) % 2=1) := by
  rw [cycleBucketPolynomial,BinaryPolynomial.sumMonomials_coeff,List.countP_map]
  unfold cycleMonomials
  rw [List.countP_filter]
  congr 2
  apply congrArg (fun c : Nat => c%2)
  apply List.countP_congr
  intro s _
  simp [Function.comp_def,beq_iff_eq,Bool.and_comm]

theorem cycleBucketPolynomial_coeff_CNF (G : IndexedGraph n m) (hs : G.Simple)
    (root : Fin n) (weights : Fin m → Nat) (t : Nat) :
    (G.cycleBucketPolynomial weights).coeff t =
      decide (modelCount (G.weightedGraphCNF root weights t)%2=1) := by
  rw [G.cycleBucketPolynomial_coeff,G.weightedGraphCNF_cyclic_parity hs root]

theorem cycleBucketPolynomial_nonzero_iff_odd_bucket (G : IndexedGraph n m) (hs : G.Simple)
    (root : Fin n) (weights : Fin m → Nat) :
    (G.cycleBucketPolynomial weights).Nonzero ↔
      ∃ t, modelCount (G.weightedGraphCNF root weights t)%2=1 := by
  unfold BinaryPolynomial.Nonzero
  simp only [G.cycleBucketPolynomial_coeff_CNF hs root,decide_eq_true_eq]

theorem cycleBucketPolynomial_outside_range (G : IndexedGraph n m) (weights : Fin m → Nat)
    (D : Nat) (hD : 0<D) (hw : ∀ e, weights e<D) (t : Nat) (ht : n*2^(D-1)<t) :
    (G.cycleBucketPolynomial weights).coeff t=false := by
  rw [cycleBucketPolynomial,BinaryPolynomial.sumMonomials_coeff,List.countP_map]
  have hz : G.cycleMonomials.countP (fun s => edgeWeight weights s==t)=0 := by
    apply List.countP_eq_zero.mpr
    intro s hm he
    have hb := G.cycleMonomials_weight_range s hm weights D hD hw
    have heq : edgeWeight weights s=t := beq_iff_eq.mp he
    omega
  simpa [Function.comp_def,hz]

theorem nonzero_cyclePolynomial_has_bounded_odd_bucket (G : IndexedGraph n m) (hs : G.Simple)
    (root : Fin n) (weights : Fin m → Nat) (D : Nat) (hD : 0<D)
    (hw : ∀ e, weights e<D) (hn : (G.cycleBucketPolynomial weights).Nonzero) :
    ∃ t, t≤n*2^(D-1) ∧ modelCount (G.weightedGraphCNF root weights t)%2=1 := by
  obtain ⟨t,ht⟩ := hn
  have hb : t≤n*2^(D-1) := by
    by_cases h : t≤n*2^(D-1)
    · exact h
    · have hz := G.cycleBucketPolynomial_outside_range weights D hD hw t (by omega)
      simp [hz] at ht
  refine ⟨t,hb,?_⟩
  rw [G.cycleBucketPolynomial_coeff_CNF hs root] at ht
  exact of_decide_eq_true ht

end HamParity.IndexedGraph
