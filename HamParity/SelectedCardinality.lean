module

public import HamParity.BinaryMonomialSurvival

@[expose] public section
namespace HamParity

theorem sum_map_constant (xs : List α) (c : Nat) : (xs.map (fun _ => c)).sum=xs.length*c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_mul,Nat.add_comm]

theorem heapValue_le_selected_bound {p : Nat} (xs : List (WeightedWire p))
    (a : Assignment p) (B : Nat) (h : ∀ z ∈ xs, 2^z.1≤B) :
    heapValue xs a ≤ xs.countP (fun z => a z.2)*B := by
  induction xs with
  | nil => simp [heapValue]
  | cons z xs ih =>
      have hz := h z (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      cases ha : a z.2 <;> simp [heapValue,List.countP_cons,ha,bitValue,Nat.add_mul] at * <;> omega

theorem edgeWeight_palette_bound {m : Nat} (weights : Fin m → Nat) (s : Assignment m)
    (D : Nat) (hD : 0<D) (hw : ∀ e, weights e<D) :
    edgeWeight weights s ≤ (List.finRange m).countP s * 2^(D-1) := by
  have h := heapValue_le_selected_bound (edgeWeightHeap weights) s (2^(D-1)) (by
    intro z hz
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hz
    exact Nat.pow_le_pow_right (by decide) (by have he := hw e; omega))
  simpa [edgeWeight,edgeWeightHeap,List.countP_map,Function.comp_def] using h

namespace IndexedGraph
variable {n m : Nat}

theorem selectedDegree_filtered (G : IndexedGraph n m) (s : Assignment m) (v : Fin n) :
    G.selectedDegree s v =
      ((List.finRange m).filter s).countP (fun e => (G.endpoints e).1==v) +
      ((List.finRange m).filter s).countP (fun e => (G.endpoints e).2==v) := by
  simp only [selectedDegree,incidences,List.countP_append,List.countP_filter]
  simp [Bool.and_comm]

theorem selected_incidence_total (G : IndexedGraph n m) (s : Assignment m) :
    ((List.finRange n).map (G.selectedDegree s)).sum=2*(List.finRange m).countP s := by
  change ((List.finRange n).map (fun v => G.selectedDegree s v)).sum=2*(List.finRange m).countP s
  simp only [G.selectedDegree_filtered,sum_map_nat_add,sum_fin_fibers]
  simp only [← List.countP_eq_length_filter]
  omega

/-- Includes loops twice and parallel indexed edges separately; no simplicity
assumption is needed for incidence double-counting. -/
theorem degreeTwo_selected_cardinality (G : IndexedGraph n m) (s : Assignment m)
    (hd : G.degreeTwoB s=true) : (List.finRange m).countP s=n := by
  have ht := G.selected_incidence_total s
  have hs : ((List.finRange n).map (G.selectedDegree s)).sum=2*n := by
    have he : (List.finRange n).map (G.selectedDegree s)=(List.finRange n).map (fun _ => 2) := by
      apply List.map_congr_left
      intro v _
      exact (G.degreeTwoB_iff s).mp hd v
    rw [he,sum_map_constant,List.length_finRange]
    omega
  omega

theorem degreeTwo_weight_range (G : IndexedGraph n m) (s : Assignment m)
    (hd : G.degreeTwoB s=true) (weights : Fin m → Nat) (D : Nat)
    (hD : 0<D) (hw : ∀ e, weights e<D) : edgeWeight weights s≤n*2^(D-1) := by
  have h := edgeWeight_palette_bound weights s D hD hw
  rwa [G.degreeTwo_selected_cardinality s hd] at h

end IndexedGraph
end HamParity
