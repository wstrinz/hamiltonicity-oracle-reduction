module

public import HamParity.SelectedCardinality

@[expose] public section
namespace HamParity.IndexedGraph
variable {n m : Nat}

/-- Distinct squarefree monomials are indexed by their edge-selection functions.
This is the actual finite family, not cyclic orders with multiplicity. -/
noncomputable def cycleMonomials (G : IndexedGraph n m) : List (Assignment m) :=
  (assignments m).filter G.cyclicSelectionB

theorem cycleMonomials_nodup (G : IndexedGraph n m) : G.cycleMonomials.Nodup :=
  (assignments_nodup m).filter _

theorem mem_cycleMonomials (G : IndexedGraph n m) (s : Assignment m) :
    s ∈ G.cycleMonomials ↔ G.cyclicSelectionB s=true := by
  simp [cycleMonomials,assignments_complete]

theorem cycleMonomials_nonempty_iff (G : IndexedGraph n m) (hs : G.Simple) (root : Fin n) :
    (∃ s, s ∈ G.cycleMonomials) ↔ Nonempty G.inputGraph.CyclicOrder := by
  constructor
  · rintro ⟨s,hm⟩
    obtain ⟨_,⟨C⟩⟩ := (G.cyclicSelectionB_iff s).mp ((G.mem_cycleMonomials s).mp hm)
    exact G.selectedCyclicOrder_input s C
  · rintro ⟨C⟩
    refine ⟨G.cycleSelection C,(G.mem_cycleMonomials _).mpr ?_⟩
    rw [← G.connectedDegreeTwoB_eq_cyclicSelectionB hs root]
    apply (G.connectedDegreeTwoB_iff _).mpr
    exact ⟨(G.degreeTwoB_iff _).mp (G.cycleSelection_degreeTwoB C hs),G.cycleSelection_connected C⟩

theorem cycleMonomials_weight_range (G : IndexedGraph n m) (s : Assignment m)
    (hm : s ∈ G.cycleMonomials) (weights : Fin m → Nat) (D : Nat)
    (hD : 0<D) (hw : ∀ e, weights e<D) : edgeWeight weights s≤n*2^(D-1) := by
  obtain ⟨hd,_⟩ := (G.cyclicSelectionB_iff s).mp ((G.mem_cycleMonomials s).mp hm)
  exact G.degreeTwo_weight_range s ((G.degreeTwoB_iff s).mpr hd) weights D hD hw

end HamParity.IndexedGraph
