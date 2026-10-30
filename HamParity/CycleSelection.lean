module

public import HamParity.CycleSelectionPositions

@[expose] public section

namespace HamParity.IndexedGraph

variable {n m : Nat} (G : IndexedGraph n m) (C : G.inputGraph.CyclicOrder)

/-- Select exactly those indexed input edges joining successive cyclic vertices,
in either orientation. Colors and helper bits are not part of this selection. -/
noncomputable def cycleSelection : Assignment m := by
  classical
  exact fun e => decide (C.nextVertex (G.endpoints e).1 = (G.endpoints e).2 ∨
    C.nextVertex (G.endpoints e).2 = (G.endpoints e).1)

theorem selected_adj_iff_index (s : Assignment m) (u v : Fin n) :
    (G.selectedGraph s).Adj u v ↔ ∃ e : Fin m, s e = true ∧
      (((G.endpoints e).1 = u ∧ (G.endpoints e).2 = v) ∨
       ((G.endpoints e).2 = u ∧ (G.endpoints e).1 = v)) := by
  rw [EdgeGraph.adj_iff]
  constructor
  · rintro ⟨p, hp, h⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    exact ⟨e, (List.mem_filter.mp he).2, h⟩
  · rintro ⟨e, he, h⟩
    exact ⟨G.endpoints e, List.mem_map.mpr ⟨e,
      List.mem_filter.mpr ⟨List.mem_finRange e, he⟩, rfl⟩, h⟩

theorem input_adj_iff_index (u v : Fin n) :
    G.inputGraph.Adj u v ↔ ∃ e : Fin m,
      (((G.endpoints e).1 = u ∧ (G.endpoints e).2 = v) ∨
       ((G.endpoints e).2 = u ∧ (G.endpoints e).1 = v)) := by
  rw [EdgeGraph.adj_iff]
  simp only [inputGraph, List.mem_map]
  constructor
  · rintro ⟨p, ⟨e, _, rfl⟩, h⟩
    exact ⟨e, h⟩
  · rintro ⟨e, h⟩
    exact ⟨G.endpoints e, ⟨e, List.mem_finRange e, rfl⟩, h⟩

theorem cycleSelection_adj_iff (u v : Fin n) :
    (G.selectedGraph (G.cycleSelection C)).Adj u v ↔
      C.nextVertex u = v ∨ C.nextVertex v = u := by
  classical
  rw [G.selected_adj_iff_index]
  constructor
  · rintro ⟨e, he, hp⟩
    have he' : C.nextVertex (G.endpoints e).1 = (G.endpoints e).2 ∨
        C.nextVertex (G.endpoints e).2 = (G.endpoints e).1 := by
      simpa only [cycleSelection, decide_eq_true_eq] using he
    rcases hp with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · simpa only [hu, hv] using he'
    · simpa only [hu, hv, or_comm] using he'
  · intro h
    have ha : G.inputGraph.Adj u v := by
      rcases h with h | h
      · rw [← h]
        exact C.nextVertex_adj u
      · rw [← h]
        exact G.inputGraph.adj_symm _ _ (C.nextVertex_adj v)
    obtain ⟨e, hp⟩ := (G.input_adj_iff_index u v).mp ha
    refine ⟨e, ?_, hp⟩
    simp only [cycleSelection, decide_eq_true_eq]
    rcases hp with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · simpa only [hu, hv] using h
    · simpa only [hu, hv, or_comm] using h

theorem cycleSelection_neighbors_iff (u v : Fin n) :
    v ∈ (G.selectedGraph (G.cycleSelection C)).neighbors u ↔
      v = C.nextVertex u ∨ v = C.prevVertex u := by
  rw [← EdgeGraph.Adj, G.cycleSelection_adj_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by rw [← h, C.prev_next_vertex])
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, C.next_prev_vertex])

/-- Simplicity supplies absence of repeated neighbor incidences; no input degree
bound is used. Every selected vertex has precisely its successor and predecessor. -/
theorem cycleSelection_degree (hs : G.Simple) (v : Fin n) :
    (G.selectedGraph (G.cycleSelection C)).incidenceDegree v = 2 := by
  let xs := (G.selectedGraph (G.cycleSelection C)).neighbors v
  let ys := [C.nextVertex v, C.prevVertex v]
  have hx : xs.Nodup := (G.selected_simple hs (G.cycleSelection C) v).1
  have hy : ys.Nodup := by simp [ys, C.nextVertex_ne_prevVertex]
  have hxy : xs ⊆ ys := by
    intro w hw
    simpa [ys] using
      (G.cycleSelection_neighbors_iff C v w).mp hw
  have hyx : ys ⊆ xs := by
    intro w hw
    apply (G.cycleSelection_neighbors_iff C v w).mpr
    simpa [ys] using hw
  have h1 := hx.length_le_of_subset hxy
  have h2 := hy.length_le_of_subset hyx
  have hl : xs.length = 2 := by simp only [ys, List.length_cons, List.length_nil] at h1 h2; omega
  exact ((G.selectedGraph (G.cycleSelection C)).neighbors_length v).symm.trans hl

theorem cycleSelection_degreeTwoB (hs : G.Simple) : G.degreeTwoB (G.cycleSelection C) = true := by
  apply (G.degreeTwoB_iff _).mpr
  intro v
  rw [G.selectedDegree_eq_graph_degree]
  exact G.cycleSelection_degree C hs v

theorem cycleSelection_at_next (i : Fin n) :
    (G.selectedGraph (G.cycleSelection C)).Adj
      (C.vertexAt i) (C.vertexAt (CyclePositions.next i)) := by
  apply (G.cycleSelection_adj_iff C _ _).mpr
  exact Or.inl (C.next_vertex i)

theorem cycleSelection_reach_zero (i : Nat) (hi : i < n) :
    (G.selectedGraph (G.cycleSelection C)).Reach
      (C.vertexAt ⟨0, by have := C.n_at_least_three; omega⟩) (C.vertexAt ⟨i, hi⟩) := by
  induction i with
  | zero => exact .refl _
  | succ i ih =>
      have hprev : i < n := by omega
      have he := G.cycleSelection_at_next C ⟨i, hprev⟩
      have hi' : i + 1 < n := hi
      simp only [CyclePositions.next, dite_eq_left hi'] at he
      exact .trans (ih hprev) ((G.selectedGraph _).adj_reach he)

theorem cycleSelection_connected :
    ∀ u v, (G.selectedGraph (G.cycleSelection C)).Reach u v := by
  intro u v
  obtain ⟨i, rfl⟩ := C.at_surjective u
  obtain ⟨j, rfl⟩ := C.at_surjective v
  exact .trans (.symm (G.cycleSelection_reach_zero C i.val i.isLt))
    (G.cycleSelection_reach_zero C j.val j.isLt)

end HamParity.IndexedGraph
