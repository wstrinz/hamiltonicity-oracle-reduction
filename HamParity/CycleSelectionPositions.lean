module

public import HamParity.GeneralGraphs

/-! Preparation source for the bounded completeness pass. Not checked until
recorded by this pass's compiler receipts. No new axioms or proof holes. -/

@[expose] public section

namespace HamParity.CyclePositions

variable {n : Nat}

def next (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else ⟨0, by have := i.isLt; omega⟩

def prev (i : Fin n) : Fin n :=
  if h : i.val = 0 then ⟨n-1, by have := i.isLt; omega⟩
  else ⟨i.val-1, by have := i.isLt; omega⟩

theorem next_prev (i : Fin n) : next (prev i) = i := by
  have hilt := i.isLt
  by_cases hi : i.val = 0
  · have hn : ¬ (n-1+1 < n) := by omega
    apply Fin.ext
    simp [next, prev, hi, hn]
  · have hn : i.val-1+1 < n := by omega
    apply Fin.ext
    simp [next, prev, hi, hn]
    omega

theorem prev_next (i : Fin n) : prev (next i) = i := by
  have hilt := i.isLt
  by_cases hi : i.val + 1 < n
  · apply Fin.ext
    simp [next, prev, hi]
  · apply Fin.ext
    simp [next, prev, hi]
    omega

theorem next_injective {i j : Fin n} (h : next i = next j) : i = j := by
  have h' := congrArg prev h
  simpa only [prev_next] using h'

theorem next_ne_prev (hn : 3 ≤ n) (i : Fin n) : next i ≠ prev i := by
  intro h
  have h' := congrArg Fin.val h
  simp only [next, prev] at h'
  split at h' <;> split at h' <;> simp_all <;> omega

end HamParity.CyclePositions

namespace HamParity.EdgeGraph.CyclicOrder

variable {n : Nat} {G : EdgeGraph n} (C : G.CyclicOrder)

noncomputable def position (v : Fin n) : Fin n := Classical.choose (C.at_surjective v)

theorem vertex_position (v : Fin n) : C.vertexAt (C.position v) = v :=
  Classical.choose_spec (C.at_surjective v)

theorem position_vertex (i : Fin n) : C.position (C.vertexAt i) = i :=
  C.at_injective _ _ (C.vertex_position _)

noncomputable def nextVertex (v : Fin n) : Fin n :=
  C.vertexAt (CyclePositions.next (C.position v))

noncomputable def prevVertex (v : Fin n) : Fin n :=
  C.vertexAt (CyclePositions.prev (C.position v))

theorem next_vertex (i : Fin n) :
    C.nextVertex (C.vertexAt i) = C.vertexAt (CyclePositions.next i) := by
  simp only [nextVertex, C.position_vertex]

theorem prev_vertex (i : Fin n) :
    C.prevVertex (C.vertexAt i) = C.vertexAt (CyclePositions.prev i) := by
  simp only [prevVertex, C.position_vertex]

theorem next_prev_vertex (v : Fin n) : C.nextVertex (C.prevVertex v) = v := by
  simp only [prevVertex, C.next_vertex, CyclePositions.next_prev, C.vertex_position]

theorem prev_next_vertex (v : Fin n) : C.prevVertex (C.nextVertex v) = v := by
  simp only [nextVertex, C.prev_vertex, CyclePositions.prev_next, C.vertex_position]

theorem nextVertex_injective {u v : Fin n} (h : C.nextVertex u = C.nextVertex v) : u = v := by
  have h' := congrArg C.prevVertex h
  simpa only [C.prev_next_vertex] using h'

theorem nextVertex_ne_prevVertex (v : Fin n) : C.nextVertex v ≠ C.prevVertex v := by
  intro h
  exact CyclePositions.next_ne_prev C.n_at_least_three _ (C.at_injective _ _ h)

theorem at_next_adj (i : Fin n) : G.Adj (C.vertexAt i) (C.vertexAt (CyclePositions.next i)) := by
  by_cases hi : i.val + 1 < n
  · simpa only [CyclePositions.next, dite_eq_left hi] using C.at_consecutive i.val hi
  · have he : i = (⟨n-1, by have := C.n_at_least_three; omega⟩ : Fin n) := by
      apply Fin.ext
      change i.val = n-1
      have := i.isLt
      omega
    have hn : ¬ (n-1+1 < n) := by have := C.n_at_least_three; omega
    simpa [CyclePositions.next, he, hn] using C.at_wrap

theorem nextVertex_adj (v : Fin n) : G.Adj v (C.nextVertex v) := by
  simpa only [nextVertex, C.vertex_position] using C.at_next_adj (C.position v)

theorem prevVertex_adj (v : Fin n) : G.Adj v (C.prevVertex v) := by
  have h := C.nextVertex_adj (C.prevVertex v)
  rw [C.next_prev_vertex] at h
  exact G.adj_symm _ _ h

end HamParity.EdgeGraph.CyclicOrder
