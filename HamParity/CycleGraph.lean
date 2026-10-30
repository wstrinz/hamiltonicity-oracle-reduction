module

public import HamParity.CycleMaximal

@[expose] public section

namespace HamParity.EdgeGraph

variable {n : Nat}

def incidentNeighbors (v : Fin n) (e : Fin n × Fin n) : List (Fin n) :=
  (if e.1 = v then [e.2] else []) ++ (if e.2 = v then [e.1] else [])

def neighbors (G : EdgeGraph n) (v : Fin n) : List (Fin n) :=
  G.edges.flatMap (incidentNeighbors v)

def Adj (G : EdgeGraph n) (u v : Fin n) : Prop := v ∈ G.neighbors u

/-- No loops and no repeated undirected edge incidences. -/
def Simple (G : EdgeGraph n) : Prop :=
  ∀ v, (G.neighbors v).Nodup ∧ v ∉ G.neighbors v

theorem mem_incidentNeighbors (u v : Fin n) (e : Fin n × Fin n) :
    v ∈ incidentNeighbors u e ↔
      (e.1 = u ∧ e.2 = v) ∨ (e.2 = u ∧ e.1 = v) := by
  simp only [incidentNeighbors, List.mem_append]
  split <;> split <;> simp_all [eq_comm]

theorem adj_iff (G : EdgeGraph n) (u v : Fin n) :
    G.Adj u v ↔ ∃ e ∈ G.edges,
      (e.1 = u ∧ e.2 = v) ∨ (e.2 = u ∧ e.1 = v) := by
  simp only [Adj, neighbors, List.mem_flatMap, mem_incidentNeighbors]

theorem adj_symm (G : EdgeGraph n) (u v : Fin n) (h : G.Adj u v) : G.Adj v u := by
  obtain ⟨e, he, h⟩ := (G.adj_iff u v).mp h
  apply (G.adj_iff v u).mpr
  refine ⟨e, he, ?_⟩
  rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact Or.inr ⟨hv, hu⟩
  · exact Or.inl ⟨hv, hu⟩

theorem adj_edge (G : EdgeGraph n) (e : Fin n × Fin n) (he : e ∈ G.edges) :
    G.Adj e.1 e.2 := (G.adj_iff _ _).mpr ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

theorem neighbors_length (G : EdgeGraph n) (v : Fin n) :
    (G.neighbors v).length = G.incidenceDegree v := by
  rcases G with ⟨es⟩
  simp only [neighbors, incidenceDegree]
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [List.flatMap_cons, List.length_append, incidentNeighbors,
        List.countP_cons, ih]
      by_cases h1 : e.1 = v <;> by_cases h2 : e.2 = v <;> simp [h1, h2] <;> omega

theorem twoNeighbors_of_degree_two (G : EdgeGraph n) (hs : G.Simple)
    (hd : ∀ v, G.incidenceDegree v = 2) : CyclePaths.TwoNeighbors G.Adj := by
  intro v
  have hl : (G.neighbors v).length = 2 := (G.neighbors_length v).trans (hd v)
  have hn := (hs v).1
  generalize he : G.neighbors v = xs at hl hn
  cases xs with
  | nil => simp at hl
  | cons a xs =>
      cases xs with
      | nil => simp at hl
      | cons b xs =>
          have hx : xs = [] := by
            have : xs.length = 0 := by simpa using hl
            cases xs with
            | nil => rfl
            | cons c ys => simp at this
          subst xs
          refine ⟨a, b, ?_, ?_, ?_, ?_⟩
          · simpa using hn
          · simp [Adj, he]
          · simp [Adj, he]
          · intro c hc
            simpa [Adj, he] using hc

/-- An explicit duplicate-free spanning list, with every successive pair and
the last-to-first pair adjacent. The length bound excludes 1/2-vertex conventions. -/
structure CyclicOrder (G : EdgeGraph n) where
  vertices : List (Fin n)
  nodup : vertices.Nodup
  covers : ∀ v, v ∈ vertices
  length_at_least_three : 3 ≤ vertices.length
  chain : CyclePaths.Chain G.Adj vertices
  closes : ∀ a b, vertices.head? = some a → vertices.getLast? = some b → G.Adj b a

theorem CyclicOrder.length_eq {G : EdgeGraph n} (C : G.CyclicOrder) :
    C.vertices.length = n := by
  have h1 := C.nodup.length_le_of_subset (l₂ := List.finRange n)
    (fun _ _ => List.mem_finRange _)
  have h2 := (List.nodup_finRange n).length_le_of_subset
    (l₂ := C.vertices) (fun v _ => C.covers v)
  simp only [List.length_finRange] at h1 h2
  omega

theorem closed_mem_iff_reach (G : EdgeGraph n) (xs : List (Fin n))
    (hc : ∀ u ∈ xs, ∀ v, G.Adj u v → v ∈ xs)
    {u v : Fin n} (h : G.Reach u v) : u ∈ xs ↔ v ∈ xs := by
  induction h with
  | refl => rfl
  | edge e he =>
      exact ⟨fun hu => hc _ hu _ (G.adj_edge e he),
        fun hv => hc _ hv _ (G.adj_symm _ _ (G.adj_edge e he))⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem cyclicOrder_of_connected_degree_two (G : EdgeGraph n) (hs : G.Simple)
    (root : Fin n) (hd : ∀ v, G.incidenceDegree v = 2)
    (hc : ∀ u v, G.Reach u v) : Nonempty G.CyclicOrder := by
  have ht := G.twoNeighbors_of_degree_two hs hd
  have hir : ∀ v, ¬G.Adj v v := fun v => (hs v).2
  obtain ⟨xs, hp, hm⟩ := CyclePaths.exists_longest G.Adj
  have hlen := CyclePaths.longest_length_three G.Adj G.adj_symm hir ht root hm
  have hclosed : ∀ u ∈ xs, ∀ v, G.Adj u v → v ∈ xs := by
    intro u hu v huv
    exact CyclePaths.longest_closed G.Adj G.adj_symm
      (CyclePaths.two_noThree G.Adj ht) hp hm hu huv
  have hcovers : ∀ v, v ∈ xs := by
    cases xs with
    | nil => simp at hlen
    | cons a ys =>
        intro v
        exact (G.closed_mem_iff_reach _ hclosed (hc a v)).mp (by simp)
  exact ⟨⟨xs, hp.2, hcovers, hlen, hp.1,
    CyclePaths.longest_closes G.Adj G.adj_symm hir ht hp hm hlen⟩⟩

end HamParity.EdgeGraph
