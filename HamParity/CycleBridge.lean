module

public import HamParity.CycleGraph

@[expose] public section

namespace HamParity

theorem filter_flatMap_sublist {α β : Type} (xs : List α) (p : α → Bool)
    (f : α → List β) : List.Sublist ((xs.filter p).flatMap f) (xs.flatMap f) := by
  induction xs with
  | nil => exact List.Sublist.refl _
  | cons x xs ih =>
      by_cases hx : p x = true
      · simpa [List.filter_cons, hx] using ih.append_left (f x)
      · simpa [List.filter_cons, hx] using
          ih.trans (List.sublist_append_right (f x) (xs.flatMap f))

namespace IndexedGraph

variable {n m : Nat}

def inputGraph (G : IndexedGraph n m) : EdgeGraph n :=
  ⟨(List.finRange m).map G.endpoints⟩

def Simple (G : IndexedGraph n m) : Prop := G.inputGraph.Simple

theorem selected_neighbors_sublist (G : IndexedGraph n m) (s : Assignment m)
    (v : Fin n) :
    List.Sublist ((G.selectedGraph s).neighbors v) (G.inputGraph.neighbors v) := by
  simp only [EdgeGraph.neighbors, selectedGraph, inputGraph, List.flatMap_map]
  exact filter_flatMap_sublist _ s _

theorem selected_simple (G : IndexedGraph n m) (hG : G.Simple) (s : Assignment m) :
    (G.selectedGraph s).Simple := by
  intro v
  have hsub := G.selected_neighbors_sublist s v
  exact ⟨List.Nodup.sublist hsub (hG v).1,
    fun hv => (hG v).2 (hsub.subset hv)⟩

theorem selected_adj_input (G : IndexedGraph n m) (s : Assignment m)
    {u v : Fin n} (h : (G.selectedGraph s).Adj u v) : G.inputGraph.Adj u v :=
  (G.selected_neighbors_sublist s u).subset h

/-- Odd count of the very same emitted selection CNF yields an actual spanning
cyclic order of a selected subgraph, under structural input simplicity. -/
theorem odd_selectionCNF_cyclicOrder (G : IndexedGraph n m)
    (hsub : G.Subcubic) (hsimple : G.Simple) (root : Fin n)
    (hodd : modelCount (G.selectionCNF root) % 2 = 1) :
    ∃ s : Assignment m, Nonempty (G.selectedGraph s).CyclicOrder := by
  obtain ⟨s, hd, hc⟩ := G.odd_selectionCNF_connected_two_regular hsub root hodd
  exact ⟨s, (G.selectedGraph s).cyclicOrder_of_connected_degree_two
    (G.selected_simple hsimple s) root hd hc⟩

/-- The cycle uses actual input edges; edge-index selection does not introduce
an abstract adjacency certificate. -/
theorem odd_selectionCNF_input_cyclicOrder (G : IndexedGraph n m)
    (hsub : G.Subcubic) (hsimple : G.Simple) (root : Fin n)
    (hodd : modelCount (G.selectionCNF root) % 2 = 1) :
    Nonempty G.inputGraph.CyclicOrder := by
  obtain ⟨s, ⟨C⟩⟩ := G.odd_selectionCNF_cyclicOrder hsub hsimple root hodd
  refine ⟨⟨C.vertices, C.nodup, C.covers, C.length_at_least_three, ?_, ?_⟩⟩
  · have hmono : ∀ xs, CyclePaths.Chain (G.selectedGraph s).Adj xs →
        CyclePaths.Chain G.inputGraph.Adj xs := by
      intro xs hx
      induction xs with
      | nil => trivial
      | cons a xs ih =>
          cases xs with
          | nil => trivial
          | cons b ys => exact ⟨G.selected_adj_input s hx.1, ih hx.2⟩
    exact hmono _ C.chain
  · intro a b ha hb
    exact G.selected_adj_input s (C.closes a b ha hb)

end IndexedGraph
end HamParity
