module

public import HamParity.SelectionCounting

@[expose] public section

namespace HamParity

def EdgeGraph.incidenceDegree {n : Nat} (G : EdgeGraph n) (v : Fin n) : Nat :=
  G.edges.countP (fun e => e.1 == v) + G.edges.countP (fun e => e.2 == v)

namespace IndexedGraph

variable {n m : Nat}

theorem selectedDegree_eq_graph_degree (G : IndexedGraph n m) (s : Assignment m)
    (v : Fin n) : G.selectedDegree s v = (G.selectedGraph s).incidenceDegree v := by
  simp [selectedDegree, incidences, selectedGraph, EdgeGraph.incidenceDegree,
    List.countP_append, List.countP_filter, List.countP_map, Function.comp_def, Bool.and_comm]

theorem selected_edge_from_input (G : IndexedGraph n m) (s : Assignment m)
    (p : Fin n × Fin n) (hp : p ∈ (G.selectedGraph s).edges) :
    ∃ e : Fin m, s e = true ∧ G.endpoints e = p := by
  obtain ⟨e, he, hep⟩ := List.mem_map.mp hp
  exact ⟨e, (List.mem_filter.mp he).2, hep⟩

theorem odd_selectionCNF_connected_two_regular (G : IndexedGraph n m)
    (hG : G.Subcubic) (root : Fin n) (h : modelCount (G.selectionCNF root) % 2 = 1) :
    ∃ s : Assignment m, (∀ v, (G.selectedGraph s).incidenceDegree v = 2) ∧
      ∀ u v, (G.selectedGraph s).Reach u v := by
  obtain ⟨s, hd, hc⟩ := G.odd_selectionCNF_connected_degree_two hG root h
  refine ⟨s, ?_, hc⟩
  intro v
  rw [← G.selectedDegree_eq_graph_degree s v]
  exact hd v

end IndexedGraph

end HamParity
