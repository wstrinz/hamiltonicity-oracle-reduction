module

public import HamParity.GraphColorCNF

/-! Small examples and a certified infinite family of edgeless graphs.
Ordinary kernel evaluation only. Draft until checked. -/

@[expose] public section

namespace HamParity.ComponentExamples

def edgeless (n : Nat) : EdgeGraph n := ⟨[]⟩

theorem edgeless_reach_iff {n : Nat} (u v : Fin n) :
    (edgeless n).Reach u v ↔ u = v := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | edge e he => cases he
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    cases h
    exact .refl _

def edgelessIndex (k : Nat) : (edgeless (k+1)).ComponentIndex 0 k where
  label := id
  representative := id
  label_representative := fun _ => rfl
  label_root := rfl
  fiber_iff_reach := fun u v => (edgeless_reach_iff u v).symm

theorem all_isolated_vertices_counted (k : Nat) :
    modelCount ((edgeless (k+1)).colorCNF 0) = 2 ^ k :=
  (edgelessIndex k).colorCNF_modelCount

def oneEdge : EdgeGraph 2 := ⟨[(0, 1)]⟩
def twoEdges : EdgeGraph 4 := ⟨[(0, 1), (2, 3)]⟩
def triangle : EdgeGraph 3 := ⟨[(0, 1), (1, 2), (2, 0)]⟩
def twoTriangles : EdgeGraph 6 :=
  ⟨[(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]⟩

theorem one_edge_count : modelCount (oneEdge.colorCNF 0) = 1 := by
  rw [EdgeGraph.colorCNF_count]
  decide

theorem two_edges_count : modelCount (twoEdges.colorCNF 0) = 2 := by
  rw [EdgeGraph.colorCNF_count]
  decide

theorem triangle_count : modelCount (triangle.colorCNF 0) = 1 := by
  rw [EdgeGraph.colorCNF_count]
  decide

theorem two_triangles_count : modelCount (twoTriangles.colorCNF 0) = 2 := by
  rw [EdgeGraph.colorCNF_count]
  decide

end HamParity.ComponentExamples
