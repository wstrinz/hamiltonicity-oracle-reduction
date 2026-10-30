module

public import HamParity.CycleBridge

@[expose] public section

namespace HamParity.CyclePaths

theorem chain_getElem {α : Type} (R : α → α → Prop) {xs : List α}
    (hc : Chain R xs) (i : Nat) (hi : i + 1 < xs.length) :
    R xs[i] xs[i+1] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
      cases xs with
      | nil => simp at hi
      | cons b ys =>
          cases i with
          | zero => exact hc.1
          | succ i => exact ih hc.2 i (by simpa using hi)

end HamParity.CyclePaths

namespace HamParity.EdgeGraph

variable {n : Nat}

theorem adj_reach (G : EdgeGraph n) {u v : Fin n} (h : G.Adj u v) : G.Reach u v := by
  obtain ⟨e, he, h⟩ := (G.adj_iff u v).mp h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .edge e he
  · exact .symm (.edge e he)

theorem chain_reach_head (G : EdgeGraph n) {xs : List (Fin n)}
    (hc : CyclePaths.Chain G.Adj xs) {a : Fin n} (ha : xs.head? = some a) :
    ∀ v ∈ xs, G.Reach a v := by
  induction xs generalizing a with
  | nil => simp at ha
  | cons b xs ih =>
      have hba : b = a := by simpa using ha
      subst a
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact .refl _
      · cases xs with
        | nil => simp at hv
        | cons c ys =>
            exact .trans (G.adj_reach hc.1) (ih hc.2 rfl v hv)

theorem CyclicOrder.connected {G : EdgeGraph n} (C : G.CyclicOrder) :
    ∀ u v, G.Reach u v := by
  have hn : C.vertices ≠ [] := by
    intro he
    have := C.length_at_least_three
    simp [he] at this
  let a := C.vertices.head hn
  have ha : C.vertices.head? = some a := List.head?_eq_some_head hn
  intro u v
  exact .trans (.symm (G.chain_reach_head C.chain ha u (C.covers u)))
    (G.chain_reach_head C.chain ha v (C.covers v))

/-- For a simple nonempty two-regular graph, connectivity is equivalent to
an actual spanning cyclic order, not a redefinition of Hamiltonicity. -/
theorem connected_iff_cyclicOrder (G : EdgeGraph n) (hs : G.Simple)
    (root : Fin n) (hd : ∀ v, G.incidenceDegree v = 2) :
    (∀ u v, G.Reach u v) ↔ Nonempty G.CyclicOrder := by
  constructor
  · exact G.cyclicOrder_of_connected_degree_two hs root hd
  · rintro ⟨C⟩
    exact C.connected

namespace CyclicOrder

variable {G : EdgeGraph n} (C : G.CyclicOrder)

def vertexAt (i : Fin n) : Fin n :=
  C.vertices[i.val]'(by rw [C.length_eq]; exact i.isLt)

theorem at_injective : ∀ i j, C.vertexAt i = C.vertexAt j → i = j := by
  intro i j h
  apply Fin.ext
  exact C.nodup.getElem_inj.mp h

theorem at_surjective : ∀ v, ∃ i, C.vertexAt i = v := by
  intro v
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem (C.covers v)
  exact ⟨⟨i, by rw [← C.length_eq]; exact hi⟩, he⟩

theorem n_at_least_three (C : G.CyclicOrder) : 3 ≤ n := by
  rw [← C.length_eq]
  exact C.length_at_least_three

theorem at_consecutive (i : Nat) (hi : i + 1 < n) :
    G.Adj (C.vertexAt ⟨i, by omega⟩) (C.vertexAt ⟨i+1, hi⟩) := by
  exact CyclePaths.chain_getElem G.Adj C.chain i (by rw [C.length_eq]; exact hi)

theorem at_wrap :
    G.Adj (C.vertexAt ⟨n-1, by have := C.n_at_least_three; omega⟩)
      (C.vertexAt ⟨0, by have := C.n_at_least_three; omega⟩) := by
  have hn : C.vertices ≠ [] := by
    intro he
    have := C.length_at_least_three
    simp [he] at this
  have hh := List.head?_eq_some_head (l := C.vertices) hn
  have hl := List.getLast?_eq_some_getLast (l := C.vertices) hn
  have h := C.closes _ _ hh hl
  simpa only [List.head_eq_getElem, List.getLast_eq_getElem, C.length_eq, vertexAt] using h

end CyclicOrder
end HamParity.EdgeGraph
