module

public import HamParity.EdgeSelection

@[expose] public section

namespace HamParity

theorem exists_odd_of_sum_odd {α : Type} (xs : List α) (f : α → Nat)
    (h : (xs.map f).sum % 2 = 1) : ∃ x ∈ xs, f x % 2 = 1 := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hx : f x % 2 = 1
      · exact ⟨x, by simp, hx⟩
      · have hx0 : f x % 2 = 0 := by
          have hm := Nat.mod_lt (f x) (by decide : 0 < 2)
          omega
        have ht : (xs.map f).sum % 2 = 1 := by
          simpa [List.map_cons, List.sum_cons, Nat.add_mod, hx0] using h
        obtain ⟨y, hy, ho⟩ := ih ht
        exact ⟨y, by simp [hy], ho⟩

namespace IndexedGraph

variable {n m : Nat}

def selectionFiber (G : IndexedGraph n m) (root : Fin n) (s : Assignment m) : Nat :=
  (assignments n).countP (fun a => (G.selectionCNF root).eval (joinAssignment s a))

theorem selectionFiber_count (G : IndexedGraph n m) (hG : G.Subcubic)
    (root : Fin n) (s : Assignment m) :
    G.selectionFiber root s =
      if G.degreeTwoB s then (assignments n).countP ((G.selectedGraph s).rootedValidB root)
      else 0 := by
  unfold selectionFiber
  simp only [G.selectionCNF_eval hG]
  cases hd : G.degreeTwoB s <;> simp

theorem selectionFiber_power (G : IndexedGraph n m) (hG : G.Subcubic)
    (root : Fin n) (s : Assignment m) :
    G.selectionFiber root s =
      if G.degreeTwoB s then 2 ^ ((G.selectedGraph s).componentCount - 1) else 0 := by
  rw [G.selectionFiber_count hG, EdgeGraph.rooted_color_count_all_graphs]

theorem selectionCNF_sum_fibers (G : IndexedGraph n m) (root : Fin n) :
    modelCount (G.selectionCNF root) =
      ((assignments m).map (G.selectionFiber root)).sum := by
  unfold modelCount countModels selectionFiber
  simpa only [Bool.and_true] using
    count_split_assignments (G.selectionCNF root).eval

theorem selectionCNF_exact_count (G : IndexedGraph n m) (hG : G.Subcubic)
    (root : Fin n) :
    modelCount (G.selectionCNF root) =
      ((assignments m).map (fun s =>
        if G.degreeTwoB s then 2 ^ ((G.selectedGraph s).componentCount - 1) else 0)).sum := by
  rw [G.selectionCNF_sum_fibers]
  apply congrArg List.sum
  apply congrArg (fun f => (assignments m).map f)
  funext s
  exact G.selectionFiber_power hG root s

theorem odd_selectionFiber (G : IndexedGraph n m) (hG : G.Subcubic)
    (root : Fin n) (s : Assignment m) (h : G.selectionFiber root s % 2 = 1) :
    G.degreeTwoB s = true ∧ ∀ u v, (G.selectedGraph s).Reach u v := by
  rw [G.selectionFiber_count hG] at h
  by_cases hd : G.degreeTwoB s = true
  · refine ⟨hd, ?_⟩
    have hc : modelCount ((G.selectedGraph s).colorCNF root) % 2 = 1 := by
      rw [EdgeGraph.colorCNF_count]
      simpa [hd] using h
    exact (G.selectedGraph s).colorCNF_odd_connected_all_graphs root hc
  · simp [hd] at h

theorem odd_selectionCNF_connected_degree_two (G : IndexedGraph n m) (hG : G.Subcubic)
    (root : Fin n) (h : modelCount (G.selectionCNF root) % 2 = 1) :
    ∃ s : Assignment m, (∀ v, G.selectedDegree s v = 2) ∧
      ∀ u v, (G.selectedGraph s).Reach u v := by
  rw [G.selectionCNF_sum_fibers] at h
  obtain ⟨s, _, hs⟩ := exists_odd_of_sum_odd (assignments m) (G.selectionFiber root) h
  obtain ⟨hd, hc⟩ := G.odd_selectionFiber hG root s hs
  exact ⟨s, (G.degreeTwoB_iff s).mp hd, hc⟩

end IndexedGraph

end HamParity
