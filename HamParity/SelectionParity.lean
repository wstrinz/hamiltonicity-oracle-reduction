module

public import HamParity.SelectionCounting

@[expose] public section

namespace HamParity

theorem sum_mod_two_eq_countP {α : Type} (xs : List α) (f : α → Nat) (p : α → Bool)
    (h : ∀ x, f x % 2 = if p x then 1 else 0) :
    (xs.map f).sum % 2 = xs.countP p % 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hp : p x with
      | false =>
          have hx : f x % 2 = 0 := by simpa [hp] using h x
          simp [List.countP_cons, hp, Nat.add_mod, hx, ih]
      | true =>
          have hx : f x % 2 = 1 := by simpa [hp] using h x
          simp [List.countP_cons, hp, Nat.add_mod, hx, ih, Nat.add_comm]

namespace EdgeGraph

theorem ComponentIndex.zero_of_connected {n k : Nat} {G : EdgeGraph n} {root : Fin n}
    (I : G.ComponentIndex root k) (hc : ∀ u v, G.Reach u v) : k = 0 := by
  cases k with
  | zero => rfl
  | succ k =>
      let j : Fin (k+1+1) := (0 : Fin (k+1)).succ
      have hl := (I.fiber_iff_reach (I.representative 0) (I.representative j)).mpr
        (hc _ _)
      simp only [I.label_representative] at hl
      have hv : (0 : Nat) = 1 := congrArg Fin.val hl
      omega

theorem rooted_color_count_connected {n : Nat} (G : EdgeGraph n) (root : Fin n)
    (hc : ∀ u v, G.Reach u v) :
    (assignments n).countP (G.rootedValidB root) = 1 := by
  let I := G.canonicalComponentIndex root
  have hk := I.zero_of_connected hc
  have hcount := I.rooted_color_count
  simpa only [hk, Nat.pow_zero] using hcount

noncomputable def connectedB {n : Nat} (G : EdgeGraph n) : Bool := by
  classical
  exact decide (∀ u v, G.Reach u v)

theorem connectedB_iff {n : Nat} (G : EdgeGraph n) :
    G.connectedB = true ↔ ∀ u v, G.Reach u v := by
  classical
  simp [connectedB]

end EdgeGraph

namespace IndexedGraph

variable {n m : Nat}

noncomputable def connectedDegreeTwoB (G : IndexedGraph n m) (s : Assignment m) : Bool :=
  G.degreeTwoB s && (G.selectedGraph s).connectedB

theorem connectedDegreeTwoB_iff (G : IndexedGraph n m) (s : Assignment m) :
    G.connectedDegreeTwoB s = true ↔
      (∀ v, G.selectedDegree s v = 2) ∧ ∀ u v, (G.selectedGraph s).Reach u v := by
  simp [connectedDegreeTwoB, G.degreeTwoB_iff, EdgeGraph.connectedB_iff]

theorem selectionFiber_mod_two (G : IndexedGraph n m) (hG : G.Subcubic)
    (root : Fin n) (s : Assignment m) :
    G.selectionFiber root s % 2 = if G.connectedDegreeTwoB s then 1 else 0 := by
  classical
  rw [G.selectionFiber_count hG]
  by_cases hd : G.degreeTwoB s = true
  · by_cases hc : ∀ u v, (G.selectedGraph s).Reach u v
    · have hb : (G.selectedGraph s).connectedB = true :=
        (EdgeGraph.connectedB_iff _).mpr hc
      simp [hd, connectedDegreeTwoB, hb,
        EdgeGraph.rooted_color_count_connected _ root hc]
    · have hb : (G.selectedGraph s).connectedB = false := by
        simp [EdgeGraph.connectedB, hc]
      obtain ⟨u, hu⟩ := Classical.not_forall.mp hc
      obtain ⟨v, hv⟩ := Classical.not_forall.mp hu
      have hz := (G.selectedGraph s).colorCNF_disconnected_even_all_graphs root ⟨u, v, hv⟩
      rw [EdgeGraph.colorCNF_count] at hz
      simp [hd, connectedDegreeTwoB, hb, hz]
  · simp [hd, connectedDegreeTwoB]

theorem selectionCNF_parity (G : IndexedGraph n m) (hG : G.Subcubic) (root : Fin n) :
    modelCount (G.selectionCNF root) % 2 =
      (assignments m).countP G.connectedDegreeTwoB % 2 := by
  rw [G.selectionCNF_sum_fibers]
  exact sum_mod_two_eq_countP (assignments m) (G.selectionFiber root)
    G.connectedDegreeTwoB (G.selectionFiber_mod_two hG root)

end IndexedGraph

end HamParity
