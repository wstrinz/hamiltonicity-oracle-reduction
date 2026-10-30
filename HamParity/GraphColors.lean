module

public import HamParity.ComponentColors
public import HamParity.CutColors

/-! Undirected reachability and a bridge from certified component labels to
actual rooted edge-color constraints. A component index must be certified by
reachability; constructing one for every finite graph is a separate obligation.
Draft until checked. -/

@[expose] public section

namespace HamParity

structure EdgeGraph (n : Nat) where
  edges : List (Fin n × Fin n)

namespace EdgeGraph

variable {n : Nat}

inductive Reach (G : EdgeGraph n) : Fin n → Fin n → Prop where
  | refl (v : Fin n) : Reach G v v
  | edge (e : Fin n × Fin n) (he : e ∈ G.edges) : Reach G e.1 e.2
  | symm {u v : Fin n} : Reach G u v → Reach G v u
  | trans {u v w : Fin n} : Reach G u v → Reach G v w → Reach G u w

def RootedValid (G : EdgeGraph n) (root : Fin n) (a : Assignment n) : Prop :=
  a root = false ∧ ∀ e ∈ G.edges, a e.1 = a e.2

def rootedValidB (G : EdgeGraph n) (root : Fin n) (a : Assignment n) : Bool :=
  !a root && G.edges.all (fun e => a e.1 == a e.2)

theorem rootedValidB_iff (G : EdgeGraph n) (root : Fin n) (a : Assignment n) :
    G.rootedValidB root a = true ↔ G.RootedValid root a := by
  simp [rootedValidB, RootedValid, List.all_eq_true]

theorem equal_of_reach (G : EdgeGraph n) (a : Assignment n)
    (hlocal : ∀ e ∈ G.edges, a e.1 = a e.2) {u v : Fin n} (h : G.Reach u v) :
    a u = a v := by
  induction h with
  | refl => rfl
  | edge e he => exact hlocal e he
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

structure ComponentIndex (G : EdgeGraph n) (root : Fin n) (k : Nat)
    extends RootedPartition n k root where
  fiber_iff_reach : ∀ u v, label u = label v ↔ G.Reach u v

namespace ComponentIndex

variable {G : EdgeGraph n} {root : Fin n} {k : Nat} (I : G.ComponentIndex root k)

theorem valid_iff (a : Assignment n) :
    G.RootedValid root a ↔ I.toRootedPartition.Valid a := by
  constructor
  · rintro ⟨hr, he⟩
    refine ⟨hr, ?_⟩
    intro u v huv
    exact G.equal_of_reach a he ((I.fiber_iff_reach u v).mp huv)
  · rintro ⟨hr, hc⟩
    refine ⟨hr, ?_⟩
    intro e he
    exact hc e.1 e.2 ((I.fiber_iff_reach e.1 e.2).mpr (.edge e he))

include I in
theorem rooted_color_count :
    (assignments n).countP (G.rootedValidB root) = 2 ^ k := by
  calc
    _ = (assignments n).countP I.toRootedPartition.validB := by
      apply List.countP_congr
      intro a _
      exact (G.rootedValidB_iff root a).trans
        ((I.valid_iff a).trans (I.toRootedPartition.validB_iff a).symm)
    _ = 2 ^ k := I.toRootedPartition.rooted_color_count

end ComponentIndex

def Disconnected (G : EdgeGraph n) : Prop :=
  ∃ u v : Fin n, ¬G.Reach u v

theorem ComponentIndex.positive_of_disconnected {G : EdgeGraph n} {root : Fin n}
    {k : Nat} (I : G.ComponentIndex root k) (h : G.Disconnected) : 0 < k := by
  cases k with
  | zero =>
      obtain ⟨u, v, huv⟩ := h
      have hl : I.label u = I.label v := by
        apply Fin.ext
        have hu := (I.label u).isLt
        have hv := (I.label v).isLt
        omega
      exact False.elim (huv ((I.fiber_iff_reach u v).mp hl))
  | succ k => omega

theorem ComponentIndex.disconnected_even {G : EdgeGraph n} {root : Fin n}
    {k : Nat} (I : G.ComponentIndex root k) (h : G.Disconnected) :
    (assignments n).countP (G.rootedValidB root) % 2 = 0 := by
  rw [I.rooted_color_count]
  have hk := I.positive_of_disconnected h
  cases k with
  | zero => omega
  | succ k => simp [Nat.pow_succ, Nat.mul_mod]

end EdgeGraph

end HamParity
