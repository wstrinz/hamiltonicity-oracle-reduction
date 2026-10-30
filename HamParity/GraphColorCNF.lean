module

public import HamParity.GraphColors

/-! Actual CNF for the colorings of a fixed edge graph. Vertex colors are the
n primary bits; wire zero is one deterministic true selector, and vertex v is
wire v.succ. Thus edge selectors never alias colors. This is a fixed-edge fiber,
not yet a compiler with freely counted edge-choice bits. Draft until checked. -/

@[expose] public section

namespace HamParity

def colorCircuit (n : Nat) : Circuit n (n+1) :=
  Circuit.snoc Circuit.nil (Gate.constant true)

namespace EdgeGraph

variable {n : Nat}

def colorEdges (G : EdgeGraph n) : List (CutEdge (n+1)) :=
  G.edges.map (fun e => ⟨0, e.1.succ, e.2.succ⟩)

def colorConstraints (G : EdgeGraph n) (root : Fin n) : CNF (n+1) :=
  rootedCutClauses root.succ G.colorEdges

def colorCNF (G : EdgeGraph n) (root : Fin n) : CNF (n+1) :=
  (colorCircuit n).clauses ++ G.colorConstraints root

theorem colorConstraints_eval (G : EdgeGraph n) (root : Fin n) (a : Assignment n) :
    (G.colorConstraints root).eval ((colorCircuit n).eval a) = G.rootedValidB root a := by
  apply Bool.eq_iff_iff.mpr
  unfold colorConstraints
  rw [rootedCutClauses_correct, G.rootedValidB_iff]
  constructor
  · rintro ⟨hr, he⟩
    refine ⟨hr, ?_⟩
    intro e hem
    have hm : (⟨0, e.1.succ, e.2.succ⟩ : CutEdge (n+1)) ∈ G.colorEdges :=
      List.mem_map.mpr ⟨e, hem, rfl⟩
    exact he _ hm rfl
  · rintro ⟨hr, he⟩
    refine ⟨hr, ?_⟩
    intro c hc _
    obtain ⟨e, hem, rfl⟩ := List.mem_map.mp hc
    exact he e hem

theorem colorCNF_count (G : EdgeGraph n) (root : Fin n) :
    modelCount (G.colorCNF root) = (assignments n).countP (G.rootedValidB root) := by
  rw [colorCNF, Circuit.constrained_model_count]
  apply List.countP_congr
  intro a _
  rw [G.colorConstraints_eval]

theorem colorCNF_width (G : EdgeGraph n) (root : Fin n) :
    WidthAtMost 3 (G.colorCNF root) := by
  exact width_append (colorCircuit n).width (rootedCutClauses_width root.succ G.colorEdges)

theorem colorCNF_length (G : EdgeGraph n) (root : Fin n) :
    (G.colorCNF root).length = 2 + 2 * G.edges.length := by
  simp [colorCNF, colorConstraints, rootedCutClauses_length, colorEdges,
    colorCircuit, Circuit.clauses, Gate.clauses, CNF.rename, Nat.add_assoc] <;> omega

theorem color_selector_distinct (v : Fin n) : (0 : Fin (n+1)) ≠ v.succ := by
  intro h
  have hv : 0 = v.val + 1 := congrArg Fin.val h
  omega

theorem color_wires_injective {u v : Fin n} (h : u.succ = v.succ) : u = v := by
  exact Fin.succ_inj.mp h

theorem ComponentIndex.colorCNF_modelCount {G : EdgeGraph n} {root : Fin n} {k : Nat}
    (I : G.ComponentIndex root k) : modelCount (G.colorCNF root) = 2 ^ k := by
  rw [G.colorCNF_count, I.rooted_color_count]

theorem ComponentIndex.colorCNF_disconnected_even {G : EdgeGraph n} {root : Fin n}
    {k : Nat} (I : G.ComponentIndex root k) (h : G.Disconnected) :
    modelCount (G.colorCNF root) % 2 = 0 := by
  rw [G.colorCNF_count]
  exact I.disconnected_even h

theorem ComponentIndex.colorCNF_odd_connected {G : EdgeGraph n} {root : Fin n}
    {k : Nat} (I : G.ComponentIndex root k)
    (h : modelCount (G.colorCNF root) % 2 = 1) : ∀ u v, G.Reach u v := by
  classical
  intro u v
  apply Classical.byContradiction
  intro huv
  have hz := I.colorCNF_disconnected_even ⟨u, v, huv⟩
  omega

end EdgeGraph

end HamParity
