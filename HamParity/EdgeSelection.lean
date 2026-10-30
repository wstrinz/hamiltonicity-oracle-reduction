module

public import HamParity.Components
public import HamParity.SplitAssignments
public import HamParity.DegreeTwo

/-! Indexed edge choices and actual subcubic degree-two/color clauses. Edge
indices are distinct Boolean variables even if endpoint pairs coincide. A loop
has two incidences. The degree bound concerns the full input incidence list. -/

@[expose] public section

namespace HamParity

theorem eval_flatMap {α : Type} {v : Nat} (xs : List α) (f : α → CNF v)
    (a : Assignment v) :
    CNF.eval (xs.flatMap f) a = xs.all (fun x => (f x).eval a) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, eval_append, ih]

theorem length_flatMap_le {α β : Type} (xs : List α) (f : α → List β) (b : Nat)
    (h : ∀ x, (f x).length ≤ b) : (xs.flatMap f).length ≤ b * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simpa [List.flatMap_cons, Nat.mul_add, Nat.add_comm] using Nat.add_le_add (h x) ih

structure IndexedGraph (n m : Nat) where
  endpoints : Fin m → Fin n × Fin n

namespace IndexedGraph

variable {n m : Nat}

def selectedGraph (G : IndexedGraph n m) (s : Assignment m) : EdgeGraph n :=
  ⟨((List.finRange m).filter s).map G.endpoints⟩

def incidences (G : IndexedGraph n m) (v : Fin n) : List (Fin m) :=
  (List.finRange m).filter (fun e => (G.endpoints e).1 == v) ++
    (List.finRange m).filter (fun e => (G.endpoints e).2 == v)

def selectedDegree (G : IndexedGraph n m) (s : Assignment m) (v : Fin n) : Nat :=
  (G.incidences v).countP s

def Subcubic (G : IndexedGraph n m) : Prop := ∀ v, (G.incidences v).length ≤ 3

def degreeTwoB (G : IndexedGraph n m) (s : Assignment m) : Bool :=
  (List.finRange n).all (fun v => G.selectedDegree s v == 2)

theorem degreeTwoB_iff (G : IndexedGraph n m) (s : Assignment m) :
    G.degreeTwoB s = true ↔ ∀ v, G.selectedDegree s v = 2 := by
  simp [degreeTwoB, List.all_eq_true]

def degreeClauses (G : IndexedGraph n m) (v : Fin n) : CNF (m+n) :=
  exactTwoClauses ((G.incidences v).map (Fin.castAdd n))

def degreeCNF (G : IndexedGraph n m) : CNF (m+n) :=
  (List.finRange n).flatMap G.degreeClauses

def selectionCutEdges (G : IndexedGraph n m) : List (CutEdge (m+n)) :=
  (List.finRange m).map (fun e =>
    ⟨Fin.castAdd n e, Fin.natAdd m (G.endpoints e).1, Fin.natAdd m (G.endpoints e).2⟩)

def selectionCutCNF (G : IndexedGraph n m) (root : Fin n) : CNF (m+n) :=
  rootedCutClauses (Fin.natAdd m root) G.selectionCutEdges

def selectionCNF (G : IndexedGraph n m) (root : Fin n) : CNF (m+n) :=
  G.degreeCNF ++ G.selectionCutCNF root

theorem degreeClauses_eval (G : IndexedGraph n m) (hG : G.Subcubic) (v : Fin n)
    (s : Assignment m) (a : Assignment n) :
    (G.degreeClauses v).eval (joinAssignment s a) = (G.selectedDegree s v == 2) := by
  unfold degreeClauses
  rw [exactTwoClauses_eval _ (by simpa using hG v)]
  simp [selectedDegree, List.countP_map, joinAssignment, Function.comp_def]

theorem degreeCNF_eval (G : IndexedGraph n m) (hG : G.Subcubic)
    (s : Assignment m) (a : Assignment n) :
    G.degreeCNF.eval (joinAssignment s a) = G.degreeTwoB s := by
  unfold degreeCNF degreeTwoB
  rw [eval_flatMap]
  congr 1
  funext v
  exact G.degreeClauses_eval hG v s a

theorem selectedValid_iff (G : IndexedGraph n m) (root : Fin n)
    (s : Assignment m) (a : Assignment n) :
    (G.selectedGraph s).rootedValidB root a = true ↔
      a root = false ∧ ∀ e, s e = true → a (G.endpoints e).1 = a (G.endpoints e).2 := by
  rw [EdgeGraph.rootedValidB_iff]
  constructor
  · rintro ⟨hr, he⟩
    refine ⟨hr, ?_⟩
    intro e hs
    exact he (G.endpoints e) (List.mem_map.mpr ⟨e,
      List.mem_filter.mpr ⟨List.mem_finRange e, hs⟩, rfl⟩)
  · rintro ⟨hr, he⟩
    refine ⟨hr, ?_⟩
    intro p hp
    obtain ⟨e, hem, rfl⟩ := List.mem_map.mp hp
    exact he e (List.mem_filter.mp hem).2

theorem selectionCutCNF_eval (G : IndexedGraph n m) (root : Fin n)
    (s : Assignment m) (a : Assignment n) :
    (G.selectionCutCNF root).eval (joinAssignment s a) =
      (G.selectedGraph s).rootedValidB root a := by
  apply Bool.eq_iff_iff.mpr
  unfold selectionCutCNF
  rw [rootedCutClauses_correct, G.selectedValid_iff]
  constructor
  · rintro ⟨hr, he⟩
    refine ⟨by simpa [joinAssignment, Fin.addCases_right] using hr, ?_⟩
    intro e hs
    have hm : (⟨Fin.castAdd n e, Fin.natAdd m (G.endpoints e).1,
        Fin.natAdd m (G.endpoints e).2⟩ : CutEdge (m+n)) ∈ G.selectionCutEdges :=
      List.mem_map.mpr ⟨e, List.mem_finRange e, rfl⟩
    have hc := he _ hm (by simpa [joinAssignment] using hs)
    simpa [joinAssignment, Fin.addCases_right] using hc
  · rintro ⟨hr, he⟩
    refine ⟨by simpa [joinAssignment, Fin.addCases_right] using hr, ?_⟩
    intro c hc hs
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hc
    have hse : s e = true := by simpa [joinAssignment] using hs
    simpa [joinAssignment, Fin.addCases_right] using he e hse

theorem selectionCNF_eval (G : IndexedGraph n m) (hG : G.Subcubic) (root : Fin n)
    (s : Assignment m) (a : Assignment n) :
    (G.selectionCNF root).eval (joinAssignment s a) =
      (G.degreeTwoB s && (G.selectedGraph s).rootedValidB root a) := by
  rw [selectionCNF, eval_append, G.degreeCNF_eval hG, G.selectionCutCNF_eval]

theorem degreeCNF_width (G : IndexedGraph n m) : WidthAtMost 3 G.degreeCNF := by
  intro c hc
  obtain ⟨v, _, hv⟩ := List.mem_flatMap.mp hc
  exact exactTwoClauses_width _ c hv

theorem degreeCNF_length (G : IndexedGraph n m) : G.degreeCNF.length ≤ 4*n := by
  simpa [degreeCNF] using length_flatMap_le (List.finRange n) G.degreeClauses 4
    (fun v => exactTwoClauses_length _)

theorem selectionCutCNF_length (G : IndexedGraph n m) (root : Fin n) :
    (G.selectionCutCNF root).length = 1 + 2*m := by
  simp [selectionCutCNF, rootedCutClauses_length, selectionCutEdges]

theorem selectionCNF_width (G : IndexedGraph n m) (root : Fin n) :
    WidthAtMost 3 (G.selectionCNF root) :=
  width_append G.degreeCNF_width (rootedCutClauses_width _ _)

theorem selectionCNF_length (G : IndexedGraph n m) (root : Fin n) :
    (G.selectionCNF root).length ≤ 4*n + 1 + 2*m := by
  rw [selectionCNF, List.length_append, G.selectionCutCNF_length]
  have h := G.degreeCNF_length
  omega

theorem edge_color_distinct (e : Fin m) (v : Fin n) :
    Fin.castAdd n e ≠ Fin.natAdd m v := by
  intro h
  have hv : e.val = m + v.val := congrArg Fin.val h
  have he := e.isLt
  omega

end IndexedGraph

end HamParity
