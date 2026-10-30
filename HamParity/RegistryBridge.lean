module
public import HamParity.RegistryModel
public import HamParity.ScheduleDecision

@[expose] public section
namespace HamiltonicityOracle

def graph {n m : Nat} (E : Edges n m) : HamParity.IndexedGraph n m := ⟨E⟩

theorem assignments_eq (v : Nat) : assignments v=HamParity.assignments v := by
  induction v with
  | zero => rfl
  | succ v ih => simp only [assignments,HamParity.assignments,ih]; rfl

def translate {v : Nat} (f : HamParity.CNF v) : CNF v :=
  f.map (fun c => c.map (fun l => (l.wire,l.positive)))

theorem translate_eval {v : Nat} (f : HamParity.CNF v) (a : Assignment v) :
    eval (translate f) a=f.eval a := by
  simp [translate,eval,HamParity.CNF.eval,HamParity.Clause.eval,HamParity.Literal.eval,
    List.all_map,List.any_map,Function.comp_def]

theorem translate_count {v : Nat} (f : HamParity.CNF v) :
    count (translate f)=HamParity.modelCount f := by
  simp only [count,assignments_eq,HamParity.modelCount]
  apply List.countP_congr
  intro a _
  simp only [translate_eval,Bool.and_true]

theorem translate_length {v : Nat} (f : HamParity.CNF v) :
    (translate f).length=f.length := by simp [translate]

theorem translate_width {v : Nat} (f : HamParity.CNF v) (h : HamParity.WidthAtMost 3 f) :
    ∀ c∈translate f, c.length≤3 := by
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  simpa using h d hd

theorem simple_eq {n m : Nat} (E : Edges n m) : Simple E=(graph E).Simple := rfl

theorem chain_eq {α : Type} (rel : α → α → Prop) (xs : List α) :
    Chain rel xs=HamParity.CyclePaths.Chain rel xs := by
  match xs with
  | [] => rfl
  | [_] => rfl
  | a::b::ys => simp only [Chain,HamParity.CyclePaths.Chain,chain_eq rel (b::ys)]

theorem hamiltonian_iff {n m : Nat} (E : Edges n m) :
    Hamiltonian E ↔ Nonempty (graph E).inputGraph.CyclicOrder := by
  constructor
  · rintro ⟨vs,hn,hv,h3,hchain,hclose⟩
    exact ⟨⟨vs,hn,hv,h3,(chain_eq _ _).mp hchain,hclose⟩⟩
  · rintro ⟨C⟩
    exact ⟨C.vertices,C.nodup,C.covers,C.length_at_least_three,
      (chain_eq _ _).mpr C.chain,C.closes⟩

theorem weightSum_eq {m : Nat} (xs : List (Nat × Fin m)) (s : Assignment m) :
    weightSum xs s=HamParity.heapValue xs s := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [weightSum,HamParity.heapValue,ih,HamParity.bitValue]

theorem filtered_eq {n m : Nat} (E : Edges n m) (root : Fin n)
    (w : Fin m → Nat) (t : Nat) :
    filteredCount E root w t=HamParity.modelCount ((graph E).weightedGraphCNF root w t) := by
  rw [HamParity.IndexedGraph.weightedGraphCNF_sum_fibers]
  unfold filteredCount
  simp only [assignments_eq]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  unfold HamParity.IndexedGraph.weightedGraphFiber
  apply List.countP_congr
  intro colors _
  rw [HamParity.IndexedGraph.weightedGraphCNF_eval_extension,
    HamParity.IndexedGraph.weightedGraphValid_join]
  have hw : edgeWeight w s=HamParity.edgeWeight w s := weightSum_eq _ _
  rw [hw]
  rfl

theorem digit_eq (L : Nat) (b : Assignment L) : digit L b=(HamParity.FairBits.digit L b).val := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [digit,HamParity.FairBits.digit,ih,HamParity.bitValue]

theorem bitGrid_eq (L m : Nat) : bitGrid L m=HamParity.FairBits.grid L m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [bitGrid,HamParity.FairBits.grid,ih,assignments_eq]

theorem repeatGrid_eq {α : Type} (xs : List α) (k : Nat) :
    repeatGrid xs k=HamParity.repeatGrid xs k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [repeatGrid,HamParity.repeatGrid,ih]

theorem samples_eq (n m : Nat) : samples n m=
    HamParity.repeatGrid (HamParity.FairBits.grid (HamParity.Schedule.bits n) m)
      (HamParity.Schedule.trials n) := by
  simp only [samples,repeatGrid_eq,bitGrid_eq]
  rfl

theorem repeatGrid_complete {α : Type} (xs : List α) (hc : ∀ a, a∈xs) (k : Nat)
    (ys : List α) (hy : ys.length=k) : ys∈HamParity.repeatGrid xs k := by
  induction k generalizing ys with
  | zero => have he : ys=[] := List.eq_nil_of_length_eq_zero hy; subst ys; simp [HamParity.repeatGrid]
  | succ k ih =>
    cases ys with
    | nil => simp at hy
    | cons y ys =>
      apply List.mem_flatMap.mpr
      exact ⟨ys,ih ys (by simpa using hy),List.mem_map.mpr ⟨y,hc y,rfl⟩⟩

end HamiltonicityOracle
