module

public import HamParity.BatchCounting

@[expose] public section

namespace HamParity

theorem sum_map_nat_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_indicator {α : Type} (xs : List α) (p : α → Bool) :
    (xs.map (fun x => if p x then 1 else 0)).sum = xs.countP p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]; omega

theorem sum_map_zero {α : Type} (xs : List α) : (xs.map (fun _ => (0 : Nat))).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.map_cons, List.sum_cons, Nat.zero_add] using ih

theorem sum_fin_fibers {α : Type} {n : Nat} (xs : List α) (f : α → Fin n) :
    ((List.finRange n).map (fun v => xs.countP (fun x => f x == v))).sum = xs.length := by
  induction xs with
  | nil => simpa only [List.countP_nil, List.length_nil] using sum_map_zero (List.finRange n)
  | cons x xs ih =>
      simp only [List.countP_cons, sum_map_nat_add, ih, sum_map_indicator]
      have hp : (List.finRange n).countP (fun v => f x == v) =
          (List.finRange n).count (f x) := by
        rw [List.count_eq_countP]
        apply List.countP_congr
        intro v _
        constructor <;> intro h <;> exact beq_iff_eq.mpr (beq_iff_eq.mp h).symm
      rw [hp, (List.nodup_finRange n).count_of_mem (List.mem_finRange (f x))]
      rfl

namespace IndexedGraph

variable {n m : Nat}

/-- Every indexed edge contributes exactly two endpoint incidences, including loops. -/
theorem incidences_total (G : IndexedGraph n m) :
    ((List.finRange n).map (fun v => (G.incidences v).length)).sum = 2*m := by
  simp only [incidences, List.length_append, ← List.countP_eq_length_filter,
    sum_map_nat_add, sum_fin_fibers, List.length_finRange]
  omega

def generalRows (G : IndexedGraph n m) : List (List (Fin (m+n))) :=
  (List.finRange n).map (fun v => (G.incidences v).map (Fin.castAdd n))

theorem generalRows_length (G : IndexedGraph n m) : G.generalRows.length = n := by
  simp [generalRows]

theorem generalRows_size (G : IndexedGraph n m) : rowsSize G.generalRows = 2*m := by
  simpa only [rowsSize, generalRows, List.map_map, Function.comp_def, List.length_map] using
    G.incidences_total

theorem generalRows_valid (G : IndexedGraph n m) (s : Assignment m) (a : Assignment n) :
    rowsValid G.generalRows (joinAssignment s a) = G.degreeTwoB s := by
  simp [rowsValid, generalRows, degreeTwoB, selectedDegree, List.all_map,
    List.countP_map, Function.comp_def, joinAssignment]

end IndexedGraph
end HamParity
