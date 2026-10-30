module

public import HamParity.Circuit

/-! Counts over an explicitly complete, duplicate-free list of all assignments.
The preservation theorem permits arbitrary Boolean output constraints. It counts
primary bits freely and proves that deterministic gate helpers add no factor. -/

@[expose] public section

namespace HamParity

def assignments : (v : Nat) → List (Assignment v)
  | 0 => [Fin.elim0]
  | v+1 => (assignments v).map (consAssignment false) ++
      (assignments v).map (consAssignment true)

theorem assignments_complete {v : Nat} (a : Assignment v) : a ∈ assignments v := by
  induction v with
  | zero =>
      have h : a = Fin.elim0 := by funext i; exact Fin.elim0 i
      simp [assignments, h]
  | succ v ih =>
      have h : consAssignment (a 0) (tailAssignment a) ∈ assignments (v+1) := by
        cases hz : a 0
        · exact List.mem_append.mpr (Or.inl
            (List.mem_map.mpr ⟨tailAssignment a, ih (tailAssignment a), rfl⟩))
        · exact List.mem_append.mpr (Or.inr
            (List.mem_map.mpr ⟨tailAssignment a, ih (tailAssignment a), rfl⟩))
      simpa using h

theorem assignments_nodup (v : Nat) : (assignments v).Nodup := by
  induction v with
  | zero => simp [assignments]
  | succ v ih =>
      have hm (b : Bool) : ((assignments v).map (consAssignment b)).Nodup := by
        apply List.pairwise_map.mpr
        exact ih.imp (fun hne heq => hne (by
          simpa using congrArg tailAssignment heq))
      apply List.nodup_append.mpr
      refine ⟨hm false, hm true, ?_⟩
      intro a ha b hb heq
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      have h : false = true := congrFun heq 0
      cases h

theorem assignments_length (v : Nat) : (assignments v).length = 2 ^ v := by
  induction v with
  | zero => rfl
  | succ v ih => simp [assignments, ih, Nat.pow_succ, Nat.mul_two]

def countModels {v : Nat} (f : CNF v) (p : Assignment v → Bool) : Nat :=
  (assignments v).countP (fun a => f.eval a && p a)

def modelCount {v : Nat} (f : CNF v) : Nat :=
  countModels f (fun _ => true)

theorem countP_add_of_pointwise {α : Type} (xs : List α) (p q r : α → Bool)
    (h : ∀ a, (if p a then 1 else 0) + (if q a then 1 else 0) =
      (if r a then 1 else 0)) :
    xs.countP p + xs.countP q = xs.countP r := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.countP_cons]
      have hp := h a
      omega

theorem count_split_gate {v : Nat} (xs : List (Assignment v))
    (g q : Assignment v → Bool) (p : Assignment (v+1) → Bool) :
    ((xs.map (consAssignment false)) ++ (xs.map (consAssignment true))).countP
      (fun a => (q (tailAssignment a) && (a 0 == g (tailAssignment a))) && p a) =
      xs.countP (fun a => q a && p (consAssignment (g a) a)) := by
  rw [List.countP_append, List.countP_map, List.countP_map]
  apply countP_add_of_pointwise
  intro a
  simp only [Function.comp_apply, tail_cons, cons_zero]
  rcases Bool.eq_false_or_eq_true (q a) with hq | hq <;>
    rcases Bool.eq_false_or_eq_true (g a) with hg | hg <;> simp [hq, hg]

theorem Circuit.count_preservation {n v : Nat} (c : Circuit n v)
    (p : Assignment v → Bool) :
    countModels c.clauses p = (assignments n).countP (fun x => p (c.eval x)) := by
  induction c with
  | nil => simp [countModels, Circuit.clauses, CNF.eval, Circuit.eval]
  | @snoc v c g ih =>
      simp only [countModels, assignments, Circuit.clauses, eval_append,
        eval_rename, Gate.eval_clauses]
      change ((assignments v).map (consAssignment false) ++
          (assignments v).map (consAssignment true)).countP
        (fun a => (c.clauses.eval (tailAssignment a) &&
          (a 0 == g.eval (tailAssignment a))) && p a) = _
      rw [count_split_gate]
      exact ih (fun a => p (consAssignment (g.eval a) a))

theorem Circuit.constrained_model_count {n v : Nat} (c : Circuit n v) (q : CNF v) :
    modelCount (c.clauses ++ q) =
      (assignments n).countP (fun x => q.eval (c.eval x)) := by
  simpa [modelCount, countModels, eval_append] using
    c.count_preservation (fun a => q.eval a)

end HamParity
