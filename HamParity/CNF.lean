module

public import Std

/-!
Actual finite CNF syntax and Boolean semantics. This first compiler layer uses lists:
duplicate clauses do not create choices and every declared variable is counted.
A later adapter will relate this syntax to the external finite-set encoding.
-/

@[expose] public section

namespace HamParity

abbrev Assignment (v : Nat) := Fin v → Bool

structure Literal (v : Nat) where
  wire : Fin v
  positive : Bool
  deriving DecidableEq, Repr

abbrev Clause (v : Nat) := List (Literal v)
abbrev CNF (v : Nat) := List (Clause v)

def Literal.eval {v : Nat} (l : Literal v) (a : Assignment v) : Bool :=
  a l.wire == l.positive

def Clause.eval {v : Nat} (c : Clause v) (a : Assignment v) : Bool :=
  c.any (fun l => l.eval a)

def CNF.eval {v : Nat} (f : CNF v) (a : Assignment v) : Bool :=
  f.all (fun c => c.eval a)

def Literal.rename {v w : Nat} (r : Fin v → Fin w) (l : Literal v) : Literal w :=
  ⟨r l.wire, l.positive⟩

def Clause.rename {v w : Nat} (r : Fin v → Fin w) (c : Clause v) : Clause w :=
  c.map (Literal.rename r)

def CNF.rename {v w : Nat} (r : Fin v → Fin w) (f : CNF v) : CNF w :=
  f.map (Clause.rename r)

def WidthAtMost {v : Nat} (k : Nat) (f : CNF v) : Prop :=
  ∀ c ∈ f, c.length ≤ k

@[simp] theorem eval_rename {v w : Nat} (r : Fin v → Fin w)
    (f : CNF v) (a : Assignment w) :
    (f.rename r).eval a = f.eval (fun i => a (r i)) := by
  simp [CNF.rename, Clause.rename, Literal.rename, CNF.eval, Clause.eval, Literal.eval,
    Function.comp_def]

@[simp] theorem eval_append {v : Nat} (f g : CNF v) (a : Assignment v) :
    (f ++ g).eval a = (f.eval a && g.eval a) := by
  simp [CNF.eval]

@[simp] theorem length_rename {v w : Nat} (r : Fin v → Fin w) (f : CNF v) :
    (f.rename r).length = f.length := by
  simp [CNF.rename]

theorem width_rename {v w k : Nat} (r : Fin v → Fin w) (f : CNF v)
    (h : WidthAtMost k f) : WidthAtMost k (f.rename r) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simpa [Clause.rename] using h d hd

theorem width_append {v k : Nat} {f g : CNF v}
    (hf : WidthAtMost k f) (hg : WidthAtMost k g) : WidthAtMost k (f ++ g) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact hf c h
  · exact hg c h

def consAssignment {v : Nat} (b : Bool) (a : Assignment v) : Assignment (v+1) :=
  Fin.cases b a

def tailAssignment {v : Nat} (a : Assignment (v+1)) : Assignment v :=
  fun i => a i.succ

@[simp] theorem cons_zero {v : Nat} (b : Bool) (a : Assignment v) :
    consAssignment b a 0 = b := rfl

@[simp] theorem cons_succ {v : Nat} (b : Bool) (a : Assignment v) (i : Fin v) :
    consAssignment b a i.succ = a i := rfl

@[simp] theorem tail_cons {v : Nat} (b : Bool) (a : Assignment v) :
    tailAssignment (consAssignment b a) = a := rfl

@[simp] theorem cons_head_tail {v : Nat} (a : Assignment (v+1)) :
    consAssignment (a 0) (tailAssignment a) = a := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end HamParity
