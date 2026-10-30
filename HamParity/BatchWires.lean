module

public import HamParity.Cycles

@[expose] public section

namespace HamParity.Circuit

def inputWire {n v : Nat} : Circuit n v → Fin n → Fin v
  | .nil, i => i
  | .snoc p _, i => (p.inputWire i).succ

def helperWire {n v : Nat} (c : Circuit n v) : Fin c.gates → Fin v :=
  match c with
  | .nil => Fin.elim0
  | .snoc p _ => Fin.cases 0 (fun j => (p.helperWire j).succ)

theorem inputs_eq_wires {n v : Nat} (c : Circuit n v) (a : Assignment v) :
    c.inputs a = fun i => a (c.inputWire i) := by
  induction c with
  | nil => rfl
  | snoc p g ih => simpa [Circuit.inputs, inputWire, tailAssignment] using ih (a := tailAssignment a)

theorem eval_inputWire {n v : Nat} (c : Circuit n v) (a : Assignment n) (i : Fin n) :
    c.eval a (c.inputWire i) = a i := by
  have h := congrFun (c.inputs_eval a) i
  simpa only [c.inputs_eq_wires] using h

theorem inputWire_injective {n v : Nat} (c : Circuit n v) :
    ∀ i j, c.inputWire i = c.inputWire j → i = j := by
  induction c with
  | nil => exact fun _ _ h => h
  | snoc p g ih =>
      intro i j h
      exact ih i j ((by simpa [inputWire, helperWire] using h))

theorem input_helper_disjoint {n v : Nat} (c : Circuit n v) :
    ∀ i j, c.inputWire i ≠ c.helperWire j := by
  induction c with
  | nil => intro i j; exact Fin.elim0 j
  | snoc p g ih =>
      intro i j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact Fin.succ_ne_zero _
      · intro h
        exact ih i j ((by simpa [inputWire, helperWire] using h))

theorem helperWire_injective {n v : Nat} (c : Circuit n v) :
    ∀ i j, c.helperWire i = c.helperWire j → i = j := by
  induction c with
  | nil => intro i; exact Fin.elim0 i
  | snoc p g ih =>
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases (fun _ => rfl) (fun j h => ?_) j
        exact False.elim (Fin.succ_ne_zero _ h.symm)
      · refine Fin.cases (fun h => ?_) (fun j h => ?_) j
        · exact False.elim (Fin.succ_ne_zero _ h)
        · exact congrArg Fin.succ (ih i j ((by simpa [inputWire, helperWire] using h)))

theorem wire_coverage {n v : Nat} (c : Circuit n v) :
    ∀ w : Fin v, (∃ i, c.inputWire i = w) ∨ (∃ j, c.helperWire j = w) := by
  induction c with
  | nil => intro w; exact Or.inl ⟨w, rfl⟩
  | snoc p g ih =>
      intro w
      refine Fin.cases (Or.inr ⟨(0 : Fin (p.gates+1)), rfl⟩) (fun w => ?_) w
      rcases ih w with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact Or.inl ⟨i, congrArg Fin.succ hi⟩
      · exact Or.inr ⟨j.succ, congrArg Fin.succ hj⟩

theorem inputWire_compose {n v w : Nat} (p : Circuit n v) (q : Circuit v w) (i : Fin n) :
    (p.compose q).inputWire i = q.inputWire (p.inputWire i) := by
  induction q with
  | nil => rfl
  | snoc q g ih => exact congrArg Fin.succ ih

end HamParity.Circuit
