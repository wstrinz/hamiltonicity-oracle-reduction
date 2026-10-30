module

public import HamParity.CNF

/-! Exact-two constraints for at most three incidence positions. Repeated wires
count repeated incidences, so a loop can contribute two to the degree. Inputs
longer than three are rejected; correctness requires the explicit length bound. -/

@[expose] public section

namespace HamParity

def exactTwoClauses {v : Nat} (wires : List (Fin v)) : CNF v :=
  match wires with
  | [a, b] => [[⟨a, true⟩], [⟨b, true⟩]]
  | [a, b, c] =>
      [[⟨a, true⟩, ⟨b, true⟩], [⟨a, true⟩, ⟨c, true⟩],
       [⟨b, true⟩, ⟨c, true⟩], [⟨a, false⟩, ⟨b, false⟩, ⟨c, false⟩]]
  | _ => [[]]

theorem exactTwoClauses_eval {v : Nat} (wires : List (Fin v))
    (h : wires.length ≤ 3) (a : Assignment v) :
    (exactTwoClauses wires).eval a = (wires.countP (fun i => a i) == 2) := by
  cases wires with
  | nil => rfl
  | cons x xs =>
      cases xs with
      | nil => cases hx : a x <;> simp [exactTwoClauses, CNF.eval, Clause.eval, hx]
      | cons y ys =>
          cases ys with
          | nil =>
              cases hx : a x <;> cases hy : a y <;>
                simp [exactTwoClauses, CNF.eval, Clause.eval, Literal.eval, hx, hy]
          | cons z zs =>
              cases zs with
              | nil =>
                  cases hx : a x <;> cases hy : a y <;> cases hz : a z <;>
                    simp [exactTwoClauses, CNF.eval, Clause.eval, Literal.eval, hx, hy, hz]
              | cons w ws => simp at h

theorem exactTwoClauses_width {v : Nat} (wires : List (Fin v)) :
    WidthAtMost 3 (exactTwoClauses wires) := by
  unfold exactTwoClauses
  split <;> simp [WidthAtMost]

theorem exactTwoClauses_length {v : Nat} (wires : List (Fin v)) :
    (exactTwoClauses wires).length ≤ 4 := by
  unfold exactTwoClauses
  split <;> simp

end HamParity
