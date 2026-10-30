module

public import HamParity.Selections

@[expose] public section

namespace HamParity.CyclePaths

variable {α : Type} (R : α → α → Prop)

def Chain : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: xs => R a b ∧ Chain (b :: xs)

def NoThree : Prop := ∀ v a b c, R v a → R v b → R v c →
  a = b ∨ a = c ∨ b = c

def TwoNeighbors : Prop := ∀ v, ∃ a b, a ≠ b ∧ R v a ∧ R v b ∧
  ∀ c, R v c → c = a ∨ c = b

theorem two_noThree (h : TwoNeighbors R) : NoThree R := by
  intro v a b c ha hb hc
  obtain ⟨x, y, _, _, _, hp⟩ := h v
  rcases hp a ha with rfl | rfl <;>
    rcases hp b hb with rfl | rfl <;>
    rcases hp c hc with rfl | rfl <;> simp

theorem chain_tail {a : α} {xs : List α} (h : Chain R (a :: xs)) : Chain R xs := by
  cases xs with
  | nil => trivial
  | cons b ys => exact h.2

theorem chain_append_one {xs : List α} {b : α} (h : Chain R xs)
    (he : ∀ a, xs.getLast? = some a → R a b) : Chain R (xs ++ [b]) := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
      cases xs with
      | nil => exact ⟨he a rfl, trivial⟩
      | cons c ys =>
          exact ⟨h.1, ih h.2 (by simpa using he)⟩

theorem chain_reverse (hs : ∀ a b, R a b → R b a) {xs : List α}
    (h : Chain R xs) : Chain R xs.reverse := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
      rw [List.reverse_cons]
      apply chain_append_one R (ih (chain_tail R h))
      intro b hb
      cases xs with
      | nil => simp at hb
      | cons c ys =>
          have hbc : c = b := by simpa using hb
          subst b
          exact hs _ _ h.1

set_option maxHeartbeats 20000 in
/-- An external vertex can touch a duplicate-free degree-at-most-two path
only at an endpoint. This is derived, not a traversal premise. -/
theorem neighbor_boundary (hs : ∀ a b, R a b → R b a) (h3 : NoThree R)
    {xs : List α} (hc : Chain R xs) (hn : xs.Nodup)
    {x z : α} (hx : x ∉ xs) (hz : z ∈ xs) (he : R x z) :
    xs.head? = some z ∨ xs.getLast? = some z := by
  induction xs with
  | nil => simp at hz
  | cons a xs ih =>
      cases xs with
      | nil => simpa [eq_comm] using hz
      | cons b ys =>
          by_cases hza : z = a
          · subst z; exact Or.inl rfl
          have hz' : z ∈ b :: ys := (List.mem_cons.mp hz).resolve_left hza
          have hn' := (List.nodup_cons.mp hn).2
          have hx' : x ∉ b :: ys := fun h => hx (List.mem_cons_of_mem a h)
          rcases ih hc.2 hn' hx' hz' with hhead | hlast
          · have hzb : b = z := by simpa using hhead
            subst z
            cases ys with
            | nil => exact Or.inr rfl
            | cons c zs =>
                have hbad := h3 b a c x (hs _ _ hc.1) hc.2.1 (hs _ _ he)
                have ha := (List.nodup_cons.mp hn).1
                have hb := (List.nodup_cons.mp hn').1
                simp only [List.mem_cons, not_or] at ha hb hx hx'
                rcases hbad with hac | hax | hcx
                · exact False.elim (ha.2.1 hac)
                · exact False.elim (hx.1 hax.symm)
                · exact False.elim (hx'.2.1 hcx.symm)
          · exact Or.inr (by simpa using hlast)

end HamParity.CyclePaths
