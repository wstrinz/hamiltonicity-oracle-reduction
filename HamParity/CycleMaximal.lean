module

public import HamParity.CyclePaths

@[expose] public section

namespace HamParity.CyclePaths

theorem bounded_maximum (P : Nat → Prop) (bound : Nat)
    (hex : ∃ k, P k) (hb : ∀ k, P k → k ≤ bound) :
    ∃ k, P k ∧ ∀ j, P j → j ≤ k := by
  classical
  induction bound with
  | zero =>
      obtain ⟨k, hk⟩ := hex
      exact ⟨k, hk, fun j hj => by have := hb j hj; omega⟩
  | succ bound ih =>
      by_cases htop : P (bound + 1)
      · exact ⟨bound + 1, htop, hb⟩
      · apply ih
        intro k hk
        have := hb k hk
        have : k ≠ bound + 1 := fun he => htop (he ▸ hk)
        omega

variable {α : Type} (R : α → α → Prop)

def IsPath (xs : List α) : Prop := Chain R xs ∧ xs.Nodup
def Longest (xs : List α) : Prop := ∀ ys, IsPath R ys → ys.length ≤ xs.length

theorem exists_longest {n : Nat} (R : Fin n → Fin n → Prop) :
    ∃ xs, IsPath R xs ∧ Longest R xs := by
  obtain ⟨k, ⟨xs, hp, hk⟩, hmax⟩ := bounded_maximum
    (fun k => ∃ xs, IsPath R xs ∧ xs.length = k) n
    ⟨0, [], ⟨trivial, List.nodup_nil⟩, rfl⟩ (by
      intro k hk
      obtain ⟨ys, hp, rfl⟩ := hk
      have h := hp.2.length_le_of_subset (l₂ := List.finRange n)
        (fun _ _ => List.mem_finRange _)
      simpa using h)
  refine ⟨xs, hp, ?_⟩
  intro ys hy
  have := hmax ys.length ⟨ys, hy, rfl⟩
  omega

theorem longest_head_closed (hs : ∀ a b, R a b → R b a)
    {xs : List α} (hp : IsPath R xs) (hm : Longest R xs)
    {a z : α} (ha : xs.head? = some a) (he : R a z) : z ∈ xs := by
  classical
  by_cases hz : z ∈ xs
  · exact hz
  apply False.elim
  obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp ha
  have hpath : IsPath R (z :: a :: ys) :=
    ⟨⟨hs _ _ he, hp.1⟩, List.nodup_cons.mpr ⟨hz, hp.2⟩⟩
  have h := hm _ hpath
  simp only [List.length_cons] at h
  omega

theorem longest_reverse (hs : ∀ a b, R a b → R b a)
    {xs : List α} (hp : IsPath R xs) (hm : Longest R xs) :
    IsPath R xs.reverse ∧ Longest R xs.reverse := by
  refine ⟨⟨chain_reverse R hs hp.1, ?_⟩, ?_⟩
  · exact (List.reverse_perm xs).nodup_iff.mpr hp.2
  · intro ys hy
    simpa using hm ys hy

theorem longest_closed (hs : ∀ a b, R a b → R b a) (h3 : NoThree R)
    {xs : List α} (hp : IsPath R xs) (hm : Longest R xs)
    {a z : α} (ha : a ∈ xs) (he : R a z) : z ∈ xs := by
  classical
  by_cases hz : z ∈ xs
  · exact hz
  apply False.elim
  rcases neighbor_boundary R hs h3 hp.1 hp.2 hz ha (hs _ _ he) with hh | hl
  · exact hz (longest_head_closed R hs hp hm hh he)
  · have hr := longest_reverse R hs hp hm
    have hzr := longest_head_closed R hs hr.1 hr.2 (by simpa using hl) he
    exact hz (List.mem_reverse.mp hzr)

theorem longest_length_three (hs : ∀ a b, R a b → R b a)
    (hi : ∀ v, ¬R v v) (ht : TwoNeighbors R) (root : α)
    {xs : List α} (hm : Longest R xs) : 3 ≤ xs.length := by
  obtain ⟨a, b, hab, hra, hrb, _⟩ := ht root
  have har : a ≠ root := by intro h; subst a; exact hi _ hra
  have hrb' : root ≠ b := by intro h; subst b; exact hi _ hrb
  have hp : IsPath R [a, root, b] := by
    refine ⟨⟨hs _ _ hra, hrb, trivial⟩, ?_⟩
    simp [har, hab, hrb']
  exact hm _ hp

theorem longest_closes (hs : ∀ a b, R a b → R b a)
    (hi : ∀ v, ¬R v v) (ht : TwoNeighbors R)
    {xs : List α} (hp : IsPath R xs) (hm : Longest R xs)
    (hlen : 3 ≤ xs.length) :
    ∀ a b, xs.head? = some a → xs.getLast? = some b → R b a := by
  intro a last ha hl
  obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp ha
  cases ys with
  | nil => simp at hlen
  | cons b zs =>
      obtain ⟨u, v, huv, hau, hav, _⟩ := ht a
      have hex : ∃ z, R a z ∧ z ≠ b := by
        by_cases hub : u = b
        · exact ⟨v, hav, fun hvb => huv (hub.trans hvb.symm)⟩
        · exact ⟨u, hau, hub⟩
      obtain ⟨z, haz, hzb⟩ := hex
      have hza : z ≠ a := by intro h; subst z; exact hi _ haz
      have hz := longest_head_closed R hs hp hm (a := a) rfl haz
      have hz' : z ∈ b :: zs := (List.mem_cons.mp hz).resolve_left hza
      have hnot : a ∉ b :: zs := (List.nodup_cons.mp hp.2).1
      have hn := (List.nodup_cons.mp hp.2).2
      rcases neighbor_boundary R hs (two_noThree R ht) hp.1.2 hn hnot hz' haz
        with hhead | hlast
      · exact False.elim (hzb (by simpa using hhead.symm))
      · have heq : z = last := by
          have hl' : (b :: zs).getLast? = some last := by simpa using hl
          exact Option.some.inj (hlast.symm.trans hl')
        subst z
        exact hs _ _ haz

end HamParity.CyclePaths
