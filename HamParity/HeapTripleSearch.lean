module

public import HamParity.WeightedHeap

@[expose] public section

namespace HamParity

/-- Remove the first occurrence in a specified column. -/
def takeColumn {p : Nat} (k : Nat) : List (WeightedWire p) → Option (Fin p × List (WeightedWire p))
  | [] => none
  | (j,w) :: xs =>
      if j=k then some (w,xs)
      else (takeColumn k xs).map (fun r => (r.1, (j,w)::r.2))

theorem takeColumn_perm {p : Nat} (k : Nat) (xs : List (WeightedWire p))
    (w : Fin p) (ys : List (WeightedWire p)) (h : takeColumn k xs = some (w,ys)) :
    xs.Perm ((k,w)::ys) := by
  induction xs generalizing w ys with
  | nil => simp [takeColumn] at h
  | cons z xs ih =>
      rcases z with ⟨j,x⟩
      by_cases hj : j=k
      · subst j
        have he : (x,xs) = (w,ys) := by simpa [takeColumn] using h
        cases he
        exact .refl _
      · cases ht : takeColumn k xs with
        | none => simp [takeColumn, hj, ht] at h
        | some r =>
            rcases r with ⟨y,zs⟩
            have he : (y,(j,x)::zs) = (w,ys) := by simpa [takeColumn, hj, ht] using h
            cases he
            exact ((ih _ _ ht).cons (j,x)).trans (.swap ..)

theorem takeColumn_none {p : Nat} (k : Nat) (xs : List (WeightedWire p))
    (h : takeColumn k xs = none) : columnCount k xs = 0 := by
  induction xs with
  | nil => rfl
  | cons z xs ih =>
      rcases z with ⟨j,x⟩
      by_cases hj : j=k
      · simp [takeColumn, hj] at h
      · have ht : takeColumn k xs = none := by simpa [takeColumn, hj] using h
        rw [columnCount_cons]
        simp [hj, ih ht]

structure HeapTriple (p : Nat) where
  column : Nat
  x : Fin p
  y : Fin p
  z : Fin p
  rest : List (WeightedWire p)

def HeapTriple.source {p : Nat} (t : HeapTriple p) : List (WeightedWire p) :=
  (t.column,t.x)::(t.column,t.y)::(t.column,t.z)::t.rest

def HeapTriple.prepend {p : Nat} (a : WeightedWire p) (t : HeapTriple p) : HeapTriple p :=
  { t with rest := a::t.rest }

/-- Search left to right for a column with three occurrences. If the head's
column fails, retain it in the residual list when searching the tail. -/
def findHeapTriple {p : Nat} : List (WeightedWire p) → Option (HeapTriple p)
  | [] => none
  | (k,x)::xs =>
      match takeColumn k xs with
      | none => (findHeapTriple xs).map (HeapTriple.prepend (k,x))
      | some (y,ys) =>
          match takeColumn k ys with
          | none => (findHeapTriple xs).map (HeapTriple.prepend (k,x))
          | some (z,zs) => some ⟨k,x,y,z,zs⟩

theorem prepend_triple_perm {p : Nat} (a : WeightedWire p) (xs : List (WeightedWire p))
    (t : HeapTriple p) (h : xs.Perm t.source) : (a::xs).Perm (t.prepend a).source := by
  have hm : (a::t.source).Perm (t.prepend a).source := by
    exact (List.perm_middle (a := a)
      (l₁ := [(t.column,t.x),(t.column,t.y),(t.column,t.z)]) (l₂ := t.rest)).symm
  exact (h.cons a).trans hm

theorem findHeapTriple_perm {p : Nat} (xs : List (WeightedWire p)) (t : HeapTriple p)
    (h : findHeapTriple xs = some t) : xs.Perm t.source := by
  induction xs generalizing t with
  | nil => simp [findHeapTriple] at h
  | cons a xs ih =>
      rcases a with ⟨k,x⟩
      have fallback (hf : (findHeapTriple xs).map (HeapTriple.prepend (k,x)) = some t) :
          ((k,x)::xs).Perm t.source := by
        cases hh : findHeapTriple xs with
        | none => simp [hh] at hf
        | some u =>
            have he : u.prepend (k,x) = t := by simpa [hh] using hf
            subst t
            exact prepend_triple_perm (k,x) xs u (ih u hh)
      cases h1 : takeColumn k xs with
      | none => exact fallback (by simpa [findHeapTriple, h1] using h)
      | some r =>
          rcases r with ⟨y,ys⟩
          cases h2 : takeColumn k ys with
          | none => exact fallback (by simpa [findHeapTriple, h1, h2] using h)
          | some r =>
              rcases r with ⟨z,zs⟩
              have he : (⟨k,x,y,z,zs⟩ : HeapTriple p) = t := by
                simpa [findHeapTriple, h1, h2] using h
              subst t
              exact ((takeColumn_perm k xs y ys h1).cons (k,x)).trans
                (((takeColumn_perm k ys z zs h2).cons (k,y)).cons (k,x))

/-- Failure is proved to mean at most two occurrences in every column;
normalization does not assume that the search found all compressible triples. -/
theorem findHeapTriple_none_shape {p : Nat} (xs : List (WeightedWire p))
    (h : findHeapTriple xs = none) : ∀ j, columnCount j xs ≤ 2 := by
  induction xs with
  | nil => intro j; simp [columnCount]
  | cons a xs ih =>
      rcases a with ⟨k,x⟩
      have fallback (hf : (findHeapTriple xs).map (HeapTriple.prepend (k,x)) = none)
          (hk : columnCount k xs ≤ 1) : ∀ j, columnCount j ((k,x)::xs) ≤ 2 := by
        have ht : findHeapTriple xs = none := by simpa using hf
        intro j
        rw [columnCount_cons]
        by_cases hj : k=j
        · subst j; simp only [ite_true]; omega
        · have hi := ih ht j
          simp only [ite_eq_right hj, Nat.zero_add]
          exact hi
      cases h1 : takeColumn k xs with
      | none =>
          apply fallback (by simpa [findHeapTriple, h1] using h)
          rw [takeColumn_none k xs h1]
          omega
      | some r =>
          rcases r with ⟨y,ys⟩
          cases h2 : takeColumn k ys with
          | none =>
              apply fallback (by simpa [findHeapTriple, h1, h2] using h)
              have he := columnCount_perm (takeColumn_perm k xs y ys h1) k
              rw [columnCount_cons, takeColumn_none k ys h2] at he
              simp only [ite_true] at he
              omega
          | some r => simp [findHeapTriple, h1, h2] at h

end HamParity
