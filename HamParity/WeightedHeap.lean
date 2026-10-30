module

public import HamParity.WeightedRipple

/-! Draft next-pass sources. Checked status requires a new guarded receipt.
Heap entries are occurrences, so shared wires and repeated columns are allowed. -/

@[expose] public section

namespace HamParity

abbrev WeightedWire (p : Nat) := Nat × Fin p

def heapValue {p : Nat} : List (WeightedWire p) → Assignment p → Nat
  | [], _ => 0
  | (k,w) :: xs, a => 2^k * bitValue (a w) + heapValue xs a

/-- A syntactic potential: it counts each wire occurrence, regardless of its
Boolean value or whether intermediate wire values are simultaneously feasible. -/
def heapMass {p : Nat} : List (WeightedWire p) → Nat
  | [] => 0
  | (k,_) :: xs => 2^k + heapMass xs

def columnCount {p : Nat} (k : Nat) (xs : List (WeightedWire p)) : Nat :=
  xs.countP (fun z => z.1 == k)

def renameHeap {p q : Nat} (r : Fin p → Fin q) (xs : List (WeightedWire p)) :
    List (WeightedWire q) := xs.map (fun z => (z.1, r z.2))

theorem heapValue_append {p : Nat} (xs ys : List (WeightedWire p)) (a : Assignment p) :
    heapValue (xs ++ ys) a = heapValue xs a + heapValue ys a := by
  induction xs with
  | nil => simp [heapValue]
  | cons z xs ih => simp [heapValue, ih, Nat.add_assoc]

theorem heapMass_append {p : Nat} (xs ys : List (WeightedWire p)) :
    heapMass (xs ++ ys) = heapMass xs + heapMass ys := by
  induction xs with
  | nil => simp [heapMass]
  | cons z xs ih => simp [heapMass, ih, Nat.add_assoc]

theorem heapValue_perm {p : Nat} {xs ys : List (WeightedWire p)}
    (h : xs.Perm ys) (a : Assignment p) : heapValue xs a = heapValue ys a := by
  induction h with
  | nil => rfl
  | cons z h ih => simp [heapValue, ih]
  | swap x y xs => simp [heapValue, Nat.add_left_comm]
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem heapMass_perm {p : Nat} {xs ys : List (WeightedWire p)}
    (h : xs.Perm ys) : heapMass xs = heapMass ys := by
  induction h with
  | nil => rfl
  | cons z h ih => simp [heapMass, ih]
  | swap x y xs => simp [heapMass, Nat.add_left_comm]
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem columnCount_perm {p : Nat} {xs ys : List (WeightedWire p)}
    (h : xs.Perm ys) (k : Nat) : columnCount k xs = columnCount k ys := by
  exact List.Perm.countP_eq (fun z : WeightedWire p => z.1 == k) h

theorem columnCount_cons {p : Nat} (k j : Nat) (w : Fin p) (xs : List (WeightedWire p)) :
    columnCount k ((j,w)::xs) = (if j=k then 1 else 0) + columnCount k xs := by
  by_cases h : j=k <;> simp [columnCount, h, Nat.add_comm]

theorem heapValue_rename {p q : Nat} (r : Fin p → Fin q) (xs : List (WeightedWire p))
    (a : Assignment q) : heapValue (renameHeap r xs) a = heapValue xs (fun i => a (r i)) := by
  induction xs with
  | nil => rfl
  | cons z xs ih =>
      simp only [renameHeap] at ih
      simp [renameHeap, heapValue, ih]

theorem heapMass_rename {p q : Nat} (r : Fin p → Fin q) (xs : List (WeightedWire p)) :
    heapMass (renameHeap r xs) = heapMass xs := by
  induction xs with
  | nil => rfl
  | cons z xs ih =>
      simp only [renameHeap] at ih
      simp [renameHeap, heapMass, ih]

theorem power_le_heapMass {p : Nat} (xs : List (WeightedWire p)) (z : WeightedWire p)
    (hz : z ∈ xs) : 2^z.1 ≤ heapMass xs := by
  induction xs with
  | nil => simp at hz
  | cons y ys ih =>
      rcases List.mem_cons.mp hz with rfl | hz
      · simp only [heapMass]; exact Nat.le_add_right _ _
      · have h := ih hz
        simp only [heapMass]
        exact Nat.le_trans h (Nat.le_add_left _ _)

end HamParity
