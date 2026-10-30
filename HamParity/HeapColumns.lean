module

public import HamParity.HeapWidth

/-! Unelaborated draft: split the zero column without losing occurrences. -/
@[expose] public section
namespace HamParity

def zeroWires {p : Nat} : List (WeightedWire p) → List (Fin p)
  | [] => []
  | (k,x)::xs => if k=0 then x::zeroWires xs else zeroWires xs

def dropColumn {p : Nat} : List (WeightedWire p) → List (WeightedWire p)
  | [] => []
  | (k,x)::xs => if k=0 then dropColumn xs else (k-1,x)::dropColumn xs

def wireSum {p : Nat} : List (Fin p) → Assignment p → Nat
  | [], _ => 0
  | x::xs, a => bitValue (a x) + wireSum xs a

theorem zeroWires_length {p : Nat} (xs : List (WeightedWire p)) :
    (zeroWires xs).length = columnCount 0 xs := by
  induction xs with
  | nil => rfl
  | cons z xs ih =>
      rcases z with ⟨k,x⟩
      by_cases hk : k=0 <;> simp [zeroWires, columnCount_cons, hk, ih, Nat.add_comm]

theorem dropColumn_count {p : Nat} (xs : List (WeightedWire p)) (k : Nat) :
    columnCount k (dropColumn xs) = columnCount (k+1) xs := by
  induction xs with
  | nil => rfl
  | cons z xs ih =>
      rcases z with ⟨j,x⟩
      by_cases hj : j=0
      · simp [dropColumn, columnCount_cons, hj, ih]
      · have he : j-1=k ↔ j=k+1 := by omega
        simp [dropColumn, columnCount_cons, hj, ih, he]

theorem dropColumn_width {p w : Nat} (xs : List (WeightedWire p))
    (h : ∀ z ∈ xs, z.1 < w+1) : ∀ z ∈ dropColumn xs, z.1 < w := by
  induction xs with
  | nil => simp [dropColumn]
  | cons y ys ih =>
      rcases y with ⟨k,x⟩
      have ht := ih (fun z hz => h z (by simp [hz]))
      by_cases hk : k=0
      · simpa [dropColumn, hk] using ht
      · intro z hz
        simp only [dropColumn, if_neg hk, List.mem_cons] at hz
        rcases hz with rfl | hz
        · have hb := h (k,x) (by simp)
          omega
        · exact ht z hz

theorem heapValue_split_column {p : Nat} (xs : List (WeightedWire p)) (a : Assignment p) :
    heapValue xs a = wireSum (zeroWires xs) a + 2 * heapValue (dropColumn xs) a := by
  induction xs with
  | nil => simp [heapValue, zeroWires, dropColumn, wireSum]
  | cons z xs ih =>
      rcases z with ⟨k,x⟩
      cases k with
      | zero => simp [heapValue, zeroWires, dropColumn, wireSum, ih, Nat.add_assoc]
      | succ k =>
          simp [heapValue, zeroWires, dropColumn, ih, Nat.pow_succ,
            Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_left_comm]

theorem columnCount_rename {p q : Nat} (r : Fin p → Fin q)
    (xs : List (WeightedWire p)) (k : Nat) :
    columnCount k (renameHeap r xs) = columnCount k xs := by
  simp [columnCount, renameHeap, List.countP_map, Function.comp_def]

end HamParity
