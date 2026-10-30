module

public import HamParity.HeapColumns

/-! Unelaborated draft. Missing positions reuse one constrained-zero wire. -/
@[expose] public section
namespace HamParity

def paddedPair {p : Nat} (zero : Fin p) : List (Fin p) → Fin p × Fin p
  | [] => (zero,zero)
  | [x] => (x,zero)
  | x::y::_ => (x,y)

theorem paddedPair_value {p : Nat} (zero : Fin p) (xs : List (Fin p))
    (a : Assignment p) (hz : a zero = false) (hl : xs.length ≤ 2) :
    bitValue (a (paddedPair zero xs).1) + bitValue (a (paddedPair zero xs).2) = wireSum xs a := by
  cases xs with
  | nil => simp [paddedPair, wireSum, hz, bitValue]
  | cons x xs =>
      cases xs with
      | nil => cases hx : a x <;> simp [paddedPair, wireSum, hz, bitValue, hx]
      | cons y ys =>
          cases ys with
          | nil => simp [paddedPair, wireSum]
          | cons z zs => simp only [List.length_cons] at hl; omega

def denseHeapRows {p : Nat} (zero : Fin p) (xs : List (WeightedWire p)) :
    Nat → List (Fin p × Fin p)
  | 0 => []
  | w+1 => paddedPair zero (zeroWires xs) :: denseHeapRows zero (dropColumn xs) w

theorem denseHeapRows_length {p : Nat} (zero : Fin p)
    (xs : List (WeightedWire p)) (w : Nat) : (denseHeapRows zero xs w).length = w := by
  induction w generalizing xs with
  | zero => rfl
  | succ w ih => simp [denseHeapRows, ih]

theorem denseHeapRows_value {p : Nat} (zero : Fin p) (xs : List (WeightedWire p))
    (w : Nat) (a : Assignment p) (hz : a zero = false)
    (hs : ∀ k, columnCount k xs ≤ 2) (hw : ∀ z ∈ xs, z.1 < w) :
    rowPairValue (denseHeapRows zero xs w) a = heapValue xs a := by
  induction w generalizing xs with
  | zero =>
      have he : xs=[] := by
        cases xs with
        | nil => rfl
        | cons z zs => have hh := hw z (by simp); omega
      simp [he, denseHeapRows, rowPairValue, heapValue]
  | succ w ih =>
      have ht : ∀ k, columnCount k (dropColumn xs) ≤ 2 := by
        intro k
        rw [dropColumn_count]
        exact hs (k+1)
      have hb := dropColumn_width xs hw
      rw [denseHeapRows, rowPairValue]
      rw [paddedPair_value zero (zeroWires xs) a hz (by rw [zeroWires_length]; exact hs 0)]
      rw [ih (dropColumn xs) ht hb]
      exact (heapValue_split_column xs a).symm

end HamParity
