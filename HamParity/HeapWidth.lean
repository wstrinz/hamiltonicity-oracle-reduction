module

public import HamParity.CarrySave

/-! Unelaborated next-pass draft. No checked status without a matching receipt. -/
@[expose] public section
namespace HamParity

def massWidth (s : Nat) : Nat := if s = 0 then 0 else s.log2 + 1

theorem massWidth_zero : massWidth 0 = 0 := by simp [massWidth]

theorem column_lt_massWidth {s k : Nat} (h : 2^k ≤ s) : k < massWidth s := by
  have hp : 0 < 2^k := Nat.pow_pos (by decide)
  have hs : s ≠ 0 := by omega
  have hk := (Nat.le_log2 hs).mpr h
  simp only [massWidth, if_neg hs]
  omega

theorem massWidth_le_of_lt_pow {s w : Nat} (h : s < 2^w) : massWidth s ≤ w := by
  by_cases hs : s=0
  · simp [hs, massWidth]
  · have hw := (Nat.log2_lt hs).mpr h
    simp only [massWidth, if_neg hs]
    omega

theorem normalizeHeap_width {p : Nat} (xs : List (WeightedWire p)) :
    ∀ z ∈ (normalizeHeap xs).heap, z.1 < massWidth (heapMass xs) := by
  intro z hz
  exact column_lt_massWidth (normalizeHeap_column_bound xs z hz)

theorem heapMass_le_length_pow {p : Nat} (xs : List (WeightedWire p)) (d : Nat)
    (h : ∀ z ∈ xs, z.1 < d) : heapMass xs ≤ xs.length * 2^d := by
  induction xs with
  | nil => simp [heapMass]
  | cons z xs ih =>
      have hz : 2^z.1 ≤ 2^d := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt (h z (by simp)))
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [heapMass, List.length_cons, Nat.add_mul]
      omega

/-- Deliberately conservative, subtraction-free palette bound, including m=0. -/
theorem heapWidth_palette_bound {p : Nat} (xs : List (WeightedWire p)) (d : Nat)
    (h : ∀ z ∈ xs, z.1 < d) :
    massWidth (heapMass xs) ≤ d + (xs.length+1).log2 + 1 := by
  apply massWidth_le_of_lt_pow
  have hm := heapMass_le_length_pow xs d h
  have hl : xs.length < 2^((xs.length+1).log2+1) :=
    Nat.lt_trans (Nat.lt_succ_self _) Nat.lt_log2_self
  have hp : 0 < 2^d := Nat.pow_pos (by decide)
  have hh := Nat.mul_lt_mul_of_pos_right hl hp
  have ht := Nat.lt_of_le_of_lt hm hh
  simpa only [Nat.pow_add, Nat.mul_comm, Nat.add_assoc] using ht

end HamParity
