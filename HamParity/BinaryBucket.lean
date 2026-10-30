module

public import HamParity.Completeness
public import HamParity.FullAdder

/-! Preparation source for the bounded weighted-arithmetic pass.
Its status is determined by new pass receipts, not by its presence on disk. -/

@[expose] public section

namespace HamParity

/-- Little-endian integer value, including every supplied bit. -/
def binaryValue : List Bool → Nat
  | [] => 0
  | b :: bs => bitValue b + 2 * binaryValue bs

theorem bitValue_lt_two (b : Bool) : bitValue b < 2 := by
  cases b <;> decide

theorem bitValue_injective {b c : Bool} (h : bitValue b = bitValue c) : b = c := by
  cases b <;> cases c <;> simp_all [bitValue]

theorem binaryValue_lt (bs : List Bool) : binaryValue bs < 2 ^ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
      have hb := bitValue_lt_two b
      simp only [binaryValue, List.length_cons, Nat.pow_succ]
      omega

theorem bitValue_lowBit (t : Nat) : bitValue (decide (t % 2 = 1)) = t % 2 := by
  have hm := Nat.mod_lt t (by decide : 0 < 2)
  by_cases h : t % 2 = 1
  · simp [bitValue, h]
  · have hz : t % 2 = 0 := by omega
    simp [bitValue, hz]

/-- Concrete unit clauses, one per output wire. -/
def binaryPins {v : Nat} : List (Fin v) → Nat → CNF v
  | [], _ => []
  | w :: ws, t => [[⟨w, decide (t % 2 = 1)⟩]] ++ binaryPins ws (t / 2)

theorem binaryPins_length {v : Nat} (ws : List (Fin v)) (t : Nat) :
    (binaryPins ws t).length = ws.length := by
  induction ws generalizing t with
  | nil => rfl
  | cons w ws ih => simp [binaryPins, ih]

theorem binaryPins_width {v : Nat} (ws : List (Fin v)) (t : Nat) :
    WidthAtMost 3 (binaryPins ws t) := by
  induction ws generalizing t with
  | nil => simp [binaryPins, WidthAtMost]
  | cons w ws ih =>
      apply width_append (by simp [WidthAtMost]) (ih (t / 2))

theorem binaryPins_eval_iff {v : Nat} (ws : List (Fin v)) (t : Nat)
    (a : Assignment v) (ht : t < 2 ^ ws.length) :
    (binaryPins ws t).eval a = true ↔ binaryValue (ws.map a) = t := by
  induction ws generalizing t with
  | nil =>
      have hz : t = 0 := by simpa using ht
      simp [binaryPins, CNF.eval, binaryValue, hz]
  | cons w ws ih =>
      have htail : t / 2 < 2 ^ ws.length := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
        simpa only [List.length_cons, Nat.pow_succ] using ht
      have hv := bitValue_lt_two (a w)
      have hm := Nat.mod_lt t (by decide : 0 < 2)
      have hd := Nat.mod_add_div t 2
      have hb := bitValue_lowBit t
      simp only [binaryPins, eval_append, Bool.and_eq_true]
      have hunit : CNF.eval ([[⟨w, decide (t % 2 = 1)⟩]] : CNF v) a = true ↔
          a w = decide (t % 2 = 1) := by
        simp [CNF.eval, Clause.eval, Literal.eval]
      rw [hunit, ih (t / 2) htail]
      simp only [List.map_cons, binaryValue]
      constructor
      · rintro ⟨he, hs⟩
        rw [he, hs, hb]
        omega
      · intro he
        have hb' : bitValue (a w) = t % 2 := by omega
        exact ⟨bitValue_injective (hb'.trans hb.symm), by omega⟩

/-- Out-of-range rejection replaces the pins with one empty clause.
It is never an empty formula, and never compares only low target bits. -/
def bucketPins {v : Nat} (ws : List (Fin v)) (t : Nat) : CNF v :=
  if t < 2 ^ ws.length then binaryPins ws t else [[]]

theorem bucketPins_eval_iff {v : Nat} (ws : List (Fin v)) (t : Nat) (a : Assignment v) :
    (bucketPins ws t).eval a = true ↔ binaryValue (ws.map a) = t := by
  by_cases ht : t < 2 ^ ws.length
  · simpa only [bucketPins, ite_eq_left ht] using binaryPins_eval_iff ws t a ht
  · have hv := binaryValue_lt (ws.map a)
    have hne : binaryValue (ws.map a) ≠ t := by simp only [List.length_map] at hv; omega
    simp [bucketPins, ht, CNF.eval, Clause.eval, hne]

theorem bucketPins_width {v : Nat} (ws : List (Fin v)) (t : Nat) :
    WidthAtMost 3 (bucketPins ws t) := by
  unfold bucketPins
  split
  · exact binaryPins_width ws t
  · simp [WidthAtMost]

theorem bucketPins_length_le {v : Nat} (ws : List (Fin v)) (t : Nat)
    (hn : 0 < ws.length) : (bucketPins ws t).length ≤ ws.length := by
  unfold bucketPins
  split
  · simp [binaryPins_length]
  · simp only [List.length_cons, List.length_nil]
    omega

end HamParity
