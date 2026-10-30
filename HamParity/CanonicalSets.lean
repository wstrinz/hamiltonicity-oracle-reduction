module

public import HamParity.DecisionAmplification

/-! Std-only finite-set representatives. These are not Mathlib Finset imports. -/
@[expose] public section
namespace HamParity.Canonical

def unique {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x::xs => let tail := unique xs; if x∈tail then tail else x::tail

theorem mem_unique {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    x∈unique xs ↔ x∈xs := by
  induction xs generalizing x with
  | nil => simp [unique]
  | cons a xs ih =>
      simp only [unique]
      split
      · rename_i ha
        have hax := (ih a).mp ha
        simp only [ih, List.mem_cons]
        constructor
        · exact Or.inr
        · intro h
          rcases h with rfl | h
          · exact hax
          · exact h
      · simp [ih]

theorem unique_nodup {α : Type} [DecidableEq α] (xs : List α) : (unique xs).Nodup := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih => simp only [unique]; split <;> simp_all

theorem unique_length {α : Type} [DecidableEq α] (xs : List α) : (unique xs).length≤xs.length := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih => simp only [unique]; split <;> simp only [List.length_cons] <;> omega

def canonical {α : Type} [DecidableEq α] [LE α] [DecidableLE α] (xs : List α) : List α :=
  (unique xs).mergeSort (fun a b => decide (a≤b))

theorem mem_canonical {α : Type} [DecidableEq α] [LE α] [DecidableLE α] (x : α) (xs : List α) :
    x∈canonical xs ↔ x∈xs := by simp [canonical,List.mem_mergeSort,mem_unique]

theorem canonical_length {α : Type} [DecidableEq α] [LE α] [DecidableLE α] (xs : List α) :
    (canonical xs).length≤xs.length := by simpa [canonical] using unique_length xs

theorem canonical_nodup {α : Type} [DecidableEq α] [LE α] [DecidableLE α] (xs : List α) :
    (canonical xs).Nodup :=
  (List.mergeSort_perm (unique xs) _).nodup_iff.mpr (unique_nodup xs)

theorem canonical_sorted {α : Type} [DecidableEq α] [LE α] [DecidableLE α]
    (ht : ∀ a b c : α,a≤b → b≤c → a≤c) (ho : ∀ a b : α,a≤b ∨ b≤a) (xs : List α) :
    (canonical xs).Pairwise (·≤·) := by
  have hs := List.pairwise_mergeSort (le:=fun a b : α => decide (a≤b))
    (by intro a b c hab hbc; exact decide_eq_true (ht a b c (of_decide_eq_true hab) (of_decide_eq_true hbc)))
    (by intro a b; simpa using ho a b) (unique xs)
  simpa only [canonical,decide_eq_true_eq] using hs

/-- Sorted duplicate-free representatives are determined by membership. -/
theorem sorted_unique_eq {α : Type} [LE α] (xs ys : List α)
    (ha : ∀ a b : α,a≤b → b≤a → a=b) (hx : xs.Nodup) (hy : ys.Nodup)
    (hsx : xs.Pairwise (·≤·)) (hsy : ys.Pairwise (·≤·))
    (hm : ∀ a,a∈xs ↔ a∈ys) : xs=ys := by
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => ha a b hab hba)
    hsx hsy ((List.perm_ext_iff_of_nodup hx hy).mpr hm)

end HamParity.Canonical
