module

public import HamParity.FiniteBucketDecision

@[expose] public section
namespace HamParity

/-- Full Cartesian product with order and repetitions retained in the trials. -/
def repeatGrid {α : Type} (xs : List α) : Nat → List (List α)
  | 0 => [[]]
  | k+1 => (repeatGrid xs k).flatMap (fun tail => xs.map (fun x => x::tail))

theorem repeatGrid_length {α : Type} (xs : List α) (k : Nat) :
    (repeatGrid xs k).length=xs.length^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [repeatGrid,List.length_flatMap,sum_map_constant,ih,Nat.pow_succ]

theorem repeatGrid_member_length {α : Type} (xs : List α) (k : Nat) (ys : List α)
    (hy : ys∈repeatGrid xs k) : ys.length=k := by
  induction k generalizing ys with
  | zero => simpa [repeatGrid] using hy
  | succ k ih =>
      obtain ⟨tail,ht,hm⟩ := List.mem_flatMap.mp hy
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
      simp [ih tail ht]

theorem repeatGrid_member_elements {α : Type} (xs : List α) (k : Nat) (ys : List α)
    (hy : ys∈repeatGrid xs k) : ∀ y∈ys,y∈xs := by
  induction k generalizing ys with
  | zero => simp only [repeatGrid,List.mem_singleton] at hy; simp [hy]
  | succ k ih =>
      obtain ⟨tail,ht,hm⟩ := List.mem_flatMap.mp hy
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
      intro y hy
      rcases List.mem_cons.mp hy with h | h
      · exact h ▸ hx
      · exact ih tail ht y h

theorem repeatGrid_complete {α : Type} (xs : List α) (k : Nat) (ys : List α)
    (hl : ys.length=k) (hm : ∀ y∈ys,y∈xs) : ys∈repeatGrid xs k := by
  induction k generalizing ys with
  | zero => have he : ys=[] := List.length_eq_zero_iff.mp hl; simp [he,repeatGrid]
  | succ k ih =>
      cases ys with
      | nil => simp at hl
      | cons y ys =>
          apply List.mem_flatMap.mpr
          refine ⟨ys,ih ys (by simpa using hl) (fun x hx => hm x (by simp [hx])),?_⟩
          exact List.mem_map.mpr ⟨y,hm y (by simp),rfl⟩

theorem repeatGrid_nodup {α : Type} (xs : List α) (hn : xs.Nodup) (k : Nat) :
    (repeatGrid xs k).Nodup := by
  induction k with
  | zero => simp [repeatGrid]
  | succ k ih =>
      apply List.pairwise_flatMap.mpr
      constructor
      · intro tail ht
        apply List.pairwise_map.mpr
        exact hn.imp (fun h he => h (List.cons.inj he).1)
      · apply ih.imp
        intro a b hab x hx y hy he
        obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
        obtain ⟨v,_,rfl⟩ := List.mem_map.mp hy
        exact hab (List.cons.inj he).2

theorem countP_and_const {α : Type} (xs : List α) (p : α → Bool) (b : Bool) :
    xs.countP (fun x => p x && b)=if b then xs.countP p else 0 := by
  cases b <;> simp

theorem repeatGrid_count_all {α : Type} (xs : List α) (p : α → Bool) (k : Nat) :
    (repeatGrid xs k).countP (fun ys => ys.all p)=(xs.countP p)^k := by
  induction k with
  | zero => simp [repeatGrid,List.countP_cons]
  | succ k ih =>
      rw [repeatGrid,List.countP_flatMap]
      simp only [Function.comp_def,List.countP_map,List.all_cons]
      have he : (fun tail : List α => xs.countP (fun x => p x && tail.all p)) =
          (fun tail => if tail.all p then xs.countP p else 0) := by
        funext tail; exact countP_and_const xs p _
      rw [he,sum_map_mul_indicator,ih,Nat.pow_succ]

theorem repeatGrid_failure_count {α : Type} (xs : List α) (p : α → Bool) (k : Nat) :
    (repeatGrid xs k).countP (fun ys => !ys.any p)=(xs.countP (fun x => !p x))^k := by
  simpa only [List.not_any_eq_all_not] using repeatGrid_count_all xs (fun x => !p x) k

end HamParity
