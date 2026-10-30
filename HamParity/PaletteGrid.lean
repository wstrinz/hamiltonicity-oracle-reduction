module

public import HamParity.MultilinearPolynomial

@[expose] public section
namespace HamParity

def paletteGrid (D : Nat) : (m : Nat) → List (Fin m → Fin D)
  | 0 => [Fin.elim0]
  | m+1 => (paletteGrid D m).flatMap (fun a =>
      (List.finRange D).map (fun j => Fin.cases j a))

theorem paletteGrid_length (D m : Nat) : (paletteGrid D m).length=D^m := by
  induction m with
  | zero => simp [paletteGrid]
  | succ m ih =>
      simp [paletteGrid,List.length_flatMap,sum_map_constant,ih,Nat.pow_succ]

theorem paletteGrid_complete {D m : Nat} (a : Fin m → Fin D) : a ∈ paletteGrid D m := by
  induction m with
  | zero =>
      have ha : a=Fin.elim0 := by funext i; exact Fin.elim0 i
      simp [paletteGrid,ha]
  | succ m ih =>
      apply List.mem_flatMap.mpr
      refine ⟨fun i => a i.succ,ih _,List.mem_map.mpr ⟨a 0,by simp,?_⟩⟩
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

theorem paletteGrid_nodup (D m : Nat) : (paletteGrid D m).Nodup := by
  induction m with
  | zero => simp [paletteGrid]
  | succ m ih =>
      apply List.pairwise_flatMap.mpr
      constructor
      · intro a ha
        apply List.pairwise_map.mpr
        exact (List.nodup_finRange D).imp (fun h he => h (congrFun he 0))
      · apply ih.imp
        intro a b hab x hx y hy he
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
        obtain ⟨k,_,rfl⟩ := List.mem_map.mp hy
        apply hab
        funext i
        exact congrFun he i.succ

theorem sum_map_le {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x≤g x) : (xs.map f).sum≤(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons]
      omega

theorem sum_map_mul_indicator {α : Type} (xs : List α) (p : α → Bool) (c : Nat) :
    (xs.map (fun x => if p x then c else 0)).sum = xs.countP p*c := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hp : p x <;> simp [hp,ih,List.countP_cons,Nat.add_mul,Nat.add_comm]

end HamParity
