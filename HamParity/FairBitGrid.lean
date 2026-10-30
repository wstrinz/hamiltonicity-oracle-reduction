module
public import HamParity.FairBitDigits

@[expose] public section
namespace HamParity.FairBits

abbrev TrialBits (L m : Nat) := Fin m → Assignment L
def decodeTrial (L : Nat) {m : Nat} (bits : TrialBits L m) : Fin m → Fin (2^L) :=
  fun e => digit L (bits e)
def encodeTrial (L : Nat) {m : Nat} (w : Fin m → Fin (2^L)) : TrialBits L m :=
  fun e => block L (w e)
theorem decodeTrial_encodeTrial (L : Nat) {m : Nat} (w : Fin m → Fin (2^L)) :
    decodeTrial L (encodeTrial L w)=w := by funext e; exact digit_block L (w e)
theorem encodeTrial_decodeTrial (L : Nat) {m : Nat} (bits : TrialBits L m) :
    encodeTrial L (decodeTrial L bits)=bits := by funext e; exact block_digit L (bits e)
theorem decodeTrial_injective (L : Nat) {m : Nat} (a b : TrialBits L m)
    (h : decodeTrial L a=decodeTrial L b) : a=b := by
  have he := congrArg (encodeTrial L) h
  simpa only [encodeTrial_decodeTrial] using he

/-- Complete product of m independent length-L fair-bit blocks. -/
def grid (L : Nat) : (m : Nat) → List (TrialBits L m)
  | 0 => [Fin.elim0]
  | m+1 => (grid L m).flatMap (fun tail => (assignments L).map (fun row => Fin.cases row tail))

theorem grid_length (L m : Nat) : (grid L m).length=(2^L)^m := by
  induction m with
  | zero => simp [grid]
  | succ m ih => simp [grid,List.length_flatMap,assignments_length,sum_map_constant,ih,Nat.pow_succ]

theorem grid_complete (L : Nat) {m : Nat} (bits : TrialBits L m) : bits∈grid L m := by
  induction m with
  | zero =>
      have he : bits=Fin.elim0 := by funext e; exact Fin.elim0 e
      simp [grid,he]
  | succ m ih =>
      apply List.mem_flatMap.mpr
      refine ⟨fun e => bits e.succ,ih _,List.mem_map.mpr ⟨bits 0,assignments_complete _,?_⟩⟩
      funext e
      exact Fin.cases rfl (fun _ => rfl) e

theorem grid_nodup (L m : Nat) : (grid L m).Nodup := by
  induction m with
  | zero => simp [grid]
  | succ m ih =>
      apply List.pairwise_flatMap.mpr
      constructor
      · intro tail ht
        apply List.pairwise_map.mpr
        exact (assignments_nodup L).imp (fun h he => h (congrFun he 0))
      · apply ih.imp
        intro a b hab x hx y hy he
        obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
        obtain ⟨v,_,rfl⟩ := List.mem_map.mp hy
        apply hab
        funext e
        exact congrFun he e.succ

theorem decoded_grid_perm (L m : Nat) :
    List.Perm ((grid L m).map (decodeTrial L)) (paletteGrid (2^L) m) := by
  apply (List.perm_ext_iff_of_nodup _ (paletteGrid_nodup _ _)).mpr
  · intro w
    constructor
    · intro _; exact paletteGrid_complete _
    · intro _; exact List.mem_map.mpr ⟨encodeTrial L w,grid_complete L _,decodeTrial_encodeTrial L w⟩
  · apply List.pairwise_map.mpr
    exact (grid_nodup L m).imp (fun h he => h (decodeTrial_injective L _ _ he))

theorem trial_event_count (L m : Nat) (event : (Fin m → Fin (2^L)) → Bool) :
    (grid L m).countP (fun bits => event (decodeTrial L bits))=(paletteGrid (2^L) m).countP event := by
  simpa only [List.countP_map,Function.comp_def] using (decoded_grid_perm L m).countP_eq event

def decodeTrials (L : Nat) {m : Nat} (xs : List (TrialBits L m)) : List (Fin m → Fin (2^L)) :=
  xs.map (decodeTrial L)

theorem decodeTrials_encode (L : Nat) {m : Nat} (xs : List (Fin m → Fin (2^L))) :
    decodeTrials L (xs.map (encodeTrial L))=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [decodeTrials,decodeTrial_encodeTrial] at ih ⊢; exact ih

theorem decodeTrials_injective (L : Nat) {m : Nat} (xs ys : List (TrialBits L m))
    (h : decodeTrials L xs=decodeTrials L ys) : xs=ys :=
  (List.map_inj_right (fun a b he => decodeTrial_injective L a b he)).mp h

theorem repeated_decoded_perm (L m k : Nat) :
    List.Perm ((repeatGrid (grid L m) k).map (decodeTrials L)) (repeatGrid (paletteGrid (2^L) m) k) := by
  apply (List.perm_ext_iff_of_nodup _ (repeatGrid_nodup _ (paletteGrid_nodup _ _) k)).mpr
  · intro ys
    constructor
    · intro h
      obtain ⟨xs,hx,rfl⟩ := List.mem_map.mp h
      exact repeatGrid_complete _ _ _ (by simpa [decodeTrials] using repeatGrid_member_length _ k xs hx)
        (fun _ _ => paletteGrid_complete _)
    · intro hy
      refine List.mem_map.mpr ⟨ys.map (encodeTrial L),?_,decodeTrials_encode L ys⟩
      exact repeatGrid_complete _ _ _ (by simpa using repeatGrid_member_length _ k ys hy)
        (fun _ _ => grid_complete L _)
  · apply List.pairwise_map.mpr
    exact (repeatGrid_nodup _ (grid_nodup L m) k).imp
      (fun h he => h (decodeTrials_injective L _ _ he))

theorem repeated_event_count (L m k : Nat) (event : List (Fin m → Fin (2^L)) → Bool) :
    (repeatGrid (grid L m) k).countP (fun bits => event (decodeTrials L bits))=
      (repeatGrid (paletteGrid (2^L) m) k).countP event := by
  simpa only [List.countP_map,Function.comp_def] using (repeated_decoded_perm L m k).countP_eq event

theorem repeated_event_probability (L m k : Nat) (event : List (Fin m → Fin (2^L)) → Bool) :
    uniformProbability (repeatGrid (grid L m) k) (fun bits => event (decodeTrials L bits))=
      uniformProbability (repeatGrid (paletteGrid (2^L) m) k) event := by
  simp only [uniformProbability,repeated_event_count,repeatGrid_length,grid_length,paletteGrid_length]

theorem fair_sample_count (L m k : Nat) : (repeatGrid (grid L m) k).length=2^(k*m*L) := by
  simp only [repeatGrid_length,grid_length,← Nat.pow_mul]
  congr 1; ac_rfl

end HamParity.FairBits
