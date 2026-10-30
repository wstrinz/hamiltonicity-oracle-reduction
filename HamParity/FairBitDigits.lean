module
public import HamParity.ScheduleAmplification

@[expose] public section
namespace HamParity.FairBits

/-- Little-endian evaluation of every fixed-length bit block; no rejection. -/
def digit : (L : Nat) → Assignment L → Fin (2^L)
  | 0,_ => ⟨0,by decide⟩
  | L+1,bits =>
      ⟨bitValue (bits 0)+2*(digit L (fun i => bits i.succ)).val,by
        have h := (digit L (fun i => bits i.succ)).isLt
        have hb := bitValue_lt_two (bits 0)
        rw [Nat.pow_succ]; omega⟩

def block : (L : Nat) → Fin (2^L) → Assignment L
  | 0,_ => Fin.elim0
  | L+1,j => Fin.cases (decide (j.val%2=1))
      (block L ⟨j.val/2,by have h := j.isLt; simp only [Nat.pow_succ] at h; omega⟩)

theorem digit_block (L : Nat) (j : Fin (2^L)) : digit L (block L j)=j := by
  induction L with
  | zero => apply Fin.ext; have h := j.isLt; simp only [digit,Nat.pow_zero] at h ⊢; omega
  | succ L ih =>
      apply Fin.ext
      simp only [digit,block,Fin.cases_zero,Fin.cases_succ,ih,bitValue_lowBit]
      omega

theorem block_digit (L : Nat) (bits : Assignment L) : block L (digit L bits)=bits := by
  induction L with
  | zero => funext i; exact Fin.elim0 i
  | succ L ih =>
      have hb := bitValue_lt_two (bits 0)
      have hd : (bitValue (bits 0)+2*(digit L (fun i => bits i.succ)).val)/2=
          (digit L (fun i => bits i.succ)).val := by omega
      have hm : decide ((bitValue (bits 0)+2*(digit L (fun i => bits i.succ)).val)%2=1)=bits 0 := by
        cases he : bits 0 <;> simp [bitValue,he] <;> omega
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · cases h0 : bits 0 <;> simp [block,digit,h0,bitValue,Nat.add_mod,Nat.mul_mod]
      · change block L ⟨(bitValue (bits 0)+2*(digit L (fun i => bits i.succ)).val)/2,_⟩ j=bits j.succ
        have hf : (⟨(bitValue (bits 0)+2*(digit L (fun i => bits i.succ)).val)/2,
          by have h := (digit L (fun i => bits i.succ)).isLt; omega⟩ : Fin (2^L)) =
          digit L (fun i => bits i.succ) := Fin.ext hd
        rw [hf,ih]

theorem digit_injective (L : Nat) (a b : Assignment L) (h : digit L a=digit L b) : a=b := by
  have he := congrArg (block L) h
  simpa only [block_digit] using he

theorem block_injective (L : Nat) (a b : Fin (2^L)) (h : block L a=block L b) : a=b := by
  have he := congrArg (digit L) h
  simpa only [digit_block] using he

theorem digit_grid_perm (L : Nat) : List.Perm ((assignments L).map (digit L)) (List.finRange (2^L)) := by
  apply (List.perm_ext_iff_of_nodup _ (List.nodup_finRange _)).mpr
  · intro j
    constructor
    · intro _; simp
    · intro _; exact List.mem_map.mpr ⟨block L j,assignments_complete _,digit_block L j⟩
  · apply List.pairwise_map.mpr
    exact (assignments_nodup L).imp (fun h he => h (digit_injective L _ _ he))

theorem digit_event_count (L : Nat) (event : Fin (2^L) → Bool) :
    (assignments L).countP (fun bits => event (digit L bits))=(List.finRange (2^L)).countP event := by
  simpa only [List.countP_map,Function.comp_def] using (digit_grid_perm L).countP_eq event

end HamParity.FairBits
