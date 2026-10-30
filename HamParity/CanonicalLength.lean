module

public import HamParity.CanonicalEncoding

@[expose] public section
namespace HamParity.Canonical

theorem length_encodeNat (n : Nat) : (encodeNat n).length=n+1 := by simp [encodeNat]

theorem length_frame (bits : List Bool) : (frame bits).length=2*bits.length+1 := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame] at ih ⊢; omega

theorem length_encodeList_cons {α : Type} (enc : α → List Bool) (a : α) (as : List α) :
    (encodeList enc (a::as)).length=2*(enc a).length+2+(encodeList enc as).length := by
  simp [encodeList,length_frame]; omega

theorem length_encodeList_upper {α : Type} (enc : α → List Bool) (xs : List α) (K : Nat)
    (h : ∀ x∈xs,(enc x).length≤K) :
    (encodeList enc xs).length≤1+(2*K+2)*xs.length := by
  induction xs with
  | nil => simp [encodeList]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      rw [length_encodeList_cons]
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega

theorem encode_clause_length (F : Input) (hf : F.WellFormed) (c : List Nat) (hc : c∈F.clauses) :
    (encodeList encodeNat c).length≤1+(4*F.variables+2)*c.length := by
  have h := length_encodeList_upper encodeNat c (2*F.variables) (by
    intro j hj
    rw [length_encodeNat]
    have hb := (hf.2.2 c hc).2.2 j hj
    omega)
  simpa [← Nat.mul_assoc] using h

theorem input_encode_length (F : Input) (hf : F.WellFormed) (k : Nat) (hw : F.WidthAtMost k) :
    F.encode.length≤F.variables+2+(8*F.variables*k+4*k+4)*F.clauses.length := by
  have h := length_encodeList_upper (encodeList encodeNat) F.clauses
    (1+(4*F.variables+2)*k) (by
      intro c hc
      exact Nat.le_trans (encode_clause_length F hf c hc)
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hw c hc)) 1))
  simp only [Input.encode,List.length_append,length_encodeNat]
  have he : 2*(1+(4*F.variables+2)*k)+2=8*F.variables*k+4*k+4 := by
    simp [Nat.mul_add,Nat.add_mul,Nat.mul_assoc]; omega
  rw [he] at h
  omega

theorem adapt_encode_length {n k : Nat} (f : CNF n) (hw : HamParity.WidthAtMost k f) :
    (adapt f).encode.length≤n+2+(8*n*k+4*k+4)*f.length := by
  have h := input_encode_length (adapt f) (adapt_wellFormed f) k (adapt_width f hw)
  exact Nat.le_trans h (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (adapt_clause_count f)) _)

theorem adapt_three_encode_length {n : Nat} (f : CNF n) (hw : HamParity.WidthAtMost 3 f) :
    (adapt f).encode.length≤n+2+(24*n+16)*f.length := by
  have h := adapt_encode_length f hw
  simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

end HamParity.Canonical
