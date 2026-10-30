module

public import HamParity.DecisionAmplification

@[expose] public section
namespace HamParity

def paletteWidth (D : Nat) : Nat := massWidth (D-1)
def encodePalette {D : Nat} (j : Fin D) : Fin (paletteWidth D) → Bool :=
  fun i => j.val.testBit i.val

theorem paletteWidth_eq (D : Nat) (hD : 2≤D) : paletteWidth D=(D-1).log2+1 := by
  simp [paletteWidth,massWidth,show D-1≠0 by omega]

theorem paletteDigit_bound {D : Nat} (hD : 2≤D) (j : Fin D) : j.val<2^(paletteWidth D) := by
  rw [paletteWidth_eq D hD]
  have h : D-1<2^((D-1).log2+1) := Nat.lt_log2_self
  have hj := j.isLt
  omega

theorem encodePalette_injective {D : Nat} (hD : 2≤D) (a b : Fin D)
    (he : encodePalette a=encodePalette b) : a=b := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<paletteWidth D
  · exact congrFun he ⟨i,hi⟩
  · have hp : 2^(paletteWidth D)≤2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (paletteDigit_bound hD a) hp),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (paletteDigit_bound hD b) hp)]

def paletteMatch {D : Nat} (j : Fin D) (bits : Fin (paletteWidth D) → Bool) : Bool :=
  (List.finRange (paletteWidth D)).all (fun i => encodePalette j i==bits i)

theorem paletteMatch_iff {D : Nat} (j : Fin D) (bits : Fin (paletteWidth D) → Bool) :
    paletteMatch j bits=true ↔ encodePalette j=bits := by
  simp only [paletteMatch,List.all_eq_true,beq_iff_eq]
  constructor
  · intro h; funext i; exact h i (by simp)
  · intro h i hi; exact congrFun h i

/-- Finite decoder rejects invalid words. It is not a random-bit sampler. -/
def decodePalette {D : Nat} (bits : Fin (paletteWidth D) → Bool) : Option (Fin D) :=
  (List.finRange D).find? (fun j => paletteMatch j bits)

theorem decodePalette_encode {D : Nat} (hD : 2≤D) (j : Fin D) :
    decodePalette (encodePalette j)=some j := by
  cases hd : decodePalette (encodePalette j) with
  | none =>
      have hn := List.find?_eq_none.mp hd j (by simp)
      exact False.elim (hn ((paletteMatch_iff j _).mpr rfl))
  | some k =>
      have hk := List.find?_some hd
      have he := (paletteMatch_iff k _).mp hk
      have hj := encodePalette_injective hD k j he
      simpa [hj] using hd

theorem decodePalette_some_iff {D : Nat} (hD : 2≤D) (bits : Fin (paletteWidth D) → Bool)
    (j : Fin D) : decodePalette bits=some j ↔ encodePalette j=bits := by
  constructor
  · intro h
    have hf := List.find?_some (p:=fun k : Fin D => paletteMatch k bits) (a:=j) h
    exact (paletteMatch_iff j bits).mp hf
  · intro h; rw [← h]; exact decodePalette_encode hD j

def paletteWord {D : Nat} (j : Fin D) : List Bool :=
  (List.finRange (paletteWidth D)).map (encodePalette j)

theorem paletteWord_length {D : Nat} (j : Fin D) : (paletteWord j).length=paletteWidth D := by
  simp [paletteWord]

theorem paletteWord_injective {D : Nat} (hD : 2≤D) (a b : Fin D)
    (h : paletteWord a=paletteWord b) : a=b := by
  apply encodePalette_injective hD a b
  funext i
  exact List.map_inj_left.mp h i (by simp)

/-- Fixed rectangular description, one width-L bit row per edge. -/
def trialDescription {m D : Nat} (w : Fin m → Fin D) : List (List Bool) :=
  (List.finRange m).map (fun e => paletteWord (w e))

theorem trialDescription_rows {m D : Nat} (w : Fin m → Fin D) :
    (trialDescription w).length=m := by simp [trialDescription]

theorem trialDescription_bits {m D : Nat} (w : Fin m → Fin D) :
    (trialDescription w).flatten.length=m*paletteWidth D := by
  simp [trialDescription,List.length_flatten,List.map_map,Function.comp_def,
    paletteWord_length,sum_map_constant]

theorem trialDescription_injective {m D : Nat} (hD : 2≤D) (a b : Fin m → Fin D)
    (h : trialDescription a=trialDescription b) : a=b := by
  funext e
  exact paletteWord_injective hD (a e) (b e) (List.map_inj_left.mp h e (by simp))

def repeatedDescription {m D : Nat} (ws : List (Fin m → Fin D)) : List (List (List Bool)) :=
  ws.map trialDescription

theorem repeatedDescription_injective {m D : Nat} (hD : 2≤D) (xs ys : List (Fin m → Fin D))
    (h : repeatedDescription xs=repeatedDescription ys) : xs=ys :=
  List.map_inj_right (fun a b he => trialDescription_injective hD a b he) |>.mp h

theorem repeatedDescription_bits {m D : Nat} (ws : List (Fin m → Fin D)) :
    (repeatedDescription ws).flatten.flatten.length=ws.length*m*paletteWidth D := by
  induction ws with
  | nil => simp [repeatedDescription]
  | cons w ws ih =>
      change ((trialDescription w ++ (repeatedDescription ws).flatten).flatten).length=
        (ws.length+1)*m*paletteWidth D
      rw [List.flatten_append,List.length_append,trialDescription_bits,ih]
      simp [Nat.add_mul,Nat.add_comm]

theorem random_description_budget {m D k : Nat} (ws : List (Fin m → Fin D))
    (hw : ws∈repeatGrid (paletteGrid D m) k) :
    (repeatedDescription ws).flatten.flatten.length=k*m*paletteWidth D := by
  rw [repeatedDescription_bits,repeatGrid_member_length _ k ws hw]

end HamParity
