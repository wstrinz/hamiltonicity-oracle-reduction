module

public import HamParity.CanonicalCNF

/-! Bit primitives mirror Encoding.lean at OAI pin 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a.
The local canonical record is a sorted-list representative, not imported Finset. -/
@[expose] public section
namespace HamParity.Canonical

def encodeNat (n : Nat) : List Bool := List.replicate n true ++ [false]
def readNat : List Bool → Option (Nat × List Bool)
  | [] => none
  | false::rest => some (0,rest)
  | true::rest => do
      let (n,tail) ← readNat rest
      pure (n+1,tail)

theorem readNat_encodeNat_append (n : Nat) (rest : List Bool) :
    readNat (encodeNat n ++ rest)=some (n,rest) := by
  induction n with
  | zero => simp [encodeNat,readNat]
  | succ n ih =>
      change (readNat (encodeNat n ++ rest)).bind (fun p => some (p.1+1,p.2)) = some (n+1,rest)
      rw [ih]; rfl

theorem encodeNat_injective (n m : Nat) (h : encodeNat n=encodeNat m) : n=m := by
  have he := congrArg (fun bits => readNat (bits++[])) h
  rw [readNat_encodeNat_append,readNat_encodeNat_append] at he
  exact congrArg Prod.fst (Option.some.inj he)

def frame (bits : List Bool) : List Bool := bits.foldr (fun b rest => true::b::rest) [false]
def readFrame : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false::rest => some ([],rest)
  | true::[] => none
  | true::b::rest => do
      let (bs,tail) ← readFrame rest
      pure (b::bs,tail)

theorem readFrame_frame_append (bits rest : List Bool) :
    readFrame (frame bits ++ rest)=some (bits,rest) := by
  induction bits with
  | nil => simp [frame,readFrame]
  | cons b bits ih =>
      change (readFrame (frame bits ++ rest)).bind (fun p => some (b::p.1,p.2)) = some (b::bits,rest)
      rw [ih]; rfl

theorem frame_append_injective (bits bits' rest rest' : List Bool)
    (h : frame bits ++ rest=frame bits' ++ rest') : bits=bits' ∧ rest=rest' := by
  have he := congrArg readFrame h
  rw [readFrame_frame_append,readFrame_frame_append] at he
  exact Prod.mk.inj (Option.some.inj he)

def encodeList {α : Type} (enc : α → List Bool) : List α → List Bool
  | [] => [false]
  | a::as => true::(frame (enc a) ++ encodeList enc as)

theorem encodeList_injective {α : Type} (enc : α → List Bool)
    (hi : ∀ a b,enc a=enc b → a=b) (xs ys : List α)
    (h : encodeList enc xs=encodeList enc ys) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [encodeList]
  | cons x xs ih =>
      cases ys with
      | nil => simp [encodeList] at h
      | cons y ys =>
          have he : frame (enc x) ++ encodeList enc xs=frame (enc y) ++ encodeList enc ys :=
            (List.cons.inj h).2
          obtain ⟨hx,ht⟩ := frame_append_injective _ _ _ _ he
          rw [hi x y hx,ih ys ht]

def Input.encode (F : Input) : List Bool :=
  encodeNat F.variables ++ encodeList (encodeList encodeNat) F.clauses

theorem readNat_encode (F : Input) : readNat F.encode=
    some (F.variables,encodeList (encodeList encodeNat) F.clauses) :=
  readNat_encodeNat_append _ _

theorem input_encode_injective (F G : Input) (h : F.encode=G.encode) : F=G := by
  have he := congrArg readNat h
  rw [readNat_encode,readNat_encode] at he
  obtain ⟨hv,hc⟩ := Prod.mk.inj (Option.some.inj he)
  have hl := encodeList_injective (encodeList encodeNat)
    (fun a b hab => encodeList_injective encodeNat encodeNat_injective a b hab) _ _ hc
  cases F; cases G; cases hv; cases hl; rfl

theorem adapt_encoded_header {n : Nat} (f : CNF n) :
    readNat (adapt f).encode=some (n,encodeList (encodeList encodeNat) (cnfNumbers f)) :=
  readNat_encode _

end HamParity.Canonical
