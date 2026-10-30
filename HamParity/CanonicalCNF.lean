module

public import HamParity.CanonicalSets

/-! Numbered finite-set mirror of the pinned external interface. No equality to
the external Mathlib Finset type is asserted without a separate compiled bridge. -/
@[expose] public section
namespace HamParity.Canonical

def literalCode {n : Nat} (l : Literal n) : Nat := 2*l.wire.val + if l.positive then 1 else 0

theorem literalCode_lt {n : Nat} (l : Literal n) : literalCode l<2*n := by
  have h := l.wire.isLt
  cases hp : l.positive <;> simp [literalCode,hp] <;> omega

theorem literalCode_injective {n : Nat} (a b : Literal n) (h : literalCode a=literalCode b) : a=b := by
  obtain ⟨av,ap⟩ := a; obtain ⟨bv,bp⟩ := b
  cases ap <;> cases bp <;> simp [literalCode] at h
  · have he : av=bv := Fin.ext (by omega); cases he; rfl
  · omega
  · omega
  · have he : av=bv := Fin.ext (by omega); cases he; rfl

def clauseNumbers {n : Nat} (c : Clause n) : List Nat := canonical (c.map literalCode)
def cnfNumbers {n : Nat} (f : CNF n) : List (List Nat) := canonical (f.map clauseNumbers)

structure Input where
  variables : Nat
  clauses : List (List Nat)
  deriving DecidableEq

def Input.WellFormed (F : Input) : Prop :=
  F.clauses.Nodup ∧ F.clauses.Pairwise (·≤·) ∧
  ∀ c∈F.clauses,c.Nodup ∧ c.Pairwise (·≤·) ∧ ∀ j∈c,j<2*F.variables

def adapt {n : Nat} (f : CNF n) : Input := ⟨n,cnfNumbers f⟩

theorem adapt_variables {n : Nat} (f : CNF n) : (adapt f).variables=n := rfl

theorem clauseNumbers_mem {n : Nat} (c : Clause n) (j : Nat) :
    j∈clauseNumbers c ↔ ∃ l∈c,literalCode l=j := by simp [clauseNumbers,mem_canonical]

theorem cnfNumbers_mem {n : Nat} (f : CNF n) (c : List Nat) :
    c∈cnfNumbers f ↔ ∃ d∈f,clauseNumbers d=c := by simp [cnfNumbers,mem_canonical]

theorem adapt_wellFormed {n : Nat} (f : CNF n) : (adapt f).WellFormed := by
  refine ⟨canonical_nodup _,canonical_sorted (fun _ _ _ => List.le_trans) List.le_total _,?_⟩
  intro c hc
  obtain ⟨d,hd,rfl⟩ := (cnfNumbers_mem f c).mp hc
  refine ⟨canonical_nodup _,canonical_sorted (fun _ _ _ => Nat.le_trans) Nat.le_total _,?_⟩
  intro j hj
  obtain ⟨l,hl,rfl⟩ := (clauseNumbers_mem d j).mp hj
  exact literalCode_lt l

theorem clauseNumbers_length {n : Nat} (c : Clause n) : (clauseNumbers c).length≤c.length := by
  simpa [clauseNumbers] using canonical_length (c.map literalCode)

theorem adapt_clause_count {n : Nat} (f : CNF n) : (adapt f).clauses.length≤f.length := by
  simpa [adapt,cnfNumbers] using canonical_length (f.map clauseNumbers)

def Input.WidthAtMost (k : Nat) (F : Input) : Prop := ∀ c∈F.clauses,c.length≤k

theorem adapt_width {n k : Nat} (f : CNF n) (hw : HamParity.WidthAtMost k f) :
    (adapt f).WidthAtMost k := by
  intro c hc
  obtain ⟨d,hd,rfl⟩ := (cnfNumbers_mem f c).mp hc
  exact Nat.le_trans (clauseNumbers_length d) (hw d hd)

def evalCode {n : Nat} (a : Assignment n) (j : Nat) : Bool :=
  if h : j/2<n then a ⟨j/2,h⟩ == decide (j%2=1) else false

theorem evalCode_literal {n : Nat} (a : Assignment n) (l : Literal n) :
    evalCode a (literalCode l)=l.eval a := by
  obtain ⟨v,b⟩ := l
  have hd : (2*v.val+1)/2=v.val := by omega
  cases b <;> simp [literalCode,evalCode,Literal.eval,v.isLt,hd]

def Input.eval (F : Input) (a : Assignment F.variables) : Bool :=
  F.clauses.all (fun c => c.any (evalCode a))

theorem clauseNumbers_eval {n : Nat} (c : Clause n) (a : Assignment n) :
    (clauseNumbers c).any (evalCode a)=c.eval a := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,Clause.eval,clauseNumbers_mem]
  constructor
  · rintro ⟨j,⟨l,hl,rfl⟩,he⟩
    exact ⟨l,hl,(evalCode_literal a l) ▸ he⟩
  · rintro ⟨l,hl,he⟩
    exact ⟨literalCode l,⟨l,hl,rfl⟩,(evalCode_literal a l).symm ▸ he⟩

theorem adapt_eval {n : Nat} (f : CNF n) (a : Assignment n) :
    (adapt f).eval a=f.eval a := by
  apply Bool.eq_iff_iff.mpr
  simp only [Input.eval,adapt,List.all_eq_true,CNF.eval,cnfNumbers_mem]
  constructor
  · intro h c hc
    have he := h (clauseNumbers c) ⟨c,hc,rfl⟩
    rwa [clauseNumbers_eval] at he
  · intro h c hc
    obtain ⟨d,hd,rfl⟩ := hc
    rw [clauseNumbers_eval]
    exact h d hd

def Input.count (F : Input) : Nat := (assignments F.variables).countP F.eval

theorem adapt_count {n : Nat} (f : CNF n) : (adapt f).count=modelCount f := by
  unfold Input.count modelCount countModels
  apply List.countP_congr
  intro a ha
  rw [adapt_eval f a]
  simp

theorem empty_declared_count (n : Nat) : (adapt ([] : CNF n)).count=2^n := by
  rw [adapt_count]
  simp [modelCount,countModels,CNF.eval,assignments_length]

end HamParity.Canonical
