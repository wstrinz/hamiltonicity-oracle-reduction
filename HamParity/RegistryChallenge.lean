module
public import Std
public import Init.Data.Rat
public import Init.Data.Nat.Sqrt

/-! Standalone mathematical specification. Only core/Std imports are permitted.
Vertices are Fin n; m distinct edge indices carry endpoint pairs. No degree cap.
Counts include every declared wire, including unused variables. -/
@[expose] public section
namespace HamiltonicityOracle
abbrev Assignment (v : Nat) := Fin v → Bool
/-- Complete Boolean assignments, each exactly once (false branch first). -/
def assignments : (v : Nat) → List (Assignment v)
  | 0 => [Fin.elim0]
  | v+1 => (assignments v).map (fun a => Fin.cases false a) ++ (assignments v).map (fun a => Fin.cases true a)
/-- Literal is a wire index and required truth value; false means negated. -/
abbrev CNF (v : Nat) := List (List (Fin v × Bool))
def eval {v : Nat} (f : CNF v) (a : Assignment v) : Bool :=
  f.all (fun c => c.any (fun l => a l.1 == l.2))
def count {v : Nat} (f : CNF v) : Nat := (assignments v).countP (eval f)
structure Query where
  variables : Nat
  formula : CNF variables
abbrev Oracle := Query → Nat
/-- Exact integer counts, not SAT answers or approximate counts. -/
def Exact (oracle : Oracle) : Prop := ∀ q, oracle q=count q.formula
abbrev Edges (n m : Nat) := Fin m → Fin n × Fin n
def neighbors {n m : Nat} (E : Edges n m) (v : Fin n) : List (Fin n) :=
  ((List.finRange m).map E).flatMap (fun e =>
    (if e.1=v then [e.2] else []) ++ (if e.2=v then [e.1] else []))
/-- No loops or repeated undirected edges, including reversed duplicates. -/
def Simple {n m : Nat} (E : Edges n m) : Prop :=
  ∀ v, (neighbors E v).Nodup ∧ v ∉ neighbors E v
def Adj {n m : Nat} (E : Edges n m) (u v : Fin n) : Prop := v ∈ neighbors E u
def Chain {α : Type} (rel : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | a::b::xs => rel a b ∧ Chain rel (b::xs)
/-- A genuine spanning cyclic list, with length at least three. -/
def Hamiltonian {n m : Nat} (E : Edges n m) : Prop :=
  ∃ vs : List (Fin n), vs.Nodup ∧ (∀ v, v∈vs) ∧ 3≤vs.length ∧
    Chain (Adj E) vs ∧ (∀ a b, vs.head?=some a → vs.getLast?=some b → Adj E b a)
def degreeTwo {n m : Nat} (E : Edges n m) (s : Assignment m) : Bool :=
  (List.finRange n).all (fun v =>
    (((List.finRange m).filter (fun e => (E e).1 == v) ++
      (List.finRange m).filter (fun e => (E e).2 == v)).countP s) == 2)
def colorsValid {n m : Nat} (E : Edges n m) (root : Fin n)
    (s : Assignment m) (colors : Assignment n) : Bool :=
  !colors root && (((List.finRange m).filter s).map E).all
    (fun e => colors e.1 == colors e.2)
def weightSum {m : Nat} : List (Nat × Fin m) → Assignment m → Nat
  | [], _ => 0
  | (k,e)::es, s => 2^k*(if s e then 1 else 0)+weightSum es s
def edgeWeight {m : Nat} (w : Fin m → Nat) (s : Assignment m) : Nat :=
  weightSum ((List.finRange m).map (fun e => (w e,e))) s
/-- Exact filtered edge/color count. Colors are counted; deterministic CNF helpers
must add no multiplicity. Weights apply only to edge variables. -/
def filteredCount {n m : Nat} (E : Edges n m) (root : Fin n)
    (w : Fin m → Nat) (t : Nat) : Nat :=
  ((assignments m).map (fun s => (assignments n).countP (fun colors =>
    (degreeTwo E s && colorsValid E root s colors) && decide (edgeWeight w s=t)))).sum
def massWidth (s : Nat) : Nat := if s=0 then 0 else s.log2+1
def bits (n : Nat) : Nat := max 1 (massWidth ((n-1).sqrt))
def palette (n : Nat) : Nat := 2^(bits n)
def trials (n : Nat) : Nat := 2*4^(palette n)
abbrev TrialBits (L m : Nat) := Fin m → Assignment L
/-- Every fixed-length bit string decodes little-endian, without rejection. -/
def digit : (L : Nat) → Assignment L → Nat
  | 0, _ => 0
  | L+1, b => (if b 0 then 1 else 0)+2*digit L (fun i => b i.succ)
def bitGrid (L : Nat) : (m : Nat) → List (TrialBits L m)
  | 0 => [Fin.elim0]
  | m+1 => (bitGrid L m).flatMap (fun tail => (assignments L).map (fun row => Fin.cases row tail))
def repeatGrid {α : Type} (xs : List α) : Nat → List (List α)
  | 0 => [[]]
  | k+1 => (repeatGrid xs k).flatMap (fun tail => xs.map (fun x => x::tail))
def samples (n m : Nat) := repeatGrid (bitGrid (bits n) m) (trials n)
def probability {α : Type} (xs : List α) (event : α → Bool) : Rat :=
  mkRat (xs.countP event) xs.length
def variableBound (n m : Nat) := 28*m+2*n+2+5*(2*((n-1).sqrt+1)+(m+1).log2+1)
def clauseBound (n m : Nat) := 108*m+6*n+19*(2*((n-1).sqrt+1)+(m+1).log2+1)+4
end HamiltonicityOracle

namespace HamiltonicityOracle
def query {n m : Nat} (E : Edges n m) (root : Fin n) (w : Fin m → Nat) (t : Nat) : Query := by sorry

/-- Finite disjunction over prescribed queries, including both bucket endpoints. No execution-cost claim. -/
abbrev run {n m : Nat} (E : Edges n m) (root : Fin n) (oracle : Oracle)
    (xs : List (TrialBits (bits n) m)) : Bool :=
  xs.any (fun b => (List.range (n*2^(palette n-1)+1)).any (fun t =>
    decide (oracle (query E root (fun e => digit (bits n) (b e)) t)%2=1)))
/-- Prescribed full-scan query slots; short-circuit evaluation may use fewer. -/
def calls (n : Nat) {m : Nat} (xs : List (TrialBits (bits n) m)) : Nat :=
  xs.length*(n*2^(palette n-1)+1)

theorem query_exact_count {n m : Nat} (E : Edges n m) (root : Fin n)
    (w : Fin m → Nat) (t : Nat) : count (query E root w t).formula=filteredCount E root w t := by sorry

theorem query_size {n m : Nat} (E : Edges n m) (root : Fin n)
    (w : Fin m → Nat) (hw : ∀ e, w e<palette n) (t : Nat) :
    (query E root w t).variables≤variableBound n m ∧
    (query E root w t).formula.length≤clauseBound n m ∧
    (∀ c∈(query E root w t).formula, c.length≤3) := by sorry

theorem fair_sample_space (n m : Nat) :
    (samples n m).Nodup ∧ (samples n m).length=2^(trials n*m*bits n) ∧
    (∀ xs : List (TrialBits (bits n) m), xs∈samples n m ↔ xs.length=trials n) := by sorry

theorem finite_oracle_reduction {n m : Nat} (E : Edges n m)
    (hs : Simple E) (root : Fin n) (hn : 3≤n) (oracle : Oracle) (ho : Exact oracle) :
    (∀ xs, run E root oracle xs=true → Hamiltonian E) ∧
    (Hamiltonian E → probability (samples n m) (fun xs => !(run E root oracle xs))≤mkRat 1 3) ∧
    (∀ xs∈samples n m, calls n xs=trials n*(n*2^(palette n-1)+1) ∧
      calls n xs≤(n+1)*2^(6*((n-1).sqrt)+7)) := by sorry

end HamiltonicityOracle
