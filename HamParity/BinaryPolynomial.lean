module

public import HamParity.WeightedGraph

/-! Finite F2 coefficient vectors with an explicit support bound. Equality of
representations is not used: trailing zero bounds may differ. Draft until checked. -/
@[expose] public section
namespace HamParity

structure BinaryPolynomial where
  bound : Nat
  coeff : Nat → Bool
  beyond : ∀ i, bound ≤ i → coeff i=false

namespace BinaryPolynomial

def Nonzero (p : BinaryPolynomial) : Prop := ∃ i, p.coeff i=true
def nonzeroB (p : BinaryPolynomial) : Bool := (List.range p.bound).any p.coeff

theorem nonzeroB_iff (p : BinaryPolynomial) : p.nonzeroB=true ↔ p.Nonzero := by
  rw [nonzeroB, List.any_eq_true]
  constructor
  · rintro ⟨i,_,hi⟩; exact ⟨i,hi⟩
  · rintro ⟨i,hi⟩
    have hb : i<p.bound := by
      by_cases h : i<p.bound
      · exact h
      · have hz := p.beyond i (by omega)
        simp [hz] at hi
    exact ⟨i,List.mem_range.mpr hb,hi⟩

theorem nonzeroB_false_iff (p : BinaryPolynomial) :
    p.nonzeroB=false ↔ ∀ i, p.coeff i=false := by
  constructor
  · intro h i
    cases hi : p.coeff i with
    | false => rfl
    | true => have hn := p.nonzeroB_iff.mpr ⟨i,hi⟩; simp [h] at hn
  · intro h
    apply Bool.eq_false_iff.mpr
    intro hn
    obtain ⟨i,hi⟩ := p.nonzeroB_iff.mp hn
    simp [h i] at hi

def zero : BinaryPolynomial := ⟨0,fun _ => false,fun _ _ => rfl⟩

def monomial (k : Nat) : BinaryPolynomial :=
  ⟨k+1,fun i => decide (i=k),by intro i hi; simp; omega⟩

def add (p q : BinaryPolynomial) : BinaryPolynomial :=
  ⟨max p.bound q.bound,fun i => p.coeff i ^^ q.coeff i,by
    intro i hi
    rw [p.beyond i (by omega),q.beyond i (by omega)]
    rfl⟩

/-- Multiplication by z^k, with no quotient/reduction of exponents. -/
def shift (k : Nat) (p : BinaryPolynomial) : BinaryPolynomial :=
  ⟨k+p.bound,fun i => if k≤i then p.coeff (i-k) else false,by
    intro i hi
    have hk : k≤i := by omega
    simp only [if_pos hk]
    exact p.beyond (i-k) (by omega)⟩

theorem add_coeff (p q : BinaryPolynomial) (i : Nat) :
    (p.add q).coeff i = (p.coeff i ^^ q.coeff i) := rfl

theorem add_zero_iff (p q : BinaryPolynomial) :
    (p.add q).nonzeroB=false ↔ ∀ i, p.coeff i=q.coeff i := by
  rw [nonzeroB_false_iff]
  constructor <;> intro h i
  · have hi := h i
    change (p.coeff i ^^ q.coeff i)=false at hi
    cases hp : p.coeff i <;> cases hq : q.coeff i <;> simp_all
  · change (p.coeff i ^^ q.coeff i)=false
    rw [h i]
    exact Bool.xor_self _

theorem shift_coeff_add (p : BinaryPolynomial) (k i : Nat) :
    (p.shift k).coeff (k+i)=p.coeff i := by simp [shift]

theorem exists_top (p : BinaryPolynomial) (hn : p.Nonzero) :
    ∃ d, p.coeff d=true ∧ ∀ i, d<i → p.coeff i=false := by
  have aux : ∀ b, (∀ i, b≤i → p.coeff i=false) → p.Nonzero →
      ∃ d, p.coeff d=true ∧ ∀ i, d<i → p.coeff i=false := by
    intro b
    induction b with
    | zero =>
        intro hb hn
        obtain ⟨i,hi⟩ := hn
        simp [hb i (by omega)] at hi
    | succ b ih =>
        intro hb hn
        cases h : p.coeff b with
        | true => exact ⟨b,h,fun i hi => hb i (by omega)⟩
        | false =>
            apply ih
            · intro i hi
              by_cases he : i=b
              · simpa [he] using h
              · exact hb i (by omega)
            · exact hn
  exact aux p.bound p.beyond hn

theorem shifts_distinct (p : BinaryPolynomial) (hn : p.Nonzero) (k l : Nat)
    (he : ∀ i, (p.shift k).coeff i=(p.shift l).coeff i) : k=l := by
  obtain ⟨d,hd,hmax⟩ := p.exists_top hn
  have no_lt : ∀ a b, a<b → (∀ i, (p.shift a).coeff i=(p.shift b).coeff i) → False := by
    intro a b hab hh
    have hleft : (p.shift a).coeff (b+d)=false := by
      simp only [shift, if_pos (by omega : a≤b+d)]
      exact hmax _ (by omega)
    have hright : (p.shift b).coeff (b+d)=true := by rw [shift_coeff_add,hd]
    have heq := hh (b+d)
    simp [hleft,hright] at heq
  by_cases hkl : k<l
  · exact False.elim (no_lt k l hkl he)
  · by_cases hlk : l<k
    · exact False.elim (no_lt l k hlk (fun i => (he i).symm))
    · omega

def sumMonomials : List Nat → BinaryPolynomial
  | [] => zero
  | k::ks => (monomial k).add (sumMonomials ks)

theorem parity_xor (a b : Nat) :
    (decide (a%2=1) ^^ decide (b%2=1)) = decide ((a+b)%2=1) := by
  have ha := Nat.mod_lt a (by decide : 0<2)
  have hb := Nat.mod_lt b (by decide : 0<2)
  have ha' : a%2=0 ∨ a%2=1 := by omega
  have hb' : b%2=0 ∨ b%2=1 := by omega
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;>
    simp [Nat.add_mod,ha',hb']

theorem sumMonomials_coeff (ks : List Nat) (i : Nat) :
    (sumMonomials ks).coeff i = decide (ks.countP (fun k => k==i)%2=1) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      simp only [sumMonomials,add_coeff,monomial,ih,List.countP_cons]
      by_cases h : k=i
      · simp only [h,decide_true,beq_self_eq_true,ite_true]
        simpa [Nat.add_comm] using parity_xor 1 (ks.countP (fun k => k==i))
      · have hr : i≠k := Ne.symm h
        simp [h,hr]

end BinaryPolynomial
end HamParity
