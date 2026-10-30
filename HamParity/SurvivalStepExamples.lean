module

public import HamParity.CycleBucketPolynomial

@[expose] public section
namespace HamParity.SurvivalStepExamples
open BinaryPolynomial

theorem equal_monomials_cancel : (sumMonomials [3,3]).nonzeroB=false := by decide
theorem different_monomials_survive : (sumMonomials [3,4]).nonzeroB=true := by decide
theorem one_bad_choice_in_four :
    (List.finRange 4).countP (fun j => (monomialTrial (monomial 0) (monomial 4) j.val).nonzeroB)=3 := by decide
theorem no_bad_choice_in_four :
    (List.finRange 4).countP (fun j => (monomialTrial (monomial 0) zero j.val).nonzeroB)=4 := by decide
theorem zero_Q_really_needed :
    (List.finRange 4).countP (fun j => (monomialTrial zero zero j.val).nonzeroB)=0 := by decide
theorem D_one_may_fail :
    (List.finRange 1).countP (fun j => (monomialTrial (monomial 0) (monomial 1) j.val).nonzeroB)=0 := by decide
theorem D_zero_empty :
    (List.finRange 0).countP (fun j => (monomialTrial (monomial 0) zero j.val).nonzeroB)=0 := by decide

theorem triangle_selected_cardinality :
    (List.finRange 3).countP (fun _ => true)=3 := by
  apply SelectionExamples.triangle.degreeTwo_selected_cardinality
  decide

theorem loop_selected_cardinality :
    (List.finRange 1).countP (fun _ => true)=1 := by
  apply SelectionExamples.oneLoop.degreeTwo_selected_cardinality
  decide

end HamParity.SurvivalStepExamples
