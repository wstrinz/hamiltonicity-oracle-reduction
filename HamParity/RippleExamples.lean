module

public import HamParity.RippleBucketCNF

@[expose] public section

namespace HamParity.RippleExamples

def aliased : List (Fin 1 × Fin 1) := [(0, 0)]

theorem alias_zero : modelCount (rippleCNF aliased 0) = 1 := by
  rw [rippleCNF_count]
  decide

theorem retained_carry : modelCount (rippleCNF aliased 2) = 1 := by
  rw [rippleCNF_count]
  decide

theorem impossible_low_bit : modelCount (rippleCNF aliased 1) = 0 := by
  rw [rippleCNF_count]
  decide

/-- Four has the same two low bits as zero, but must be rejected. -/
theorem reject_out_of_range : modelCount (rippleCNF aliased 4) = 0 := by
  rw [rippleCNF_count]
  decide

def threeColumns : List (Fin 1 × Fin 1) := [(0, 0), (0, 0), (0, 0)]

theorem carries_across_columns : modelCount (rippleCNF threeColumns 14) = 1 := by
  rw [rippleCNF_count]
  decide

theorem empty_rows_count_unused_inputs :
    modelCount (rippleCNF ([] : List (Fin 3 × Fin 3)) 0) = 8 := by
  rw [rippleCNF_count]
  decide

theorem empty_rows_reject_one :
    modelCount (rippleCNF ([] : List (Fin 3 × Fin 3)) 1) = 0 := by
  rw [rippleCNF_count]
  decide

theorem no_primary_inputs :
    modelCount (rippleCNF ([] : List (Fin 0 × Fin 0)) 0) = 1 := by
  rw [rippleCNF_count]
  decide

end HamParity.RippleExamples
