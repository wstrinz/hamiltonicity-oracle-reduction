module

public import HamParity.WeightedBucketCNF

/-! Unelaborated examples. Counts reduce to primary assignments, not helpers. -/
@[expose] public section
namespace HamParity.WeightedBucketExamples

def sparseGap : List (WeightedWire 2) := [(0,0),(4,1)]
def aliases : List (WeightedWire 1) := [(0,0),(0,0),(0,0)]
def carryChain : List (WeightedWire 1) := [(0,0),(1,0),(0,0),(1,0),(0,0)]

theorem gap_seventeen : modelCount (weightedBucketCNF sparseGap 17)=1 := by
  rw [weightedBucketCNF_count]; decide
theorem gap_impossible : modelCount (weightedBucketCNF sparseGap 2)=0 := by
  rw [weightedBucketCNF_count]; decide
theorem alias_three : modelCount (weightedBucketCNF aliases 3)=1 := by
  rw [weightedBucketCNF_count]; decide
theorem alias_one_impossible : modelCount (weightedBucketCNF aliases 1)=0 := by
  rw [weightedBucketCNF_count]; decide
theorem chain_seven : modelCount (weightedBucketCNF carryChain 7)=1 := by
  rw [weightedBucketCNF_count]; decide
theorem matching_low_bits_out_of_range : modelCount (weightedBucketCNF aliases 11)=0 := by
  rw [weightedBucketCNF_count]; decide
theorem empty_unused : modelCount (weightedBucketCNF ([] : List (WeightedWire 3)) 0)=8 := by
  rw [weightedBucketCNF_count]; decide
theorem empty_no_inputs : modelCount (weightedBucketCNF ([] : List (WeightedWire 0)) 0)=1 := by
  rw [weightedBucketCNF_count]; decide
theorem empty_nonzero : modelCount (weightedBucketCNF ([] : List (WeightedWire 0)) 1)=0 := by
  rw [weightedBucketCNF_count]; decide
theorem empty_two_helpers : (buildWeighted ([] : List (WeightedWire 0))).wires=2 := by
  rw [buildWeighted_variables]
  rw [normalizeHeap.eq_def]
  rfl

end HamParity.WeightedBucketExamples
