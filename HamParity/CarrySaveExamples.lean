module

public import HamParity.CarrySaveNormalize

@[expose] public section

namespace HamParity.CarrySaveExamples

def aliases : List (WeightedWire 1) := [(0,0),(0,0),(0,0)]
def cascade : List (WeightedWire 1) := [(0,0),(1,0),(0,0),(1,0),(0,0)]
def fallback : List (WeightedWire 1) := [(5,0),(0,0),(1,0),(0,0),(0,0)]
def fallbackSecond : List (WeightedWire 1) := [(5,0),(0,0),(5,0),(0,0),(0,0)]

theorem aliases_one_step : (normalizeHeap aliases).steps = 1 := by
  rw [normalizeHeap.eq_def]
  dsimp [aliases, findHeapTriple, takeColumn, HeapTriple.compressed, renameHeap, List.map, HeapTriple.prepend, Option.map]
  rw [normalizeHeap.eq_def]
  dsimp [aliases, findHeapTriple, takeColumn, HeapTriple.compressed, renameHeap, List.map, HeapTriple.prepend, Option.map]
theorem cascade_two_steps : (normalizeHeap cascade).steps = 2 := by
  rw [normalizeHeap.eq_def]
  dsimp [cascade, findHeapTriple, takeColumn, HeapTriple.compressed, renameHeap, List.map, HeapTriple.prepend, Option.map]
  rw [normalizeHeap.eq_def]
  dsimp [cascade, findHeapTriple, takeColumn, HeapTriple.compressed, renameHeap, List.map, HeapTriple.prepend, Option.map]
  rw [normalizeHeap.eq_def]
  dsimp [cascade, findHeapTriple, takeColumn, HeapTriple.compressed, renameHeap, List.map, HeapTriple.prepend, Option.map]
theorem fallback_one_step : (normalizeHeap fallback).steps = 1 := by
  rw [normalizeHeap.eq_def]
  dsimp [fallback, findHeapTriple, takeColumn, HeapTriple.compressed, renameHeap, List.map, HeapTriple.prepend, Option.map]
  rw [normalizeHeap.eq_def]
  dsimp [fallback, findHeapTriple, takeColumn, HeapTriple.compressed, renameHeap, List.map, HeapTriple.prepend, Option.map]
theorem second_search_failure_restores_occurrences :
    heapMass (normalizeHeap fallbackSecond).heap = 67 ∧
      (normalizeHeap fallbackSecond).steps = 1 := by
  constructor
  · rw [normalizeHeap_mass]; decide
  · rw [normalizeHeap.eq_def]
    dsimp [fallbackSecond, findHeapTriple, takeColumn, HeapTriple.compressed, renameHeap, List.map, HeapTriple.prepend, Option.map]
    rw [normalizeHeap.eq_def]
    dsimp [fallbackSecond, findHeapTriple, takeColumn, HeapTriple.compressed, renameHeap, List.map, HeapTriple.prepend, Option.map]

theorem cascade_mass : heapMass (normalizeHeap cascade).heap = 7 := by
  rw [normalizeHeap_mass]
  decide

theorem fallback_mass : heapMass (normalizeHeap fallback).heap = 37 := by
  rw [normalizeHeap_mass]
  decide

theorem cascade_true_value :
    heapValue (normalizeHeap cascade).heap ((normalizeHeap cascade).circuit.eval (fun _ => true)) = 7 := by
  rw [normalizeHeap_value]
  decide

theorem empty_no_helpers : (normalizeHeap ([] : List (WeightedWire 0))).wires = 0 := by
  rw [normalizeHeap.eq_def]
  rfl

end HamParity.CarrySaveExamples
