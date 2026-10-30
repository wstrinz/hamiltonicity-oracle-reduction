module

public import HamParity.HeapTripleSearch

@[expose] public section

namespace HamParity

def HeapTriple.compressor {p : Nat} (t : HeapTriple p) : Circuit p (p+5) :=
  fullAdder t.x t.y t.z

def HeapTriple.compressed {p : Nat} (t : HeapTriple p) : List (WeightedWire (p+5)) :=
  (t.column, fullAdderSum p) :: (t.column+1, 0) :: renameHeap (shiftWire 5) t.rest

theorem HeapTriple.compressed_length {p : Nat} (t : HeapTriple p) :
    t.compressed.length + 1 = t.source.length := by
  simp [compressed, source, renameHeap]

theorem HeapTriple.compressed_mass {p : Nat} (t : HeapTriple p) :
    heapMass t.compressed = heapMass t.source := by
  simp only [compressed, source, heapMass, heapMass_rename, Nat.pow_succ]
  omega

theorem HeapTriple.compressed_value {p : Nat} (t : HeapTriple p) (a : Assignment p) :
    heapValue t.compressed (t.compressor.eval a) = heapValue t.source a := by
  have hf := congrArg (fun z => 2^t.column * z) (fullAdder_value t.x t.y t.z a)
  simp only [Nat.mul_add] at hf
  have hr : heapValue (renameHeap (shiftWire 5) t.rest) (t.compressor.eval a) =
      heapValue t.rest a := by
    rw [heapValue_rename]
    congr 1
  simp only [compressor] at hr
  simp only [compressed, source, heapValue, Nat.pow_succ, compressor, Nat.mul_assoc]
  rw [hr]
  omega

theorem compression_length_step {p : Nat} (xs : List (WeightedWire p)) (t : HeapTriple p)
    (h : findHeapTriple xs = some t) : t.compressed.length + 1 = xs.length := by
  rw [t.compressed_length]
  exact (findHeapTriple_perm xs t h).length_eq.symm

theorem compression_length_lt {p : Nat} (xs : List (WeightedWire p)) (t : HeapTriple p)
    (h : findHeapTriple xs = some t) : t.compressed.length < xs.length := by
  have hl := compression_length_step xs t h
  omega

end HamParity
