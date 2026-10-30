module

public import HamParity.Counting

@[expose] public section

namespace HamParity

def joinAssignment {m n : Nat} (s : Assignment m) (a : Assignment n) : Assignment (m+n) :=
  Fin.addCases s a

def leftAssignment {m n : Nat} (a : Assignment (m+n)) : Assignment m :=
  fun i => a (Fin.castAdd n i)

def rightAssignment {m n : Nat} (a : Assignment (m+n)) : Assignment n :=
  fun i => a (Fin.natAdd m i)

@[simp] theorem left_join {m n : Nat} (s : Assignment m) (a : Assignment n) :
    leftAssignment (joinAssignment s a) = s := by
  funext i
  simp [leftAssignment, joinAssignment]

@[simp] theorem right_join {m n : Nat} (s : Assignment m) (a : Assignment n) :
    rightAssignment (joinAssignment s a) = a := by
  funext i
  simp [rightAssignment, joinAssignment, Fin.addCases_right]

theorem join_split {m n : Nat} (a : Assignment (m+n)) :
    joinAssignment (leftAssignment a) (rightAssignment a) = a := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [joinAssignment, leftAssignment]
  · simp [joinAssignment, rightAssignment, Fin.addCases_right]

theorem join_left_eq {m n : Nat} {s t : Assignment m} {a b : Assignment n}
    (h : joinAssignment s a = joinAssignment t b) : s = t := by
  simpa only [left_join] using congrArg leftAssignment h

theorem join_right_eq {m n : Nat} {s t : Assignment m} {a b : Assignment n}
    (h : joinAssignment s a = joinAssignment t b) : a = b := by
  simpa only [right_join] using congrArg rightAssignment h

def splitAssignments (m n : Nat) : List (Assignment (m+n)) :=
  (assignments m).flatMap (fun s => (assignments n).map (joinAssignment s))

theorem splitAssignments_nodup (m n : Nat) : (splitAssignments m n).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro s _
    apply List.pairwise_map.mpr
    exact (assignments_nodup n).imp (fun hne heq => hne (join_right_eq heq))
  · apply (assignments_nodup m).imp
    intro s t hne x hx y hy heq
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy
    exact hne (join_left_eq heq)

theorem assignments_split_perm (m n : Nat) :
    (assignments (m+n)).Perm (splitAssignments m n) := by
  apply (List.perm_ext_iff_of_nodup (assignments_nodup _) (splitAssignments_nodup m n)).mpr
  intro a
  constructor
  · intro _
    exact List.mem_flatMap.mpr ⟨leftAssignment a, assignments_complete _,
      List.mem_map.mpr ⟨rightAssignment a, assignments_complete _, join_split a⟩⟩
  · intro _
    exact assignments_complete a

theorem count_split_assignments {m n : Nat} (p : Assignment (m+n) → Bool) :
    (assignments (m+n)).countP p =
      ((assignments m).map (fun s =>
        (assignments n).countP (fun a => p (joinAssignment s a)))).sum := by
  rw [(assignments_split_perm m n).countP_eq p]
  simp [splitAssignments, List.countP_flatMap, List.countP_map, Function.comp_def]

end HamParity
