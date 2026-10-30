module

public import HamParity.Counting


/-! Rooted binary colorings of a finite partition. A component numbering and
representatives describe the partition, not a coloring bijection. The coloring
bijection, enumeration, and exact count are derived below. Draft until checked. -/

@[expose] public section

namespace HamParity

structure RootedPartition (n k : Nat) (root : Fin n) where
  label : Fin n → Fin (k+1)
  representative : Fin (k+1) → Fin n
  label_representative : ∀ i, label (representative i) = i
  label_root : label root = 0


namespace RootedPartition

variable {n k : Nat} {root : Fin n} (P : RootedPartition n k root)

def Valid (a : Assignment n) : Prop :=
  a root = false ∧ ∀ u v, P.label u = P.label v → a u = a v

def validB (a : Assignment n) : Bool :=
  decide (a root = false ∧ ∀ u v, P.label u = P.label v → a u = a v)

theorem validB_iff (a : Assignment n) : P.validB a = true ↔ P.Valid a := by
  simp [validB, Valid]


def lift (b : Assignment k) : Assignment n :=
  fun v => consAssignment false b (P.label v)

def lower (a : Assignment n) : Assignment k :=
  fun i => a (P.representative i.succ)

theorem lower_lift (b : Assignment k) : P.lower (P.lift b) = b := by
  funext i
  simp [lower, lift, P.label_representative]

theorem lift_injective {b c : Assignment k} (h : P.lift b = P.lift c) : b = c := by
  simpa only [P.lower_lift] using congrArg P.lower h

theorem lift_valid (b : Assignment k) : P.Valid (P.lift b) := by
  constructor
  · simp [lift, P.label_root]
  · intro u v h
    simp only [lift, h]

theorem lift_lower (a : Assignment n) (ha : P.Valid a) : P.lift (P.lower a) = a := by
  funext v
  rcases Fin.eq_zero_or_eq_succ (P.label v) with hv | ⟨i, hi⟩
  · have hc : a v = a root := ha.2 v root (hv.trans P.label_root.symm)
    simpa [lift, hv] using (hc.trans ha.1).symm
  · have hc : a v = a (P.representative i.succ) :=
      ha.2 v (P.representative i.succ) (hi.trans (P.label_representative i.succ).symm)
    simpa [lift, lower, hi] using hc.symm

theorem coloring_list_perm :
    ((assignments n).filter P.validB).Perm ((assignments k).map P.lift) := by
  have hleft : ((assignments n).filter P.validB).Nodup :=
    List.Pairwise.filter _ (assignments_nodup n)
  have hright : ((assignments k).map P.lift).Nodup := by
    apply List.pairwise_map.mpr
    exact (assignments_nodup k).imp (fun hne heq => hne (P.lift_injective heq))
  apply (List.perm_ext_iff_of_nodup hleft hright).mpr
  intro a
  constructor
  · intro ha
    have hv := (P.validB_iff a).mp (List.mem_filter.mp ha).2
    exact List.mem_map.mpr ⟨P.lower a, assignments_complete _, P.lift_lower a hv⟩
  · intro ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact List.mem_filter.mpr ⟨assignments_complete _,
      (P.validB_iff _).mpr (P.lift_valid b)⟩


theorem rooted_color_count : (assignments n).countP P.validB = 2 ^ k := by
  rw [List.countP_eq_length_filter, P.coloring_list_perm.length_eq,
    List.length_map, assignments_length]

theorem rooted_color_count_components_minus_one :
    (assignments n).countP P.validB = 2 ^ ((k+1)-1) := by
  simpa using P.rooted_color_count

end RootedPartition

end HamParity
