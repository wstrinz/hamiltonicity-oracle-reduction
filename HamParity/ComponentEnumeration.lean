module

public import HamParity.GraphColorCNF

/-! Classical finite enumeration of actual reachability classes. This derives a
component-index certificate for every finite rooted graph; it is not an efficient
component-finding algorithm. Draft until checked. -/

@[expose] public section

namespace HamParity

namespace FiniteEnumeration

noncomputable def distinct {α : Type} : List α → List α
  | [] => []
  | x :: xs => by
      classical
      exact if x ∈ distinct xs then distinct xs else x :: distinct xs

@[simp] theorem mem_distinct {α : Type} (a : α) (xs : List α) :
    a ∈ distinct xs ↔ a ∈ xs := by
  classical
  induction xs generalizing a with
  | nil => simp [distinct]
  | cons b xs ih =>
      by_cases hb : b ∈ distinct xs
      · have hbx : b ∈ xs := (ih b).mp hb
        rw [distinct, if_pos hb, ih]
        constructor
        · exact List.mem_cons_of_mem b
        · intro ha
          rcases List.mem_cons.mp ha with hab | ha
          · simpa only [hab] using hbx
          · exact ha
      · simp [distinct, hb, ih]

theorem distinct_nodup {α : Type} (xs : List α) : (distinct xs).Nodup := by
  classical
  induction xs with
  | nil => simp [distinct]
  | cons x xs ih =>
      by_cases hx : x ∈ distinct xs <;> simp [distinct, hx, ih]

end FiniteEnumeration

namespace EdgeGraph

variable {n : Nat}

def reachSetoid (G : EdgeGraph n) : Setoid (Fin n) where
  r := G.Reach
  iseqv := ⟨Reach.refl, fun h => Reach.symm h,
    fun h₁ h₂ => Reach.trans h₁ h₂⟩

abbrev ComponentClass (G : EdgeGraph n) := Quotient G.reachSetoid

def classOf (G : EdgeGraph n) (v : Fin n) : G.ComponentClass :=
  Quotient.mk G.reachSetoid v

theorem classOf_eq_iff (G : EdgeGraph n) (u v : Fin n) :
    G.classOf u = G.classOf v ↔ G.Reach u v := by
  constructor
  · intro h
    exact Quotient.exact (s := G.reachSetoid) h
  · intro h
    exact Quotient.sound (s := G.reachSetoid) h

theorem exists_class_representative (G : EdgeGraph n) (q : G.ComponentClass) :
    ∃ v : Fin n, G.classOf v = q := by
  exact Quotient.inductionOn q (fun v => ⟨v, rfl⟩)

noncomputable def classRepresentative (G : EdgeGraph n) (q : G.ComponentClass) : Fin n :=
  Classical.choose (G.exists_class_representative q)

theorem classOf_representative (G : EdgeGraph n) (q : G.ComponentClass) :
    G.classOf (G.classRepresentative q) = q :=
  Classical.choose_spec (G.exists_class_representative q)

noncomputable def allClasses (G : EdgeGraph n) : List G.ComponentClass :=
  FiniteEnumeration.distinct ((List.finRange n).map G.classOf)

theorem allClasses_nodup (G : EdgeGraph n) : G.allClasses.Nodup :=
  FiniteEnumeration.distinct_nodup _

theorem mem_allClasses (G : EdgeGraph n) (q : G.ComponentClass) : q ∈ G.allClasses := by
  obtain ⟨v, rfl⟩ := G.exists_class_representative q
  apply (FiniteEnumeration.mem_distinct _ _).mpr
  exact List.mem_map.mpr ⟨v, List.mem_finRange v, rfl⟩

noncomputable def otherClasses (G : EdgeGraph n) (root : Fin n) : List G.ComponentClass := by
  classical
  exact G.allClasses.filter (fun q => decide (q ≠ G.classOf root))

theorem mem_otherClasses (G : EdgeGraph n) (root : Fin n) (q : G.ComponentClass) :
    q ∈ G.otherClasses root ↔ q ≠ G.classOf root := by
  classical
  simp [otherClasses, List.mem_filter, G.mem_allClasses]

theorem otherClasses_nodup (G : EdgeGraph n) (root : Fin n) :
    (G.otherClasses root).Nodup := by
  classical
  exact List.Pairwise.filter _ G.allClasses_nodup

noncomputable def rootClasses (G : EdgeGraph n) (root : Fin n) : List G.ComponentClass :=
  G.classOf root :: G.otherClasses root

theorem rootClasses_nodup (G : EdgeGraph n) (root : Fin n) :
    (G.rootClasses root).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro h
    exact ((G.mem_otherClasses root _).mp h) rfl
  · exact G.otherClasses_nodup root

theorem mem_rootClasses (G : EdgeGraph n) (root : Fin n) (q : G.ComponentClass) :
    q ∈ G.rootClasses root := by
  classical
  by_cases hq : q = G.classOf root
  · exact List.mem_cons.mpr (Or.inl hq)
  · exact List.mem_cons.mpr (Or.inr ((G.mem_otherClasses root q).mpr hq))

noncomputable def componentCount (G : EdgeGraph n) : Nat := G.allClasses.length

theorem rootClasses_length (G : EdgeGraph n) (root : Fin n) :
    (G.otherClasses root).length + 1 = G.componentCount := by
  have hp : (G.rootClasses root).Perm G.allClasses := by
    apply (List.perm_ext_iff_of_nodup (G.rootClasses_nodup root) G.allClasses_nodup).mpr
    intro q
    exact ⟨fun _ => G.mem_allClasses q, fun _ => G.mem_rootClasses root q⟩
  exact hp.length_eq

noncomputable def canonicalLabel (G : EdgeGraph n) (root v : Fin n) :
    Fin ((G.otherClasses root).length + 1) := by
  classical
  exact ⟨(G.rootClasses root).idxOf (G.classOf v),
    List.idxOf_lt_length_of_mem (G.mem_rootClasses root (G.classOf v))⟩

noncomputable def canonicalRepresentative (G : EdgeGraph n) (root : Fin n)
    (i : Fin ((G.otherClasses root).length + 1)) : Fin n :=
  G.classRepresentative ((G.rootClasses root)[i.val]'i.isLt)

theorem class_at_label (G : EdgeGraph n) (root v : Fin n) :
    (G.rootClasses root)[(G.canonicalLabel root v).val]'(G.canonicalLabel root v).isLt =
      G.classOf v := by
  classical
  exact List.getElem_idxOf (G.canonicalLabel root v).isLt

theorem canonical_label_representative (G : EdgeGraph n) (root : Fin n)
    (i : Fin ((G.otherClasses root).length + 1)) :
    G.canonicalLabel root (G.canonicalRepresentative root i) = i := by
  classical
  apply Fin.ext
  change (G.rootClasses root).idxOf
    (G.classOf (G.classRepresentative ((G.rootClasses root)[i.val]'i.isLt))) = i.val
  rw [G.classOf_representative]
  exact (G.rootClasses_nodup root).idxOf_getElem i.val i.isLt

theorem canonical_label_root (G : EdgeGraph n) (root : Fin n) :
    G.canonicalLabel root root = 0 := by
  classical
  apply Fin.ext
  simp [canonicalLabel, rootClasses]

theorem canonical_label_iff (G : EdgeGraph n) (root u v : Fin n) :
    G.canonicalLabel root u = G.canonicalLabel root v ↔ G.Reach u v := by
  classical
  constructor
  · intro h
    apply (G.classOf_eq_iff u v).mp
    rw [← G.class_at_label root u, ← G.class_at_label root v, h]
  · intro h
    have hc := (G.classOf_eq_iff u v).mpr h
    apply Fin.ext
    change (G.rootClasses root).idxOf (G.classOf u) =
      (G.rootClasses root).idxOf (G.classOf v)
    rw [hc]

noncomputable def canonicalComponentIndex (G : EdgeGraph n) (root : Fin n) :
    G.ComponentIndex root (G.otherClasses root).length where
  label := G.canonicalLabel root
  representative := G.canonicalRepresentative root
  label_representative := G.canonical_label_representative root
  label_root := G.canonical_label_root root
  fiber_iff_reach := G.canonical_label_iff root

theorem rooted_color_count_all_graphs (G : EdgeGraph n) (root : Fin n) :
    (assignments n).countP (G.rootedValidB root) = 2 ^ (G.componentCount - 1) := by
  have hc := (G.canonicalComponentIndex root).rooted_color_count
  rw [← G.rootClasses_length root]
  simpa using hc

theorem colorCNF_count_all_graphs (G : EdgeGraph n) (root : Fin n) :
    modelCount (G.colorCNF root) = 2 ^ (G.componentCount - 1) := by
  rw [G.colorCNF_count, G.rooted_color_count_all_graphs root]

theorem colorCNF_disconnected_even_all_graphs (G : EdgeGraph n) (root : Fin n)
    (h : G.Disconnected) : modelCount (G.colorCNF root) % 2 = 0 :=
  (G.canonicalComponentIndex root).colorCNF_disconnected_even h

theorem colorCNF_odd_connected_all_graphs (G : EdgeGraph n) (root : Fin n)
    (h : modelCount (G.colorCNF root) % 2 = 1) : ∀ u v, G.Reach u v :=
  (G.canonicalComponentIndex root).colorCNF_odd_connected h

end EdgeGraph

end HamParity
