import Paper28.TreeCuts

/-! Exhaustive native graph split for the Jacobian induction: either the
connected graph is a star, or an edge has a further edge on both sides. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
variable {V : Type*} (T : SimpleGraph V)

/-- Every vertex other than the center has no neighbor other than it. -/
def StarCenter (c : V) : Prop := ∀ x, x ≠ c → ∀ y, T.Adj x y → y = c

def HasTwoNeighbors (c : V) : Prop := ∃ a b, T.Adj c a ∧ T.Adj c b ∧ a ≠ b

def InternalEdge (v w : V) : Prop :=
  T.Adj v w ∧ (∃ a, T.Adj v a ∧ a ≠ w) ∧ (∃ b, T.Adj w b ∧ b ≠ v)

theorem two_neighbors_other (c : V) (hc : HasTwoNeighbors T c) (w : V) :
    ∃ a, T.Adj c a ∧ a ≠ w := by
  classical
  obtain ⟨a, b, ha, hb, hab⟩ := hc
  by_cases h : a = w
  · exact ⟨b, hb, fun hbw => hab (h.trans hbw.symm)⟩
  · exact ⟨a, ha, h⟩

/-- Connectedness propagates the leaf condition from the center's neighbors
through the whole graph. -/
theorem starCenter_of_neighbors_leaves (hT : T.Connected) (c : V)
    (hleaf : ∀ x, T.Adj c x → ∀ y, T.Adj x y → y = c) : StarCenter T c := by
  have hp (x : V) : x = c ∨ (T.Adj c x ∧ ∀ y, T.Adj x y → y = c) := by
    have hr := (reachable_iff_reflTransGen c x).mp (hT c x)
    induction hr with
    | refl => exact Or.inl rfl
    | @tail a b _ hab ih =>
      rcases ih with hac | ⟨hca, hla⟩
      · subst a
        exact Or.inr ⟨hab, hleaf b hab⟩
      · exact Or.inl (hla b hab)
  intro x hxc y hxy
  exact ((hp x).resolve_left hxc).2 y hxy

/-- A connected graph without an internal edge is a star, including the
single-vertex and single-edge cases. -/
theorem star_or_internal_edge (hT : T.Connected) :
    (∃ c, StarCenter T c) ∨ ∃ v w, InternalEdge T v w := by
  classical
  by_cases hi : ∃ v w, InternalEdge T v w
  · exact Or.inr hi
  · left
    by_cases hb : ∃ c, HasTwoNeighbors T c
    · obtain ⟨c, hc⟩ := hb
      refine ⟨c, starCenter_of_neighbors_leaves T hT c ?_⟩
      intro x hcx y hxy
      by_contra hyc
      exact hi ⟨c, x, hcx, two_neighbors_other T c hc x, y, hxy, hyc⟩
    · let c := Classical.choice hT.nonempty
      refine ⟨c, starCenter_of_neighbors_leaves T hT c ?_⟩
      intro x hcx y hxy
      by_contra hyc
      exact hb ⟨x, c, y, hcx.symm, hxy, Ne.symm hyc⟩

/-- Both recursive trees strictly decrease in size at an internal edge. -/
theorem internal_edge_card_decreases [Finite V] (hT : T.IsTree) (v w : V)
    (h : InternalEdge T v w) :
    Nat.card (retainedSide T v w) < Nat.card V ∧
      Nat.card (retainedSide T w v) < Nat.card V := by
  obtain ⟨hvw, ⟨a, hva, haw⟩, ⟨b, hwb, hbv⟩⟩ := h
  exact ⟨retainedTree_card_lt T hT v w b hvw hwb hbv,
    retainedTree_card_lt T hT w v a hvw.symm hva haw⟩

/-- In a star every noncentral neighbor set is a subsingleton; its shadow
therefore has the single constant spherical coordinate. -/
theorem StarCenter.neighbors_subsingleton {c : V} (hc : StarCenter T c)
    (x : V) (hxc : x ≠ c) : Subsingleton (T.neighborSet x) := by
  constructor
  intro a b
  apply Subtype.ext
  exact (hc x hxc a.val a.property).trans (hc x hxc b.val b.property).symm

end Paper28
