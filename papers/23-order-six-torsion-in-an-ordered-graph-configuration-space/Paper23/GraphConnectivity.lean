import Paper23.GraphStructure

/-! Explicit paths and the short-path subdivision condition. -/
namespace Paper23.GraphConnectivity
open Cubical GraphStructure

/-- Incidence adjacency, with edge orientation forgotten. -/
def Adjacent (u v : Vertex) : Prop := ∃ e : Edge,
  endpoints e = (u,v) ∨ endpoints e = (v,u)

instance (u v : Vertex) : Decidable (Adjacent u v) :=
  inferInstanceAs (Decidable (∃ e : Edge, endpoints e = (u,v) ∨ endpoints e = (v,u)))

theorem adjacent_symmetric : Symmetric Adjacent := by
  rintro u v ⟨e,h | h⟩
  · exact ⟨e, Or.inr h⟩
  · exact ⟨e, Or.inl h⟩

/-- A finite edge path starting at s and ending at t. -/
def Follows (s t : Vertex) (xs : List Vertex) : Prop :=
  List.rec (motive := fun _ => Vertex → Prop) (fun s => s = t)
    (fun u _ rec s => Adjacent s u ∧ rec u) xs s

instance (s t : Vertex) (xs : List Vertex) : Decidable (Follows s t xs) := by
  induction xs generalizing s with
  | nil => exact inferInstanceAs (Decidable (s = t))
  | cons u xs ih => exact @instDecidableAnd (Adjacent s u) (Follows u t xs) _ (ih u)

/-- Checked spanning paths, excluding the initial vertex zero. -/
def zeroPath : Vertex → List Vertex := ![
  [],
  [6,7,1],
  [12,13,2],
  [14,15,3],
  [6,7,1,16,17,4],
  [6,7,1,18,19,5],
  [6],
  [6,7],
  [8],
  [8,9],
  [10],
  [10,11],
  [12],
  [12,13],
  [14],
  [14,15],
  [6,7,1,16],
  [6,7,1,16,17],
  [6,7,1,18],
  [6,7,1,18,19],
  [12,13,2,20],
  [14,15,3,21],
  [12,13,2,22],
  [12,13,2,22,23],
  [12,13,2,24],
  [12,13,2,24,25],
  [14,15,3,26],
  [14,15,3,26,27],
  [14,15,3,28],
  [14,15,3,28,29],
  [6,7,1,16,17,4,30],
  [6,7,1,18,19,5,31]]

theorem zeroPath_follows : ∀ v : Vertex, Follows 0 v (zeroPath v) := by decide

theorem follows_reachable (s t : Vertex) (xs : List Vertex) (h : Follows s t xs) :
    Relation.ReflTransGen Adjacent s t := by
  induction xs generalizing s with
  | nil => exact h ▸ Relation.ReflTransGen.refl
  | cons u xs ih => exact Relation.ReflTransGen.head h.1 (ih u h.2)

/-- Connectivity of the actual thirty-two-vertex graph. -/
theorem connected (u v : Vertex) : Relation.ReflTransGen Adjacent u v := by
  have hu := follows_reachable 0 u (zeroPath u) (zeroPath_follows u)
  have hv := follows_reachable 0 v (zeroPath v) (zeroPath_follows v)
  exact (Relation.ReflTransGen.symmetric adjacent_symmetric hu).trans hv

/-- No single edge joins two distinct original (degree not two) vertices. -/
theorem no_short_special_edge : ∀ u v : CoreVertex,
    ¬ Adjacent ⟨u.val, by omega⟩ ⟨v.val, by omega⟩ := by decide

/-- No two-edge path joins distinct original (degree not two) vertices. -/
theorem no_short_special_two_edges : ∀ u v : CoreVertex, u ≠ v →
    ∀ w : Vertex, ¬ (Adjacent ⟨u.val, by omega⟩ w ∧
      Adjacent w ⟨v.val, by omega⟩) := by decide

/-- A three-edge path between a and b supplies the sharpness witness. -/
theorem special_three_edge_path : Follows 0 1 [6,7,1] := by decide

end Paper23.GraphConnectivity
