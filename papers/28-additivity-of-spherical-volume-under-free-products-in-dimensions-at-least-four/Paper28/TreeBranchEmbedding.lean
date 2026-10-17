import Paper28.TreeBranches

/-! Actual branch routing is natural for embeddings of a connected
subtree into a tree, by uniqueness of paths. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
variable {V W : Type*} (Q : SimpleGraph V) (R : SimpleGraph W)
  (hQ : Q.IsTree) (hR : R.IsTree) (e : Q ↪g R)

theorem firstNeighbor_embedding (v a : V) (ha : a ≠ v) :
    firstNeighbor R hR (e v) (e a) (fun h => ha (e.injective h)) =
      e.mapNeighborSet v (firstNeighbor Q hQ v a ha) := by
  apply (firstNeighbor_eq_iff_avoiding R hR (e v) (e a) _ _).mpr
  obtain ⟨p,hp⟩ := (firstNeighbor_eq_iff_avoiding Q hQ v a ha (firstNeighbor Q hQ v a ha)).mp rfl
  refine ⟨p.map e.toHom,?_⟩
  rw [Walk.support_map]
  intro h
  obtain ⟨x,hx,he⟩ := List.mem_map.mp h
  exact hp ((e.injective he) ▸ hx)

theorem treeBranch_embedding (v : V) (a : Q.edgeSet) :
    treeBranch R hR (e v) (e.mapEdgeSet a) = e.mapNeighborSet v (treeBranch Q hQ v a) := by
  let x := edgeTarget Q v a
  have hx : e x.val ∈ (e.mapEdgeSet a).val := Sym2.mem_map.mpr ⟨x.val,x.property.1,rfl⟩
  rw [treeBranch_eq_firstNeighbor_endpoint R hR (e v) (e.mapEdgeSet a) (e x.val) hx
    (fun h => x.property.2 (e.injective h)),
    treeBranch_eq_firstNeighbor_endpoint Q hQ v a x.val x.property.1 x.property.2]
  exact firstNeighbor_embedding Q R hQ hR e v x.val x.property.2

end Paper28
