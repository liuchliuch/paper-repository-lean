import Paper28.TreeBranches

/-! Native unique-path routing is natural under every tree automorphism.
This supplies the combinatorial part of the shadow equivariance (8). -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
variable {V : Type*} (Q : SimpleGraph V) (hQ : Q.IsTree) (e : Q ≃g Q)

theorem firstNeighbor_automorphism (v a : V) (ha : a ≠ v) :
    firstNeighbor Q hQ (e v) (e a) (fun h => ha (e.injective h)) =
      e.mapNeighborSet v (firstNeighbor Q hQ v a ha) := by
  apply (firstNeighbor_eq_iff_avoiding Q hQ (e v) (e a) _ _).mpr
  obtain ⟨p,hp⟩ := (firstNeighbor_eq_iff_avoiding Q hQ v a ha (firstNeighbor Q hQ v a ha)).mp rfl
  refine ⟨p.map e.toHom,?_⟩
  rw [Walk.support_map]
  rintro h
  obtain ⟨x,hx,he⟩ := List.mem_map.mp h
  exact hp ((e.injective he) ▸ hx)

theorem treeBranch_automorphism (v : V) (a : Q.edgeSet) :
    treeBranch Q hQ (e v) (e.mapEdgeSet a) = e.mapNeighborSet v (treeBranch Q hQ v a) := by
  let x := edgeTarget Q v a
  have hx : e x.val ∈ (e.mapEdgeSet a).val := by
    exact Sym2.mem_map.mpr ⟨x.val,x.property.1,rfl⟩
  rw [treeBranch_eq_firstNeighbor_endpoint Q hQ (e v) (e.mapEdgeSet a) (e x.val) hx
    (fun h => x.property.2 (e.injective h)),
    treeBranch_eq_firstNeighbor_endpoint Q hQ v a x.val x.property.1 x.property.2]
  exact firstNeighbor_automorphism Q hQ e v x.val x.property.2

end Paper28
