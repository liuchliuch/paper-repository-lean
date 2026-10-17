import Paper28.BassSerreFiniteHull

/-! The explicit finite path hull induces an actual finite tree. This
is the tree on which the already proved Jacobian theorem is applied. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph Set
open scoped Classical
variable {G : Type} [Group G] [DecidableEq G] {A B : Subgroup G}
  (T : BassSerreObject A B) (F : Finset G)

abbrev BassSerreHullVertex := {v : BassSerreVertex A B // v ∈ bassSerreHullVertices T F}

def bassSerreFiniteTree : SimpleGraph (BassSerreHullVertex T F) :=
  (bassSerreGraph A B).induce (bassSerreHullVertices T F : Set (BassSerreVertex A B))

theorem bassSerreFiniteTree_isTree : (bassSerreFiniteTree T F).IsTree := by
  constructor
  · apply (connected_iff_exists_forall_reachable _).mpr
    refine ⟨⟨bassSerreLeft A B 1,Finset.mem_insert_self _ _⟩,?_⟩
    intro z
    by_cases hz : z.val = bassSerreLeft A B 1
    · have he : z = ⟨bassSerreLeft A B 1,Finset.mem_insert_self _ _⟩ := Subtype.ext hz
      rw [he]
    · have hm := Finset.mem_of_mem_insert_of_ne z.property hz
      obtain ⟨g,hg,hzPath⟩ := Finset.mem_biUnion.mp hm
      rcases Finset.mem_union.mp hzPath with hl | hr
      · let p := treePath (bassSerreGraph A B) T.isTree (bassSerreLeft A B 1) (bassSerreLeft A B g)
        have hs : {x | x ∈ p.support} ⊆ (bassSerreHullVertices T F : Set (BassSerreVertex A B)) := by
          intro x hx
          exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_union_left _ (List.mem_toFinset.mpr hx)⟩)
        exact (p.connected_induce_support ⟨_,p.start_mem_support⟩ ⟨z.val,List.mem_toFinset.mp hl⟩).map
          ((bassSerreGraph A B).induceHomOfLE hs).toHom
      · let p := treePath (bassSerreGraph A B) T.isTree (bassSerreLeft A B 1) (bassSerreRight A B g)
        have hs : {x | x ∈ p.support} ⊆ (bassSerreHullVertices T F : Set (BassSerreVertex A B)) := by
          intro x hx
          exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_union_right _ (List.mem_toFinset.mpr hx)⟩)
        exact (p.connected_induce_support ⟨_,p.start_mem_support⟩ ⟨z.val,List.mem_toFinset.mp hr⟩).map
          ((bassSerreGraph A B).induceHomOfLE hs).toHom
  · exact T.isTree.IsAcyclic.induce _

end Paper28
