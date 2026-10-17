import Paper28.BassSerreObjectInput

/-! An explicit finite set of tree vertices contains every possible
nonconstant shadow of a fixed finite coordinate set. This is the native
finiteness argument for the sums in (9), before any current is pushed. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
open scoped Classical
variable {G : Type} [Group G] [DecidableEq G] {A B : Subgroup G}
  (T : BassSerreObject A B)

def bassSerreHullVertices (F : Finset G) : Finset (BassSerreVertex A B) :=
  insert (bassSerreLeft A B 1) (F.biUnion (fun g =>
    (treePath (bassSerreGraph A B) T.isTree (bassSerreLeft A B 1) (bassSerreLeft A B g)).support.toFinset ∪
    (treePath (bassSerreGraph A B) T.isTree (bassSerreLeft A B 1) (bassSerreRight A B g)).support.toFinset))

theorem firstNeighbor_eq_of_avoiding_walk {V : Type*} (Q : SimpleGraph V) (hQ : Q.IsTree)
    (v a b : V) (ha : a ≠ v) (hb : b ≠ v) (p : Q.Walk a b) (hp : v ∉ p.support) :
    firstNeighbor Q hQ v a ha = firstNeighbor Q hQ v b hb := by
  let w := firstNeighbor Q hQ v a ha
  obtain ⟨q,hq⟩ := (firstNeighbor_eq_iff_avoiding Q hQ v a ha w).mp rfl
  apply Eq.symm
  apply (firstNeighbor_eq_iff_avoiding Q hQ v b hb w).mpr
  refine ⟨q.append p,?_⟩
  intro h
  rw [Walk.support_append] at h
  rcases List.mem_append.mp h with h | h
  · exact hq h
  · exact hp (List.mem_of_mem_tail h)

theorem bassSerreBranch_outside_hull (F : Finset G) (v : BassSerreVertex A B)
    (hv : v ∉ bassSerreHullVertices T F) :
    ∃ w : (bassSerreGraph A B).neighborSet v, ∀ g ∈ F,
      treeBranch (bassSerreGraph A B) T.isTree v (bassSerreEdge A B g) = w := by
  have hroot : bassSerreLeft A B 1 ≠ v := by
    intro he
    exact hv (he ▸ Finset.mem_insert_self _ _)
  refine ⟨firstNeighbor (bassSerreGraph A B) T.isTree v _ hroot,?_⟩
  intro g hg
  let p := treePath (bassSerreGraph A B) T.isTree (bassSerreLeft A B 1) (bassSerreLeft A B g)
  have hp : v ∉ p.support := by
    intro h
    apply hv
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_union_left _ (List.mem_toFinset.mpr h)⟩)
  have hgV : bassSerreLeft A B g ≠ v := by
    intro he
    exact hp (he ▸ p.end_mem_support)
  rw [treeBranch_eq_firstNeighbor_endpoint (bassSerreGraph A B) T.isTree v (bassSerreEdge A B g)
    (bassSerreLeft A B g) (by exact Sym2.mem_mk_left _ _) hgV]
  exact (firstNeighbor_eq_of_avoiding_walk _ T.isTree v _ _ hroot hgV p hp).symm

theorem bassSerreBranchA_outside_hull (F : Finset G) (v : G ⧸ A)
    (hv : Sum.inl v ∉ bassSerreHullVertices T F) :
    ∃ a : A, ∀ g ∈ F, bassSerreBranchA T v g = a := by
  obtain ⟨w,hw⟩ := bassSerreBranch_outside_hull T F (.inl v) hv
  exact ⟨(T.leftLabel v).symm w,fun g hg => congrArg (T.leftLabel v).symm (hw g hg)⟩

theorem bassSerreBranchB_outside_hull (F : Finset G) (v : G ⧸ B)
    (hv : Sum.inr v ∉ bassSerreHullVertices T F) :
    ∃ b : B, ∀ g ∈ F, bassSerreBranchB T v g = b := by
  obtain ⟨w,hw⟩ := bassSerreBranch_outside_hull T F (.inr v) hv
  exact ⟨(T.rightLabel v).symm w,fun g hg => congrArg (T.rightLabel v).symm (hw g hg)⟩

end Paper28
