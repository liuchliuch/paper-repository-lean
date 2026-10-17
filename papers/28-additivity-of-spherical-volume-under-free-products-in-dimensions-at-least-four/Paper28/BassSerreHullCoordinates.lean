import Paper28.BassSerreFiniteTree
import Paper28.TreeBranchEmbedding

/-! Exact edge and branch coordinates of the actual finite hull tree.
These identify the maps in the area estimate with the finite-tree shadows
of Lemma 2.3, rather than assuming that geometric identification. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph Set
open scoped Classical
variable {G : Type} [Group G] [DecidableEq G] {A B : Subgroup G}
  (T : BassSerreObject A B) (F : Finset G)

def bassSerreHullEmbedding : bassSerreFiniteTree T F ↪g bassSerreGraph A B :=
  SimpleGraph.Embedding.induce (bassSerreHullVertices T F : Set (BassSerreVertex A B))

def bassSerreHullEdgeCoordinates : (bassSerreFiniteTree T F).edgeSet ↪ G :=
  (bassSerreHullEmbedding T F).mapEdgeSet.trans (bassSerreEdgeEquiv T).symm.toEmbedding

theorem bassSerreHullEdgeCoordinates_edge (e : (bassSerreFiniteTree T F).edgeSet) :
    bassSerreEdge A B (bassSerreHullEdgeCoordinates T F e) = (bassSerreHullEmbedding T F).mapEdgeSet e :=
  (bassSerreEdgeEquiv T).apply_symm_apply _

theorem bassSerreHullEdgeCoordinates_cover (g : G) (hg : g ∈ F) :
    g ∈ Set.range (bassSerreHullEdgeCoordinates T F) := by
  have hl : bassSerreLeft A B g ∈ bassSerreHullVertices T F :=
    Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_union_left _
      (List.mem_toFinset.mpr (treePath (bassSerreGraph A B) T.isTree _ _).end_mem_support)⟩)
  have hr : bassSerreRight A B g ∈ bassSerreHullVertices T F :=
    Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_union_right _
      (List.mem_toFinset.mpr (treePath (bassSerreGraph A B) T.isTree _ _).end_mem_support)⟩)
  let e : (bassSerreFiniteTree T F).edgeSet :=
    ⟨s((⟨bassSerreLeft A B g,hl⟩ : BassSerreHullVertex T F),⟨bassSerreRight A B g,hr⟩),⟨g,rfl,rfl⟩⟩
  refine ⟨e,?_⟩
  apply T.edge_bijective.injective
  exact (bassSerreHullEdgeCoordinates_edge T F e).trans rfl

def bassSerreHullNeighborCoordinatesA (v : G ⧸ A) (hv : Sum.inl v ∈ bassSerreHullVertices T F) :
    (bassSerreFiniteTree T F).neighborSet ⟨.inl v,hv⟩ ↪ A :=
  ((bassSerreHullEmbedding T F).mapNeighborSet ⟨.inl v,hv⟩).trans (T.leftLabel v).symm.toEmbedding

def bassSerreHullNeighborCoordinatesB (v : G ⧸ B) (hv : Sum.inr v ∈ bassSerreHullVertices T F) :
    (bassSerreFiniteTree T F).neighborSet ⟨.inr v,hv⟩ ↪ B :=
  ((bassSerreHullEmbedding T F).mapNeighborSet ⟨.inr v,hv⟩).trans (T.rightLabel v).symm.toEmbedding

theorem bassSerreHullBranchA (v : G ⧸ A) (hv : Sum.inl v ∈ bassSerreHullVertices T F)
    (e : (bassSerreFiniteTree T F).edgeSet) :
    bassSerreBranchA T v (bassSerreHullEdgeCoordinates T F e) =
      bassSerreHullNeighborCoordinatesA T F v hv
        (treeBranch (bassSerreFiniteTree T F) (bassSerreFiniteTree_isTree T F) ⟨.inl v,hv⟩ e) := by
  unfold bassSerreBranchA
  rw [bassSerreHullEdgeCoordinates_edge]
  exact congrArg (T.leftLabel v).symm
    (treeBranch_embedding _ _ (bassSerreFiniteTree_isTree T F) T.isTree (bassSerreHullEmbedding T F) ⟨.inl v,hv⟩ e)

theorem bassSerreHullBranchB (v : G ⧸ B) (hv : Sum.inr v ∈ bassSerreHullVertices T F)
    (e : (bassSerreFiniteTree T F).edgeSet) :
    bassSerreBranchB T v (bassSerreHullEdgeCoordinates T F e) =
      bassSerreHullNeighborCoordinatesB T F v hv
        (treeBranch (bassSerreFiniteTree T F) (bassSerreFiniteTree_isTree T F) ⟨.inr v,hv⟩ e) := by
  unfold bassSerreBranchB
  rw [bassSerreHullEdgeCoordinates_edge]
  exact congrArg (T.rightLabel v).symm
    (treeBranch_embedding _ _ (bassSerreFiniteTree_isTree T F) T.isTree (bassSerreHullEmbedding T F) ⟨.inr v,hv⟩ e)

def bassSerreHullIncidentCoordinatesA (v : G ⧸ A) (hv : Sum.inl v ∈ bassSerreHullVertices T F) :
    (bassSerreFiniteTree T F).incidenceSet ⟨.inl v,hv⟩ ↪ A :=
  ((bassSerreFiniteTree T F).incidenceSetEquivNeighborSet ⟨.inl v,hv⟩).toEmbedding.trans
    (bassSerreHullNeighborCoordinatesA T F v hv)

def bassSerreHullIncidentCoordinatesB (v : G ⧸ B) (hv : Sum.inr v ∈ bassSerreHullVertices T F) :
    (bassSerreFiniteTree T F).incidenceSet ⟨.inr v,hv⟩ ↪ B :=
  ((bassSerreFiniteTree T F).incidenceSetEquivNeighborSet ⟨.inr v,hv⟩).toEmbedding.trans
    (bassSerreHullNeighborCoordinatesB T F v hv)

theorem bassSerreHullBranchEdgeA (v : G ⧸ A) (hv : Sum.inl v ∈ bassSerreHullVertices T F)
    (e : (bassSerreFiniteTree T F).edgeSet) :
    bassSerreBranchA T v (bassSerreHullEdgeCoordinates T F e) =
      bassSerreHullIncidentCoordinatesA T F v hv
        (treeBranchEdge (bassSerreFiniteTree T F) (bassSerreFiniteTree_isTree T F) ⟨.inl v,hv⟩ e) := by
  simpa only [bassSerreHullIncidentCoordinatesA,treeBranchEdge,Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply,Equiv.apply_symm_apply] using bassSerreHullBranchA T F v hv e

theorem bassSerreHullBranchEdgeB (v : G ⧸ B) (hv : Sum.inr v ∈ bassSerreHullVertices T F)
    (e : (bassSerreFiniteTree T F).edgeSet) :
    bassSerreBranchB T v (bassSerreHullEdgeCoordinates T F e) =
      bassSerreHullIncidentCoordinatesB T F v hv
        (treeBranchEdge (bassSerreFiniteTree T F) (bassSerreFiniteTree_isTree T F) ⟨.inr v,hv⟩ e) := by
  simpa only [bassSerreHullIncidentCoordinatesB,treeBranchEdge,Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply,Equiv.apply_symm_apply] using bassSerreHullBranchB T F v hv e

end Paper28
