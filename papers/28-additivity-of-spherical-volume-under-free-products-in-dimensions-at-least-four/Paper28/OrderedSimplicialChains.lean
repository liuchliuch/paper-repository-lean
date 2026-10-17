import Paper28.FiniteEuclideanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Category.Grp.Adjunctions

/-! Actual integer simplicial chains of the native finite Euclidean
complex. Vertices are enumerated once; weakly ordered vertex tuples give
its ordinary simplicial set, including degeneracies. The native alternating
face complex proves boundary squared zero. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory Set
open scoped Simplicial
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [DecidableEq H]

theorem FiniteEuclideanComplex.finite_vertices (K : FiniteEuclideanComplex H) :
    K.complex.vertices.Finite := by
  rw [Geometry.SimplicialComplex.vertices_eq]
  exact K.finite_faces.biUnion (fun s _ => s.finite_toSet)

instance FiniteEuclideanComplex.fintypeVertices (K : FiniteEuclideanComplex H) : Fintype K.complex.vertices :=
  K.finite_vertices.fintype

abbrev FiniteEuclideanComplex.VertexIndex (K : FiniteEuclideanComplex H) :=
  Fin (Fintype.card K.complex.vertices)

def FiniteEuclideanComplex.enumeratedVertex (K : FiniteEuclideanComplex H) (i : K.VertexIndex) : H :=
  ((Fintype.equivFin K.complex.vertices).symm i).val

@[ext]
structure OrderedComplexSimplex (K : FiniteEuclideanComplex H) (n : ℕ) where
  indices : Fin (n+1) →o K.VertexIndex
  face : (Finset.univ.image (fun i => K.enumeratedVertex (indices i))) ∈ K.complex.faces

def orderedSimplexRestrict {K : FiniteEuclideanComplex H} {n m : ℕ}
    (f : Fin (m+1) →o Fin (n+1)) (σ : OrderedComplexSimplex K n) : OrderedComplexSimplex K m := by
  classical
  refine ⟨σ.indices.comp f,K.complex.down_closed σ.face ?_ ?_⟩
  · intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨f i,Finset.mem_univ _,rfl⟩
  · exact (Finset.image_nonempty.mpr ⟨(0 : Fin (m+1)),Finset.mem_univ _⟩).ne_empty

def orderedComplexSSet (K : FiniteEuclideanComplex H) : SSet where
  obj n := OrderedComplexSimplex K n.unop.len
  map f := fun σ => orderedSimplexRestrict f.unop.toOrderHom σ
  map_id _ := by
    funext σ
    apply OrderedComplexSimplex.ext
    rfl
  map_comp _ _ := by
    funext σ
    apply OrderedComplexSimplex.ext
    rfl

def orderedSimplicialChainComplex (K : FiniteEuclideanComplex H) : ChainComplex AddCommGrpCat ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat).obj
    (orderedComplexSSet K ⋙ AddCommGrpCat.free)

abbrev orderedSimplicialChains (K : FiniteEuclideanComplex H) (k : ℕ) :=
  FreeAbelianGroup (OrderedComplexSimplex K k)

theorem orderedSimplicialChainComplex_X (K : FiniteEuclideanComplex H) (k : ℕ) :
    (orderedSimplicialChainComplex K).X k = AddCommGrpCat.of (orderedSimplicialChains K k) := rfl

end Paper28
