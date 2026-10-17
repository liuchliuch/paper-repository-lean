import Paper28.OrderedSimplicialChains
import Paper28.EuclideanPolyhedralCurrents
import Paper28.CurrentChainComplex

/-! The actual integration of finite integer simplicial chains into the
standard Euclidean current objects. Its chain-map property follows from
the generic simplex Stokes law and the native alternating face boundary. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory Set
open scoped Simplicial
variable {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}

def orderedSimplexVertices {k : ℕ} (σ : OrderedComplexSimplex K k) : AffineSimplexVertices d k :=
  fun i => K.enumeratedVertex (σ.indices i)

def orderedSimplexFace {k : ℕ} (i : Fin (k+2)) (σ : OrderedComplexSimplex K (k+1)) :
    OrderedComplexSimplex K k := orderedSimplexRestrict (SimplexCategory.δ i).toOrderHom σ

theorem orderedSimplexFace_vertices {k : ℕ} (i : Fin (k+2)) (σ : OrderedComplexSimplex K (k+1)) :
    orderedSimplexVertices (orderedSimplexFace i σ) = fun j => orderedSimplexVertices σ (i.succAbove j) := rfl

def orderedIntegration
    {I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance}
    (S : EuclideanSimplexIntegrationInput d I) (k : ℕ) : orderedSimplicialChains K k →+ I.Current k :=
  FreeAbelianGroup.lift (fun σ => S.integration k (orderedSimplexVertices σ))

theorem orderedIntegration_mem_polyhedral
    {I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance}
    (S : EuclideanSimplexIntegrationInput d I) (k : ℕ) (z : orderedSimplicialChains K k) :
    orderedIntegration S k z ∈ euclideanPolyhedralCurrents S k := by
  refine FreeAbelianGroup.induction_on z ?_ ?_ ?_ ?_
  · rw [map_zero]
    exact AddSubgroup.zero_mem _
  · intro σ
    rw [orderedIntegration,FreeAbelianGroup.lift_apply_of]
    exact AddSubgroup.subset_closure (Set.mem_range_self _)
  · intro σ hσ
    rw [map_neg]
    exact AddSubgroup.neg_mem _ hσ
  · intro a b ha hb
    rw [map_add]
    exact AddSubgroup.add_mem _ ha hb

theorem orderedBoundary_of (k : ℕ) (σ : OrderedComplexSimplex K (k+1)) :
    (orderedSimplicialChainComplex K).d (k+1) k (FreeAbelianGroup.of σ) =
      ∑ i : Fin (k+2), ((-1 : ℤ)^(i : ℕ)) • FreeAbelianGroup.of (orderedSimplexFace i σ) := by
  change (AlgebraicTopology.AlternatingFaceMapComplex.obj
    (orderedComplexSSet K ⋙ AddCommGrpCat.free)).d (k+1) k (FreeAbelianGroup.of σ) = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  change (AddCommGrpCat.homAddEquiv (∑ i : Fin (k+2), ((-1 : ℤ)^(i : ℕ)) •
    SimplicialObject.δ (orderedComplexSSet K ⋙ AddCommGrpCat.free) i)) (FreeAbelianGroup.of σ) = _
  rw [map_sum]
  rw [AddMonoidHom.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  change ((-1 : ℤ)^(i : ℕ)) • FreeAbelianGroup.map (orderedSimplexFace i) (FreeAbelianGroup.of σ) = _
  rw [FreeAbelianGroup.map_of_apply]

theorem orderedIntegration_boundary
    {I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance}
    (S : EuclideanSimplexIntegrationInput d I) (k : ℕ) (z : orderedSimplicialChains K (k+1)) :
    I.boundary k (orderedIntegration S (k+1) z) =
      orderedIntegration S k ((orderedSimplicialChainComplex K).d (k+1) k z) := by
  refine FreeAbelianGroup.induction_on z ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · intro σ
    rw [orderedBoundary_of,orderedIntegration,FreeAbelianGroup.lift_apply_of,S.stokes,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul,orderedIntegration,FreeAbelianGroup.lift_apply_of,orderedSimplexFace_vertices]
  · intro σ ih
    simpa only [map_neg] using congrArg Neg.neg ih
  · intro a b ha hb
    simpa only [map_add] using congrArg₂ (fun x y => x+y) ha hb

def orderedIntegrationChainMap
    {I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance}
    (S : EuclideanSimplexIntegrationInput d I) :
    orderedSimplicialChainComplex K ⟶ compactCurrentChainComplex I :=
  ChainComplex.ofHom _ _
    (AlgebraicTopology.AlternatingFaceMapComplex.d_squared (orderedComplexSSet K ⋙ AddCommGrpCat.free))
    _ _ (by intro k; ext z; exact I.boundary_squared_zero k z)
    (fun k => AddCommGrpCat.ofHom (orderedIntegration S k)) (by
    intro k
    apply AddCommGrpCat.ext
    intro z
    change I.boundary k (orderedIntegration S (k+1) z) = orderedIntegration S k
      ((AlgebraicTopology.AlternatingFaceMapComplex.objD (orderedComplexSSet K ⋙ AddCommGrpCat.free) k) z)
    exact (orderedIntegration_boundary S k z).trans
      (congrArg (fun q => orderedIntegration S k (q z))
        (AlgebraicTopology.alternatingFaceMapComplex_obj_d (orderedComplexSSet K ⋙ AddCommGrpCat.free) k)))

end Paper28
