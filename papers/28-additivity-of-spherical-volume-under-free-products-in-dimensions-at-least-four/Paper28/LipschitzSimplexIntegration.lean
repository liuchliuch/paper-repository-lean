import Paper28.RealSingularChains
import Paper28.CurrentChainComplex
import Paper28.StrongContractions

/-! Canonical integration objects for actual Lipschitz singular simplices
and the standard Stokes law. The native integration chain map is derived.
The published RS comparison is an explicit parameter for this exact map,
with completeness and local strong contractions as its hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory Set
open scoped Simplicial

def lipschitzSimplexFace {Y : Type} [MetricSpace Y] {k : ℕ} (i : Fin (k+2))
    (σ : LipschitzSingularSimplex Y (k+1)) : LipschitzSingularSimplex Y k :=
  lipschitzSingularRestrict i.succAbove σ

structure LipschitzSimplexIntegrationInput {Y : Type} (metricY : MetricSpace Y)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY) where
  integration : ∀ k, @LipschitzSingularSimplex Y metricY k → J.Current k
  support_subset : ∀ k σ, J.support (integration k σ) ⊆ Set.range σ.val
  stokes : ∀ k (σ : @LipschitzSingularSimplex Y metricY (k+1)),
    J.boundary k (integration (k+1) σ) =
      ∑ i : Fin (k+2), ((-1 : ℤ)^(i : ℕ)) • integration k (lipschitzSimplexFace i σ)

theorem freeSSetBoundary_of (X : SSet) (k : ℕ) (σ : X.obj (Opposite.op ⦋k+1⦌)) :
    (freeSSetChainComplex X).d (k+1) k (FreeAbelianGroup.of σ) =
      ∑ i : Fin (k+2), ((-1 : ℤ)^(i : ℕ)) • FreeAbelianGroup.of (SimplicialObject.δ X i σ) := by
  change (AlgebraicTopology.AlternatingFaceMapComplex.obj (X ⋙ AddCommGrpCat.free)).d
    (k+1) k (FreeAbelianGroup.of σ) = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  change (AddCommGrpCat.homAddEquiv (∑ i : Fin (k+2), ((-1 : ℤ)^(i : ℕ)) •
    SimplicialObject.δ (X ⋙ AddCommGrpCat.free) i)) (FreeAbelianGroup.of σ) = _
  rw [map_sum,AddMonoidHom.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  change ((-1 : ℤ)^(i : ℕ)) • FreeAbelianGroup.map (SimplicialObject.δ X i) (FreeAbelianGroup.of σ) = _
  rw [FreeAbelianGroup.map_of_apply]

def lipschitzCurrentIntegration {Y : Type} {metricY : MetricSpace Y}
    {J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY}
    (A : LipschitzSimplexIntegrationInput metricY J) (k : ℕ) :
    FreeAbelianGroup (@LipschitzSingularSimplex Y metricY k) →+ J.Current k :=
  FreeAbelianGroup.lift (A.integration k)

theorem lipschitzCurrentIntegration_boundary {Y : Type} [metricY : MetricSpace Y]
    {J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY}
    (A : LipschitzSimplexIntegrationInput metricY J) (k : ℕ)
    (z : FreeAbelianGroup (LipschitzSingularSimplex Y (k+1))) :
    J.boundary k (lipschitzCurrentIntegration A (k+1) z) =
      lipschitzCurrentIntegration A k ((lipschitzSingularChainComplex Y).d (k+1) k z) := by
  refine FreeAbelianGroup.induction_on z ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · intro σ
    rw [freeSSetBoundary_of,lipschitzCurrentIntegration,FreeAbelianGroup.lift_apply_of,A.stokes,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul,lipschitzCurrentIntegration,FreeAbelianGroup.lift_apply_of]
    rfl
  · intro σ ih
    simpa only [map_neg] using congrArg Neg.neg ih
  · intro a b ha hb
    simpa only [map_add] using congrArg₂ (fun x y => x+y) ha hb

def lipschitzCurrentIntegrationChainMap {Y : Type} [metricY : MetricSpace Y]
    {J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY}
    (A : LipschitzSimplexIntegrationInput metricY J) :
    lipschitzSingularChainComplex Y ⟶ compactCurrentChainComplex J :=
  ChainComplex.ofHom _ _
    (AlgebraicTopology.AlternatingFaceMapComplex.d_squared (lipschitzSingularSSet Y ⋙ AddCommGrpCat.free))
    _ _ (by intro k; apply AddCommGrpCat.ext; intro z; exact J.boundary_squared_zero k z)
    (fun k => AddCommGrpCat.ofHom (lipschitzCurrentIntegration A k)) (by
      intro k
      apply AddCommGrpCat.ext
      intro z
      exact (lipschitzCurrentIntegration_boundary A k z).trans
        (congrArg (fun q => lipschitzCurrentIntegration A k (q z))
          (AlgebraicTopology.alternatingFaceMapComplex_obj_d (lipschitzSingularSSet Y ⋙ AddCommGrpCat.free) k)))

structure LipschitzCurrentHomologyComparisonInput {Y : Type} [metricY : MetricSpace Y]
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
    (A : LipschitzSimplexIntegrationInput metricY J) : Prop where
  comparison : CompleteSpace Y → AdmitsLocallyStrongLipschitzContractions Y →
    ∀ k, IsIso (HomologicalComplex.homologyMap (lipschitzCurrentIntegrationChainMap A) k)

end Paper28
