import Paper28.OrderedSimplicialIntegration

/-! Actual oriented integer simplicial chains with strictly ordered
vertices. Their inclusion into the simplicial set chains is injective;
boundary closure and d squared zero are derived through that inclusion.
Thus degeneracies are not mistaken for independent integration currents. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory
variable {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}

abbrev NondegenerateComplexSimplex (K : FiniteEuclideanComplex (EuclideanAmbient d)) (k : ℕ) :=
  {σ : OrderedComplexSimplex K k // StrictMono σ.indices}

abbrev finiteSimplicialChains (K : FiniteEuclideanComplex (EuclideanAmbient d)) (k : ℕ) :=
  FreeAbelianGroup (NondegenerateComplexSimplex K k)

def nondegenerateSimplexFace {k : ℕ} (i : Fin (k+2)) (σ : NondegenerateComplexSimplex K (k+1)) :
    NondegenerateComplexSimplex K k :=
  ⟨orderedSimplexFace i σ.val,σ.property.comp (Fin.strictMono_succAbove i)⟩

def nondegenerateChainInclusion (k : ℕ) : finiteSimplicialChains K k →+ orderedSimplicialChains K k :=
  FreeAbelianGroup.map Subtype.val

def nondegenerateChainProjection (k : ℕ) : orderedSimplicialChains K k →+ finiteSimplicialChains K k := by
  classical
  exact FreeAbelianGroup.lift (fun σ => if h : StrictMono σ.indices then FreeAbelianGroup.of ⟨σ,h⟩ else 0)

theorem nondegenerateChainProjection_inclusion (k : ℕ) (z : finiteSimplicialChains K k) :
    nondegenerateChainProjection k (nondegenerateChainInclusion k z) = z := by
  have he : (nondegenerateChainProjection (K := K) k).comp (nondegenerateChainInclusion k) = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    intro σ
    simp [nondegenerateChainInclusion,nondegenerateChainProjection,σ.property]
  exact DFunLike.congr_fun he z

theorem nondegenerateChainInclusion_injective (k : ℕ) :
    Function.Injective (nondegenerateChainInclusion (K := K) k) :=
  fun a b h => by simpa only [nondegenerateChainProjection_inclusion] using congrArg (nondegenerateChainProjection k) h

def finiteSimplicialBoundary (k : ℕ) : finiteSimplicialChains K (k+1) →+ finiteSimplicialChains K k :=
  FreeAbelianGroup.lift (fun σ => ∑ i : Fin (k+2), ((-1 : ℤ)^(i : ℕ)) •
    FreeAbelianGroup.of (nondegenerateSimplexFace i σ))

theorem nondegenerateChainInclusion_boundary (k : ℕ) (z : finiteSimplicialChains K (k+1)) :
    nondegenerateChainInclusion k (finiteSimplicialBoundary k z) =
      (orderedSimplicialChainComplex K).d (k+1) k (nondegenerateChainInclusion (k+1) z) := by
  have he : (nondegenerateChainInclusion k).comp (finiteSimplicialBoundary k) =
      ((orderedSimplicialChainComplex K).d (k+1) k).hom.comp (nondegenerateChainInclusion (k+1)) := by
    apply FreeAbelianGroup.lift_ext
    intro σ
    change nondegenerateChainInclusion k (finiteSimplicialBoundary k (FreeAbelianGroup.of σ)) =
      (orderedSimplicialChainComplex K).d (k+1) k (nondegenerateChainInclusion (k+1) (FreeAbelianGroup.of σ))
    simp only [finiteSimplicialBoundary,FreeAbelianGroup.lift_apply_of,map_sum,map_zsmul,
      nondegenerateChainInclusion,FreeAbelianGroup.map_of_apply]
    rw [orderedBoundary_of]
    rfl
  exact DFunLike.congr_fun he z

theorem finiteSimplicialBoundary_squared (k : ℕ) (z : finiteSimplicialChains K (k+2)) :
    finiteSimplicialBoundary k (finiteSimplicialBoundary (k+1) z) = 0 := by
  apply nondegenerateChainInclusion_injective k
  rw [nondegenerateChainInclusion_boundary,nondegenerateChainInclusion_boundary,map_zero]
  change ((orderedSimplicialChainComplex K).d (k+2) (k+1) ≫
    (orderedSimplicialChainComplex K).d (k+1) k) (nondegenerateChainInclusion (k+2) z) = 0
  rw [HomologicalComplex.d_comp_d]
  rfl

def finiteSimplicialChainComplex (K : FiniteEuclideanComplex (EuclideanAmbient d)) :
    ChainComplex AddCommGrpCat ℕ :=
  ChainComplex.of (fun k => AddCommGrpCat.of (finiteSimplicialChains K k))
    (fun k => AddCommGrpCat.ofHom (finiteSimplicialBoundary k)) (by
      intro k
      apply AddCommGrpCat.ext
      intro z
      exact finiteSimplicialBoundary_squared k z)

def finiteSimplicialIntegration
    {I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance}
    (S : EuclideanSimplexIntegrationInput d I) (k : ℕ) : finiteSimplicialChains K k →+ I.Current k :=
  (orderedIntegration S k).comp (nondegenerateChainInclusion k)

theorem finiteSimplicialIntegration_boundary
    {I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance}
    (S : EuclideanSimplexIntegrationInput d I) (k : ℕ) (z : finiteSimplicialChains K (k+1)) :
    I.boundary k (finiteSimplicialIntegration S (k+1) z) =
      finiteSimplicialIntegration S k (finiteSimplicialBoundary k z) := by
  change I.boundary k (orderedIntegration S (k+1) (nondegenerateChainInclusion (k+1) z)) = _
  rw [orderedIntegration_boundary]
  exact congrArg (orderedIntegration S k) (nondegenerateChainInclusion_boundary k z).symm

end Paper28
