import Paper28.RealSingularChains
import Paper28.SimplicialCarrierIntegration

/-! The actual barycentric simplicial-to-Lipschitz-singular map, with
native face/degeneracy naturality. Its ordinary singular comparison is
the composite with the actual forgetful chain map. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory Set
open scoped Simplicial
variable {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}

def simplexBarycentricLinear {k : ℕ} (v : AffineSimplexVertices d k) :
    (Fin (k+1) → ℝ) →L[ℝ] EuclideanAmbient d :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (v i)

theorem simplexBarycentricLinear_apply {k : ℕ} (v : AffineSimplexVertices d k) (t : Fin (k+1) → ℝ) :
    simplexBarycentricLinear v t = ∑ i, t i • v i := by
  simp only [simplexBarycentricLinear,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply]

def orderedSimplexParameter {k : ℕ} (σ : OrderedComplexSimplex K k)
    (t : stdSimplex ℝ (Fin (k+1))) : K.complex.space := by
  refine ⟨∑ i, t.val i • orderedSimplexVertices σ i,?_⟩
  apply K.complex.convexHull_subset_space σ.face
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => t.property.1 i) t.property.2
    (fun i _ => subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))

theorem orderedSimplexParameter_lipschitz {k : ℕ} (σ : OrderedComplexSimplex K k) :
    LipschitzWith ‖simplexBarycentricLinear (orderedSimplexVertices σ)‖₊ (orderedSimplexParameter σ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [simplexBarycentricLinear_apply] using
    (simplexBarycentricLinear (orderedSimplexVertices σ)).lipschitz.dist_le_mul x.val y.val

theorem orderedSimplexParameter_natural {n m : ℕ} (f : Fin (m+1) →o Fin (n+1))
    (σ : OrderedComplexSimplex K n) (t : stdSimplex ℝ (Fin (m+1))) :
    orderedSimplexParameter (orderedSimplexRestrict f σ) t =
      orderedSimplexParameter σ (stdSimplex.map f t) := by
  classical
  apply Subtype.ext
  change (∑ i, t.val i • orderedSimplexVertices σ (f i)) =
    ∑ j, (FunOnFinite.linearMap ℝ ℝ (fun i => f i) t.val) j • orderedSimplexVertices σ j
  simp only [FunOnFinite.linearMap_apply_apply,Finset.sum_smul]
  symm
  calc
    _ = ∑ j, ∑ i ∈ Finset.univ.filter (fun i => f i = j), t.val i • orderedSimplexVertices σ (f i) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise Finset.univ f (fun i => t.val i • orderedSimplexVertices σ (f i))

def simplicialToLipschitzSingular {Y : Type} [MetricSpace Y]
    (h : K.complex.space → Y) (L : NNReal) (hh : LipschitzWith L h) :
    orderedComplexSSet K ⟶ lipschitzSingularSSet Y where
  app _ σ := ⟨⟨fun t => h (orderedSimplexParameter σ t),
    hh.continuous.comp (orderedSimplexParameter_lipschitz σ).continuous⟩,
    L*‖simplexBarycentricLinear (orderedSimplexVertices σ)‖₊,
    hh.comp (orderedSimplexParameter_lipschitz σ)⟩
  naturality _ _ f := by
    funext σ
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    exact congrArg h (orderedSimplexParameter_natural f.unop.toOrderHom σ t)

def finiteSimplicialToLipschitzChainMap {Y : Type} [MetricSpace Y]
    (h : K.complex.space → Y) (L : NNReal) (hh : LipschitzWith L h) :
    finiteSimplicialChainComplex K ⟶ lipschitzSingularChainComplex Y :=
  nondegenerateChainInclusionMap ≫ freeSSetChainMap (simplicialToLipschitzSingular h L hh)

def finiteSimplicialToSingularChainMap {Y : Type} [MetricSpace Y]
    (h : K.complex.space → Y) (L : NNReal) (hh : LipschitzWith L h) :
    finiteSimplicialChainComplex K ⟶ realSingularChainComplex Y :=
  finiteSimplicialToLipschitzChainMap h L hh ≫ forgetLipschitzSingularChainMap Y

end Paper28
