import Paper28.SphericalRealizationCharts
import Paper28.AtlasSphericalMap
import Paper28.NormalizedAffineMatrices
import Paper28.RoundStratumPullback

/-! Actual finite smooth round strata for h composed with the explicit
full-subcomplex retraction. All hypotheses of the sharp analytic theorem
are derived from barycentric charts and the actual piecewise round metric. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
universe w
variable {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
  {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  {A : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type w} [MetricSpace Y]
variable (C : FullSubcomplexSphericalCharts A Y)

theorem atlasSphericalMap_chart (y₀ : Y) (j : Idx) (x : EuclideanAmbient d)
    (hx : x ∈ atlasRetractionDomain A) (hxj : x ∈ atlasCell A j) :
    atlasSphericalMap A C.homeomorph y₀ x = C.chart j (atlasSphereLift A (C.vertex j) j x) := by
  rw [atlasSphericalMap_on_domain A C.homeomorph y₀ x hx]
  have hc := C.barycentric_formula j (atlasSimplexCoordinates A x hx)
    (fun v hv => atlasCoordinates_zero_off_cell A j x hxj v hv)
    ⟨atlasRetraction A x,atlasRetraction_mapsTo A hx⟩ (atlasCoordinates_reconstruct A x).symm
  rw [hc]
  congr 1
  change sphericalNormalize (∑ v, atlasCoordinates A x v • C.vertex j v) = _
  rw [atlasCoordinates_weighted_sum A (C.vertex j) x,
    sphericalNormalize_pos_smul _ (inv_pos.mpr hx.2),atlasSphereLift_eq A (C.vertex j) j x hxj]

def atlasSphereDerivativeMatrix (j : Idx) (x : EuclideanAmbient d) :
    Matrix (Fin (C.dimension j)) (Fin d) ℝ :=
  normalizedAffineMatrix (atlasLiftLinear A (C.vertex j) j) (atlasLiftOffset A (C.vertex j) j) x

theorem atlasSphereLift_raw_nonzero (j : Idx) (x : EuclideanAmbient d)
    (hx : x ∈ atlasRetractionDomain A ∩ atlasCell A j) :
    atlasLiftLinear A (C.vertex j) j x+atlasLiftOffset A (C.vertex j) j ≠ 0 := by
  rw [atlasLift_raw_eq A (C.vertex j) j x hx.2]
  exact atlasWeightedVector_nonzero A (C.vertex j) j x hx.1 hx.2 (C.center j) (C.hemisphere j)

theorem atlasSphereDerivativeMatrix_continuous (j : Idx) :
    ContinuousOn (atlasSphereDerivativeMatrix C j) (atlasRetractionDomain A ∩ atlasCell A j) :=
  normalizedAffineMatrix_continuousOn _ _ _ (atlasSphereLift_raw_nonzero C j)

theorem atlasSphereLift_hasFDerivAt (j : Idx) (x : EuclideanAmbient d)
    (hx : x ∈ atlasRetractionDomain A ∩ atlasCell A j) :
    HasFDerivAt (atlasSphereLift A (C.vertex j) j)
      (Matrix.toEuclideanLin (atlasSphereDerivativeMatrix C j x)).toContinuousLinearMap x :=
  normalizedAffineMatrix_derivative _ _ _ (atlasSphereLift_raw_nonzero C j x hx)

theorem atlasSphereLift_unit (j : Idx) (x : EuclideanAmbient d)
    (hx : x ∈ atlasRetractionDomain A ∩ atlasCell A j) :
    ‖atlasSphereLift A (C.vertex j) j x‖ = 1 :=
  normalizedAffineMap_norm _ _ _ (atlasSphereLift_raw_nonzero C j x hx)

theorem atlasSphereLift_round_stratum (y₀ : Y) (j : Idx) (F : realizationFaces A j) :
    RoundLiftOn inferInstance (atlasSphericalMap A C.homeomorph y₀)
      (atlasSphereLift A (C.vertex j) j) (realizationStratum A j F) := by
  apply roundLiftOn_of_chart inferInstance _ _ (C.chart j) (realizationStratum A j F)
    (atlasRetractionDomain A ∩ atlasCell A j) (relativeSphericalPatch (C.vertex j) F.val)
    (fun _ hx => hx.1) (atlasSphereLift_mem_relative C j F)
    (fun x hx => atlasSphericalMap_chart C y₀ j x hx.1.1 hx.1.2)
    (fun x hx => (atlasSphereLift_hasFDerivAt C j x hx).continuousAt)
    (C.round_relative_face j F.val F.property)

theorem atlasCell_isClosed (j : Idx) : IsClosed (atlasCell A j) := by
  exact ((A.cells j).finite_toSet.image A.vertex).isCompact_convexHull.isClosed

theorem atlasCells_cover : atlasRetractionDomain A ⊆ ⋃ j, atlasCell A j := fun _ hx => A.cover hx.1

end Paper28
