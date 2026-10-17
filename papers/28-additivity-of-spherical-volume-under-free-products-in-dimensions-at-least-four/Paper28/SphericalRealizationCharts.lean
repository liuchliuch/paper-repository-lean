import Paper28.AtlasNormalizedCoordinates
import Paper28.EuclideanAreaInput

/-! Geometric coordinate data for a finite spherical realization. The
fields specify its actual barycentric charts and piecewise round metric.
They contain no retraction, derivative, current, approximation, sharp mass
estimate or filling assertion. Existence of these data is a separate task. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
universe w
variable {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]

def relativeSphericalPatch {m : ℕ} (q : V → EuclideanAmbient m) (F : Finset V) :
    Set (EuclideanAmbient m) :=
  {u | ∃ t : stdSimplex ℝ V, (∀ v, 0 < t.val v ↔ v ∈ F) ∧
    u = sphericalNormalize (∑ v, t.val v • q v)}

structure FullSubcomplexSphericalCharts {d : ℕ}
    {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    (A : FullSubcomplexBarycentricAtlas K V Idx) (Y : Type w) [MetricSpace Y] where
  homeomorph : K.complex.space ≃ₜ Y
  dimension : Idx → ℕ
  vertex : ∀ j, V → EuclideanAmbient (dimension j)
  unit_vertex : ∀ j v, v ∈ A.cells j ∩ A.selected → ‖vertex j v‖ = 1
  center : ∀ j, EuclideanAmbient (dimension j)
  hemisphere : ∀ j v, v ∈ A.cells j ∩ A.selected → 0 < inner ℝ (center j) (vertex j v)
  chart : ∀ j, EuclideanAmbient (dimension j) → Y
  barycentric_formula : ∀ j (t : stdSimplex ℝ V),
    (∀ v, v ∉ A.cells j ∩ A.selected → t.val v = 0) →
    ∀ x : K.complex.space, x.val = ∑ v, t.val v • A.vertex v →
      homeomorph x = chart j (sphericalNormalize (∑ v, t.val v • vertex j v))
  round_relative_face : ∀ j (F : Finset V), F ⊆ A.cells j ∩ A.selected →
    ∀ u ∈ relativeSphericalPatch (vertex j) F, ∃ r : ℝ, 0 < r ∧
    ∀ v ∈ relativeSphericalPatch (vertex j) F, ∀ z ∈ relativeSphericalPatch (vertex j) F,
      dist v u < r → dist z u < r → dist (chart j v) (chart j z) = angular v z

variable {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  {A : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type w} [MetricSpace Y]

abbrev realizationFaces (A : FullSubcomplexBarycentricAtlas K V Idx) (j : Idx) :=
  {F : Finset V // F ⊆ A.cells j ∩ A.selected}

def realizationStratum (A : FullSubcomplexBarycentricAtlas K V Idx) (j : Idx)
    (F : realizationFaces A j) : Set (EuclideanAmbient d) :=
  (atlasRetractionDomain A ∩ atlasCell A j) ∩ {x | atlasPositiveFace A x = F.val}

theorem realizationStrata_cover (j : Idx) :
    atlasRetractionDomain A ∩ atlasCell A j ⊆ ⋃ F : realizationFaces A j, realizationStratum A j F := by
  intro x hx
  exact mem_iUnion.mpr ⟨⟨atlasPositiveFace A x,atlasPositiveFace_subset A j x hx.2⟩,hx,rfl⟩

theorem atlasSphereLift_mem_relative (C : FullSubcomplexSphericalCharts A Y) (j : Idx)
    (F : realizationFaces A j) (x : EuclideanAmbient d) (hx : x ∈ realizationStratum A j F) :
    atlasSphereLift A (C.vertex j) j x ∈ relativeSphericalPatch (C.vertex j) F.val := by
  refine ⟨atlasSimplexCoordinates A x hx.1.1,?_,?_⟩
  · intro v
    change 0 < atlasCoordinates A x v ↔ v ∈ F.val
    rw [atlasCoordinates_pos_iff A x hx.1.1 v,hx.2]
  · rw [atlasSphereLift_eq A (C.vertex j) j x hx.1.2]
    change sphericalNormalize (atlasWeightedVector A (C.vertex j) x) =
      sphericalNormalize (∑ v, atlasCoordinates A x v • C.vertex j v)
    rw [atlasCoordinates_weighted_sum A (C.vertex j) x,
      sphericalNormalize_pos_smul _ (inv_pos.mpr hx.1.1.2)]

end Paper28
