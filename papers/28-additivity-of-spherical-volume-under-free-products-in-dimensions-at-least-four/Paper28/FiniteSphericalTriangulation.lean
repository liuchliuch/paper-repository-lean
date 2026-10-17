import Paper28.GeodesicSimplexCurrents
import Paper28.OrderedSimplicialChains
import Paper28.SphericalAtlasBiLipschitz

/-! A finite spherical triangulation has its own finite cells and actual
normalized barycentric charts. It contains no ambient neighborhood atlas,
retraction, Lipschitz estimate, current, approximation or filling data.
Its intrinsic metric is specified separately by actual finite cell paths.
Classical full-neighborhood realization returns only geometric data. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {d : ℕ} (K : FiniteEuclideanComplex (EuclideanAmbient d))
  (Y : Type) [MetricSpace Y]

structure FiniteSphericalTriangulation where
  cellCount : ℕ
  cells : Fin cellCount → Finset K.VertexIndex
  cell_face : ∀ j, (cells j).image K.enumeratedVertex ∈ K.complex.faces
  cover : K.complex.space ⊆ ⋃ j, convexHull ℝ (K.enumeratedVertex '' (cells j : Set K.VertexIndex))
  homeomorph : K.complex.space ≃ₜ Y
  dimension : Fin cellCount → ℕ
  vertex : ∀ j, K.VertexIndex → EuclideanAmbient (dimension j)
  unit_vertex : ∀ j v, v ∈ cells j → ‖vertex j v‖ = 1
  independent : ∀ j, LinearIndependent ℝ (fun v : {v : K.VertexIndex // v ∈ cells j} => vertex j v.val)
  center : ∀ j, EuclideanAmbient (dimension j)
  hemisphere : ∀ j v, v ∈ cells j → 0 < inner ℝ (center j) (vertex j v)
  chart : ∀ j, EuclideanAmbient (dimension j) → Y
  barycentric_formula : ∀ j (t : stdSimplex ℝ K.VertexIndex),
    (∀ v, v ∉ cells j → t.val v = 0) →
    ∀ x : K.complex.space, x.val = ∑ v, t.val v • K.enumeratedVertex v →
      homeomorph x = chart j (sphericalNormalize (∑ v, t.val v • vertex j v))
  round_relative_face : ∀ j (F : Finset K.VertexIndex), F ⊆ cells j →
    ∀ u ∈ relativeSphericalPatch (vertex j) F, ∃ r : ℝ, 0 < r ∧
    ∀ v ∈ relativeSphericalPatch (vertex j) F, ∀ z ∈ relativeSphericalPatch (vertex j) F,
      dist v u < r → dist z u < r → dist (chart j v) (chart j z) = angular v z

variable {K Y} (S : FiniteSphericalTriangulation K Y)

structure TriangulationSphericalStep (x y : Y) where
  cell : Fin S.cellCount
  left : EuclideanAmbient (S.dimension cell)
  right : EuclideanAmbient (S.dimension cell)
  left_mem : left ∈ closedSphericalPatch (S.vertex cell) (S.cells cell)
  right_mem : right ∈ closedSphericalPatch (S.vertex cell) (S.cells cell)
  left_eq : S.chart cell left = x
  right_eq : S.chart cell right = y

inductive TriangulationSphericalPath : Y → Y → Type
  | nil (x : Y) : TriangulationSphericalPath x x
  | cons {x y z : Y} (step : TriangulationSphericalStep S x y)
      (rest : TriangulationSphericalPath y z) : TriangulationSphericalPath x z

def TriangulationSphericalPath.length {x y : Y} : TriangulationSphericalPath S x y → ℝ
  | .nil _ => 0
  | .cons step rest => angular step.left step.right+rest.length

structure IntrinsicSphericalTriangulationMetric : Prop where
  path_exists : ∀ x y, Nonempty (TriangulationSphericalPath S x y)
  distance_formula : ∀ x y, dist x y = sInf (Set.range
    (fun p : TriangulationSphericalPath S x y => p.length))

/-- An actual geometric spherical simplex contained in one source cell.
The isometric lift permits coordinate spheres of different dimensions. -/
structure CellwiseGeodesicParameterization (k : ℕ) where
  geometric : GeodesicSphericalParameterization Y k
  cell : Fin S.cellCount
  embedding : EuclideanAmbient geometric.dimension →ₗᵢ[ℝ] EuclideanAmbient (S.dimension cell)
  chart_eq : ∀ u ∈ sphericalSimplexPatch geometric.rawVertices,
    S.chart cell (embedding u) = geometric.chart u
  location : embedding '' sphericalSimplexPatch geometric.rawVertices ⊆
    closedSphericalPatch (S.vertex cell) (S.cells cell)

def cellwiseSphericalPolyhedralCurrents
    {J : CompactIntegralCurrentAlgebraInput.{0,0} Y inferInstance}
    (A : LipschitzSimplexIntegrationInput inferInstance J) (k : ℕ) : AddSubgroup (J.Current k) :=
  AddSubgroup.closure (Set.range (fun σ : {σ : CellwiseGeodesicParameterization S k //
    LinearIndependent ℝ σ.geometric.rawVertices} => A.integration k σ.val.geometric.parameter))

/-- Geometric output of classical full-subcomplex neighborhood realization.
All fields identify actual charts, cell inclusions and the defining metric.
There are no analytic estimates or current conclusions. -/
structure SphericalNeighborhoodRealization {e : ℕ}
    (K₁ : FiniteEuclideanComplex (EuclideanAmbient e)) where
  vertexCount : ℕ
  cellCount : ℕ
  atlas : FullSubcomplexBarycentricAtlas K₁ (Fin vertexCount) (Fin cellCount)
  charts : FullSubcomplexSphericalCharts atlas Y
  metric : SphericalCellPathMetricInput charts
  nondegenerate : CellVertexIndependence charts
  vertex_injective : Function.Injective atlas.vertex
  sourceCell : Fin cellCount → Fin S.cellCount
  embedding : ∀ j, EuclideanAmbient (charts.dimension j) →ₗᵢ[ℝ] EuclideanAmbient (S.dimension (sourceCell j))
  chart_eq : ∀ j u, u ∈ closedSphericalPatch (charts.vertex j) (atlas.cells j ∩ atlas.selected) →
    S.chart (sourceCell j) (embedding j u) = charts.chart j u
  location : ∀ j, embedding j '' closedSphericalPatch (charts.vertex j) (atlas.cells j ∩ atlas.selected) ⊆
    closedSphericalPatch (S.vertex (sourceCell j)) (S.cells (sourceCell j))

/-- Classical PL realization/full-subcomplex construction, with exact
spherical coordinate and intrinsic metric identifications only. -/
structure SphericalFullNeighborhoodInput : Prop where
  realization : ∀ {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    {Y : Type} [MetricSpace Y] (S : FiniteSphericalTriangulation K Y),
    IntrinsicSphericalTriangulationMetric S →
      ∃ e : ℕ, ∃ K₁ : FiniteEuclideanComplex (EuclideanAmbient e), Nonempty (SphericalNeighborhoodRealization S K₁)

end Paper28
