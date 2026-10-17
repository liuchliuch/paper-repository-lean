import Paper28.AtlasFaceCoordinates

/-! The actual spherical cell chart is injective on its closed patch.
This is derived from the realization homeomorphism, exact barycentric
formula and native affine independence, not assumed as a chart conclusion. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
universe w
variable {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]

def closedSphericalPatch {m : ℕ} (q : V → EuclideanAmbient m) (F : Finset V) :
    Set (EuclideanAmbient m) :=
  {u | ∃ t : stdSimplex ℝ V, (∀ v, v ∉ F → t.val v = 0) ∧
    u = sphericalNormalize (∑ v, t.val v • q v)}

theorem spherical_chart_injective_on_closed_patch
    {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    {B : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type w} [MetricSpace Y]
    (C : FullSubcomplexSphericalCharts B Y) (hB : Function.Injective B.vertex) (j : Idx) :
    Set.InjOn (C.chart j) (closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected)) := by
  rintro u ⟨t,ht,hu⟩ v ⟨s,hs,hv⟩ he
  let x : K.complex.space := ⟨∑ a, t.val a • B.vertex a,atlasFacePoint_mem B j t ht⟩
  let y : K.complex.space := ⟨∑ a, s.val a • B.vertex a,atlasFacePoint_mem B j s hs⟩
  have hx := C.barycentric_formula j t ht x rfl
  have hy := C.barycentric_formula j s hs y rfl
  have hxy : C.homeomorph x = C.homeomorph y := by
    rw [hx,hy,← hu,← hv]
    exact he
  have hts := atlasFace_coordinates_unique B hB j t s ht hs
    (congrArg Subtype.val (C.homeomorph.injective hxy))
  rw [hts] at hu
  exact hu.trans hv.symm

theorem atlasSphereLift_mem_closed_patch
    {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    {B : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type w} [MetricSpace Y]
    (C : FullSubcomplexSphericalCharts B Y) (j : Idx) (x : EuclideanAmbient d)
    (hx : x ∈ atlasRetractionDomain B ∩ atlasCell B j) :
    atlasSphereLift B (C.vertex j) j x ∈ closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected) := by
  refine ⟨atlasSimplexCoordinates B x hx.1,atlasCoordinates_zero_off_cell B j x hx.2,?_⟩
  change atlasSphereLift B (C.vertex j) j x =
    sphericalNormalize (∑ v, atlasCoordinates B x v • C.vertex j v)
  rw [atlasCoordinates_weighted_sum B (C.vertex j) x,
    sphericalNormalize_pos_smul _ (inv_pos.mpr hx.1.2),atlasSphereLift_eq B (C.vertex j) j x hx.2]

end Paper28
