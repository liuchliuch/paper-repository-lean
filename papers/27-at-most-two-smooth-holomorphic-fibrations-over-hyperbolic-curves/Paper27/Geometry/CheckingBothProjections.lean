import Paper27.Geometry.CoordinateCalculus
import Paper27.LocalProjection

/-!
# Checking the second projection in the intermediate construction

The actual Riemann--Hurwitz formula gives ramification degree eight for a
degree-two map from a genus-nine curve to a genus-three curve. Hence an
actual ramification point exists. Surjective base change lifts that point,
and the actual derivative of the composite remains zero. An actual local
double-branch chart then proves that the actual surface projection fails to
be a submersion. These deductions are separate from the historical existence
of the curves, base change, and branched-cover surface.

Source anchor: P27 Remark 2.5, `S2.Thmtheorem5`, local model `S2.Ex10`.
-/

noncomputable section

open scoped Manifold Topology
open Filter

namespace Paper27.Geometry.CheckingBothProjections

open MetricComparison

section CoordinateZero

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {M : CompactComplexManifold E} {N : CompactComplexManifold F}

/-- A zero actual differential in actual biholomorphic coordinates is a
zero actual manifold differential. Both chart derivatives are invertible. -/
theorem mfderiv_zero_of_coordinate_zero (f : HolomorphicMap M N)
    (e : OpenPartialHomeomorph M E) (t : OpenPartialHomeomorph N F)
    (he : e.MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, E))
    (ht : t.MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, F))
    (p : M) (hp : p ∈ e.source) (hfp : f p ∈ t.source)
    (hzero : fderiv ℂ (t ∘ f ∘ e.symm) (e p) = 0) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f p = 0 := by
  have hz := e.map_source hp
  have hback : e.symm (e p) = p := e.left_inv hp
  have hinv := he.mdifferentiableAt_symm hz
  have htarget : f (e.symm (e p)) ∈ t.source := hback.symm ▸ hfp
  have hformula : fderiv ℂ (t ∘ f ∘ e.symm) (e p) =
      (mfderiv 𝓘(ℂ, F) 𝓘(ℂ, F) t (f (e.symm (e p)))).comp
        ((mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f (e.symm (e p))).comp
          (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) e.symm (e p))) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp (e p) (ht.mdifferentiableAt htarget)
      ((f.holomorphic _).comp (e p) hinv), mfderiv_comp (e p) (f.holomorphic _) hinv]
    rfl
  have hlin := hformula.symm.trans hzero
  let A : E ≃L[ℂ] E := he.symm.mfderiv hz
  let T : F ≃L[ℂ] F := ht.mfderiv htarget
  have hqzero : (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f (e.symm (e p)) : E →L[ℂ] F) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun L => L (A.symm v)) hlin
    change T (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f (e.symm (e p)) (A (A.symm v))) = 0 at hv
    rw [A.apply_symm_apply] at hv
    apply T.injective
    change T (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f (e.symm (e p)) v) = T 0
    rw [map_zero]
    exact hv
  let d : M → (E →L[ℂ] F) := fun x => mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x
  have hpoint : d (e.symm (e p)) = d p := congrArg d hback
  change d (e.symm (e p)) = 0 at hqzero
  change d p = 0
  exact hpoint.symm.trans hqzero

end CoordinateZero

section Curves

variable {C B D : Curve}

/-- At an actual curve ramification point, the actual manifold derivative
vanishes, rather than only a coordinate coefficient. -/
theorem curve_mfderiv_zero_of_written_deriv_zero (u : HolomorphicMap C B) (p : C)
    (hd : deriv (writtenCoordinateMap u p) ((chartAt ℂ p) p) = 0) :
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) u p = 0 := by
  apply mfderiv_zero_of_coordinate_zero u (chartAt ℂ p) (chartAt ℂ (u p))
    (mdifferentiable_chart p) (mdifferentiable_chart (u p)) p
    (mem_chart_source ℂ p) (mem_chart_source ℂ (u p))
  apply ContinuousLinearMap.ext
  intro z
  change fderiv ℂ (writtenCoordinateMap u p) ((chartAt ℂ p) p) z = 0
  rw [fderiv_eq_deriv_mul, hd, zero_mul]

/-- Riemann--Hurwitz for the actual degree-two, genus-nine to genus-three
map gives eight, with no numerical ramification hypothesis. -/
theorem ramification_degree_eight (maps : ClassicalCurveMapFacts)
    (π : HolomorphicMap C B) (hπ : Nonconstant π)
    (hC : C.genus = 9) (hB : B.genus = 3)
    (hf : {p : C | π p = B.basepoint}.Finite) (hdegree : mapDegree π hf = 2) :
    divisorDegree (ramificationDivisor π (maps.ramification_finite C B π hπ)) = 8 := by
  have hRH := maps.riemann_hurwitz C B π hπ (maps.ramification_finite C B π hπ) hf
  norm_num [eulerCharacteristic, hC, hB, hdegree] at hRH
  linarith

/-- Positive degree of the actual effective ramification divisor supplies
an actual point where the derivative is zero. -/
theorem exists_ramification_point (maps : ClassicalCurveMapFacts)
    (π : HolomorphicMap C B) (hπ : Nonconstant π)
    (hC : C.genus = 9) (hB : B.genus = 3)
    (hf : {p : C | π p = B.basepoint}.Finite) (hdegree : mapDegree π hf = 2) :
    ∃ p : C, 0 < ramificationOrder π p ∧
      deriv (writtenCoordinateMap π p) ((chartAt ℂ p) p) = 0 ∧
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) π p = 0 := by
  let R := ramificationDivisor π (maps.ramification_finite C B π hπ)
  have hRdegree := ramification_degree_eight maps π hπ hC hB hf hdegree
  have hex : ∃ p : C, R p ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero : R = 0 := Finsupp.ext h
    change divisorDegree R = 8 at hRdegree
    simp only [hzero, divisorDegree, Finsupp.support_zero, Finset.sum_empty] at hRdegree
    norm_num at hRdegree
  obtain ⟨p, hp⟩ := hex
  have horder : ramificationOrder π p ≠ 0 := hp
  have hd : deriv (writtenCoordinateMap π p) ((chartAt ℂ p) p) = 0 := by
    by_contra hne
    exact horder ((ramificationOrder_eq_zero_iff maps π hπ p).mpr hne)
  exact ⟨p, Nat.pos_of_ne_zero horder, hd, curve_mfderiv_zero_of_written_deriv_zero π p hd⟩

def composeCurveMaps (u : HolomorphicMap C B) (v : HolomorphicMap D C) : HolomorphicMap D B where
  toFun := u ∘ v
  holomorphic := u.holomorphic.comp v.holomorphic

/-- Base change does not remove a zero derivative of the curve map. The
statement needs only a lifted point; etaleness is stronger than necessary. -/
theorem basechange_mfderiv_zero (π : HolomorphicMap C B) (b : HolomorphicMap D C)
    {p : C} (hπ : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) π p = 0)
    {t : D} (ht : b t = p) :
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (composeCurveMaps π b) t = 0 := by
  change mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (π ∘ b) t = 0
  rw [mfderiv_comp t (π.holomorphic _) (b.holomorphic t), ht, hπ]
  exact ContinuousLinearMap.zero_comp _

/-- The actual zero derivative gives zero derivative of the actual graph
function in the fixed actual curve coordinates. -/
theorem written_deriv_zero_of_mfderiv_zero (u : HolomorphicMap C B) (p : C)
    (hu : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) u p = 0) :
    deriv (writtenCoordinateMap u p) ((chartAt ℂ p) p) = 0 := by
  have hs := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have hb : u ((chartAt ℂ p).symm ((chartAt ℂ p) p)) ∈ (chartAt ℂ (u p)).source := by
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
    exact mem_chart_source ℂ (u p)
  rw [← fderiv_deriv]
  change fderiv ℂ (CoordinateCalculus.coordinateMap u p (u p)) ((chartAt ℂ p) p) 1 = 0
  rw [CoordinateCalculus.coordinateMap_derivative u p (u p) hs hb,
    (chartAt ℂ p).left_inv (mem_chart_source ℂ p), hu]
  change mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ (u p)) (u p) (0 : ℂ) = 0
  exact map_zero _

end Curves

section DoubleCharts

variable {X : CompactComplexSurface} {C B : Curve}

/-- Actual local double-branch coordinates for the second projection over
the actual graph map `κ`. No rank or smoothness failure is a field. -/
structure DoubleProjectionChart (h : HolomorphicMap X B) (κ : HolomorphicMap C B) (t : C) where
  point : X
  point_image : h point = κ t
  coordinates : OpenPartialHomeomorph X (ℂ × ℂ)
  source_mem : point ∈ coordinates.source
  holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) coordinates coordinates.source
  inverse_holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
    coordinates.symm coordinates.target
  centre : coordinates point = ((chartAt ℂ t) t, 0)
  maps_target : ∀ q ∈ coordinates.source, h q ∈ (chartAt ℂ (κ t)).source
  identity : ∀ q ∈ coordinates.source,
    (chartAt ℂ (κ t)) (h q) =
      localSecondProjection 2 (writtenCoordinateMap κ t) (coordinates q)

/-- At a zero derivative of the actual graph map, the second actual surface
projection has zero actual manifold differential. -/
theorem double_projection_mfderiv_zero {h : HolomorphicMap X B} {κ : HolomorphicMap C B}
    {t : C} (A : DoubleProjectionChart h κ t)
    (hκ : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) κ t = 0) :
    mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) h A.point = 0 := by
  have hd := written_deriv_zero_of_mfderiv_zero κ t hκ
  have hφ : HasDerivAt (writtenCoordinateMap κ t) 0 ((chartAt ℂ t) t) := by
    have han : AnalyticAt ℂ (writtenCoordinateMap κ t) ((chartAt ℂ t) t) :=
      CoordinateCalculus.curve_coordinateMap_analytic κ t
    simpa only [hd] using han.differentiableAt.hasDerivAt
  have hmodel : HasFDerivAt (𝕜 := ℂ) (localSecondProjection 2 (writtenCoordinateMap κ t))
      0 (A.coordinates A.point) := by
    rw [A.centre]
    exact hasFDerivAt_localSecondProjection_zero 2 (by decide) hφ
  have hgerm : (chartAt ℂ (κ t)) ∘ h ∘ A.coordinates.symm =ᶠ[𝓝 (A.coordinates A.point)]
      localSecondProjection 2 (writtenCoordinateMap κ t) := by
    filter_upwards [A.coordinates.open_target.mem_nhds (A.coordinates.map_source A.source_mem)]
      with z hz
    have hid := A.identity (A.coordinates.symm z) (A.coordinates.map_target hz)
    rw [A.coordinates.right_inv hz] at hid
    exact hid
  exact mfderiv_zero_of_coordinate_zero h A.coordinates (chartAt ℂ (κ t))
    ⟨A.holomorphic, A.inverse_holomorphic⟩ (mdifferentiable_chart (κ t)) A.point A.source_mem
    (A.maps_target A.point A.source_mem) (hgerm.fderiv_eq.trans hmodel.fderiv)

def IsSubmersion (h : HolomorphicMap X B) : Prop :=
  ∀ p : X, Function.Surjective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) h p)

theorem double_projection_not_submersion {h : HolomorphicMap X B} {κ : HolomorphicMap C B}
    {t : C} (A : DoubleProjectionChart h κ t)
    (hκ : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) κ t = 0) : ¬ IsSubmersion h := by
  intro hs
  have hzero := double_projection_mfderiv_zero A hκ
  obtain ⟨v, hv⟩ := hs A.point (1 : ℂ)
  rw [hzero] at hv
  exact (zero_ne_one : (0 : ℂ) ≠ 1) hv

/-- This conclusion is about the actual surface map and actual curve base.
Surjective etale base change lifts the ramification point; the zero-chain
argument in fact only requires surjectivity of that base change. -/
theorem basechanged_double_projection_not_submersion {F : Curve}
    (maps : ClassicalCurveMapFacts) (π : HolomorphicMap F B) (hπ : Nonconstant π)
    (hF : F.genus = 9) (hB : B.genus = 3)
    (hf : {p : F | π p = B.basepoint}.Finite) (hdegree : mapDegree π hf = 2)
    (b : HolomorphicMap C F) (hb : Function.Surjective b)
    (h : HolomorphicMap X B)
    (charts : ∀ t : C, Nonempty (DoubleProjectionChart h (composeCurveMaps π b) t)) :
    ¬ IsSubmersion h := by
  obtain ⟨p, _horder, _hcoordinate, hzero⟩ := exists_ramification_point maps π hπ hF hB hf hdegree
  obtain ⟨t, ht⟩ := hb p
  obtain ⟨A⟩ := charts t
  exact double_projection_not_submersion A (basechange_mfderiv_zero π b hzero ht)

theorem basechanged_double_fibration_not_smooth {F : Curve}
    (maps : ClassicalCurveMapFacts) (h : Fibration X)
    (π : HolomorphicMap F h.base) (hπ : Nonconstant π)
    (hF : F.genus = 9) (hB : h.base.genus = 3)
    (hf : {p : F | π p = h.base.basepoint}.Finite) (hdegree : mapDegree π hf = 2)
    (b : HolomorphicMap C F) (hb : Function.Surjective b)
    (charts : ∀ t : C, Nonempty (DoubleProjectionChart
      (CoordinateCalculus.fibrationMap h) (composeCurveMaps π b) t)) : ¬ h.Smooth :=
  basechanged_double_projection_not_submersion maps π hπ hF hB hf hdegree b hb
    (CoordinateCalculus.fibrationMap h) charts

end DoubleCharts

/-- Minimal raw data from the published intermediate genus-six-family
construction. Only one connected component of the parameter curve is used;
its etale degree is deliberately not identified with the possibly
disconnected original degree 64. The second projection is an actual map,
with no unverified connected-fibre assertion included. -/
structure ZaalIntermediateData where
  genusThreeCurve : Curve
  genusNineCurve : Curve
  parameterCurve : Curve
  surface : CompactComplexSurface
  π : HolomorphicMap genusNineCurve genusThreeCurve
  π_nonconstant : Nonconstant π
  genus_nine : genusNineCurve.genus = 9
  genus_three : genusThreeCurve.genus = 3
  fibre_finite : {p : genusNineCurve | π p = genusThreeCurve.basepoint}.Finite
  degree_two : mapDegree π fibre_finite = 2
  baseChange : HolomorphicMap parameterCurve genusNineCurve
  baseChange_surjective : Function.Surjective baseChange
  baseChange_unramified : ∀ p : parameterCurve,
    Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) baseChange p)
  secondProjection : HolomorphicMap surface genusThreeCurve
  local_double_chart : ∀ t : parameterCurve,
    Nonempty (DoubleProjectionChart secondProjection (composeCurveMaps π baseChange) t)

/-- Explicit historical construction input: C. Zaal, *Explicit complete
curves in the moduli space of curves of genus three*, Geom. Dedicata 56
(1995), pp. 186–187 (the intermediate genus-six family, not the later
genus-three construction), original published scan
https://pure.uva.nl/ws/files/3875454/1106_11965y.pdf . The two projection
restrictions of the translated fibre product have degree two. This input
contains neither ramification degree eight nor a nonsubmersion conclusion. -/
def ZaalIntermediateConstruction : Prop := Nonempty ZaalIntermediateData

theorem ZaalIntermediateData.second_projection_not_submersion
    (A : ZaalIntermediateData) (maps : ClassicalCurveMapFacts) :
    ¬ IsSubmersion A.secondProjection :=
  basechanged_double_projection_not_submersion maps A.π A.π_nonconstant
    A.genus_nine A.genus_three A.fibre_finite A.degree_two
    A.baseChange A.baseChange_surjective A.secondProjection A.local_double_chart

/-- The historical input is instantiated, then Riemann--Hurwitz, base-change
calculus, and the actual local model prove failure of the second projection. -/
theorem checking_both_projections (maps : ClassicalCurveMapFacts)
    (construction : ZaalIntermediateConstruction) :
    ∃ (X : CompactComplexSurface) (B : Curve) (h : HolomorphicMap X B), ¬ IsSubmersion h := by
  obtain ⟨A⟩ := construction
  exact ⟨A.surface, A.genusThreeCurve, A.secondProjection, A.second_projection_not_submersion maps⟩

end Paper27.Geometry.CheckingBothProjections
