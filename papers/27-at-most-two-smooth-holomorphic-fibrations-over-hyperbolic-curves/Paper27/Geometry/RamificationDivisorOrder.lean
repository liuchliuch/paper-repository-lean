import Paper27.Geometry.ActualCyclicModels
import Paper27.Geometry.RetractionCoordinateGerms
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The actual Jacobian divisor coefficient of a cyclic branch

The determinant is the genuine two-by-two complex Jacobian, obtained from
the actual Fréchet derivative in the standard coordinate vectors. In cyclic
coordinates it is calculated here to be `n * y^(n-1)`. Consequently its
actual analytic order on a transverse normal slice is `n-1`.

For actual surface cyclic charts, the coordinate function is the actual
map in the actual source and target charts. The coefficient is defined by
its analytic order, not supplied as a divisor label. The local-degree
calculation then identifies this coefficient plus one with the actual local
degree, and hence with the uniform index proved on a connected component.
-/

noncomputable section

open scoped Manifold Topology
open Filter

namespace Paper27.Geometry.RamificationDivisorOrder

open RamificationIndexConstancy

/-- The determinant of the actual complex derivative in the standard
ordered coordinate vectors `(1,0),(0,1)`. -/
def complexJacobian (F : ℂ × ℂ → ℂ × ℂ) (p : ℂ × ℂ) : ℂ :=
  (fderiv ℂ F p (1, 0)).1 * (fderiv ℂ F p (0, 1)).2 -
    (fderiv ℂ F p (0, 1)).1 * (fderiv ℂ F p (1, 0)).2

/-- The usual Jacobian matrix has as columns the images of the two standard
vectors under the actual derivative. -/
def jacobianMatrix (F : ℂ × ℂ → ℂ × ℂ) (p : ℂ × ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(fderiv ℂ F p (1, 0)).1, (fderiv ℂ F p (0, 1)).1;
     (fderiv ℂ F p (1, 0)).2, (fderiv ℂ F p (0, 1)).2]

theorem complexJacobian_eq_det (F : ℂ × ℂ → ℂ × ℂ) (p : ℂ × ℂ) :
    complexJacobian F p = (jacobianMatrix F p).det := by
  simp only [complexJacobian, jacobianMatrix, Matrix.det_fin_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

theorem complexJacobian_congr {F G : ℂ × ℂ → ℂ × ℂ} {p : ℂ × ℂ}
    (h : F =ᶠ[𝓝 p] G) : complexJacobian F p = complexJacobian G p := by
  unfold complexJacobian
  rw [h.fderiv_eq]

/-- The determinant calculation for the actual cyclic map, including the
off-diagonal graph derivative. Those terms cancel in the determinant. -/
theorem complexJacobian_localBranchMap (n : ℕ) {φ : ℂ → ℂ} {x y : ℂ}
    (hφ : AnalyticAt ℂ φ x) :
    complexJacobian (localBranchMap n φ) (x, y) = (n : ℂ) * y ^ (n - 1) := by
  have hder := CyclicModel.hasFDerivAt_model n (q := (x, y)) hφ.differentiableAt.hasDerivAt
  unfold complexJacobian
  rw [hder.fderiv]
  simp only [CyclicModel.jointDifferential_apply, mul_one, mul_zero, add_zero, zero_add,
    one_mul, zero_mul, sub_zero]

/-- An exact cyclic formula on an open coordinate domain determines the
actual coordinate Jacobian at every point of that domain. -/
theorem complexJacobian_of_cyclic_identity {F : ℂ × ℂ → ℂ × ℂ}
    {φ : ℂ → ℂ} {n : ℕ} {V : Set (ℂ × ℂ)} (hV : IsOpen V)
    (hidentity : Set.EqOn F (localBranchMap n φ) V)
    {p : ℂ × ℂ} (hp : p ∈ V) (hφ : AnalyticAt ℂ φ p.1) :
    complexJacobian F p = (n : ℂ) * p.2 ^ (n - 1) := by
  have hgerm : F =ᶠ[𝓝 p] localBranchMap n φ :=
    Filter.eventually_of_mem (hV.mem_nhds hp) fun q hq => hidentity hq
  rw [complexJacobian_congr hgerm]
  exact complexJacobian_localBranchMap n hφ

/-- The coefficient is nonzero because the index is positive; the actual
analytic order is therefore precisely the power `n-1`. -/
theorem analyticOrderAt_cyclic_jacobian (n : ℕ) (hn : 0 < n) :
    analyticOrderAt (fun y : ℂ => (n : ℂ) * y ^ (n - 1)) 0 = (n - 1 : ℕ) := by
  have han : AnalyticAt ℂ (fun y : ℂ => (n : ℂ) * y ^ (n - 1)) 0 :=
    analyticAt_const.mul (analyticAt_id.pow (n - 1))
  apply han.analyticOrderAt_eq_natCast.mpr
  refine ⟨fun _ => (n : ℂ), analyticAt_const, ?_, ?_⟩
  · exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  · exact Filter.Eventually.of_forall fun y => by simp only [sub_zero, smul_eq_mul, mul_comm]

theorem analyticOrderNatAt_cyclic_jacobian (n : ℕ) (hn : 0 < n) :
    analyticOrderNatAt (fun y : ℂ => (n : ℂ) * y ^ (n - 1)) 0 = n - 1 := by
  simp only [analyticOrderNatAt, analyticOrderAt_cyclic_jacobian n hn, ENat.toNat_coe]

/-- On a transverse slice of any open cyclic representative, the actual
Jacobian has the asserted germ and exact analytic order. -/
theorem transverse_jacobian_germ {F : ℂ × ℂ → ℂ × ℂ}
    {φ : ℂ → ℂ} {n : ℕ} {V : Set (ℂ × ℂ)} {a : ℂ}
    (hV : IsOpen V) (ha : (a, (0 : ℂ)) ∈ V)
    (hidentity : Set.EqOn F (localBranchMap n φ) V) (hφ : AnalyticAt ℂ φ a) :
    (fun y : ℂ => complexJacobian F (a, y)) =ᶠ[𝓝 0]
      fun y => (n : ℂ) * y ^ (n - 1) := by
  have hline : Tendsto (fun y : ℂ => (a, y)) (𝓝 0) (𝓝 (a, 0)) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  exact Filter.eventually_of_mem (hline (hV.mem_nhds ha)) fun y hy =>
    complexJacobian_of_cyclic_identity hV hidentity hy hφ

theorem transverse_jacobian_order {F : ℂ × ℂ → ℂ × ℂ}
    {φ : ℂ → ℂ} {n : ℕ} {V : Set (ℂ × ℂ)} {a : ℂ}
    (hn : 0 < n) (hV : IsOpen V) (ha : (a, (0 : ℂ)) ∈ V)
    (hidentity : Set.EqOn F (localBranchMap n φ) V) (hφ : AnalyticAt ℂ φ a) :
    analyticOrderAt (fun y : ℂ => complexJacobian F (a, y)) 0 = (n - 1 : ℕ) := by
  rw [analyticOrderAt_congr (transverse_jacobian_germ hV ha hidentity hφ)]
  exact analyticOrderAt_cyclic_jacobian n hn

section Surfaces

variable {X Y : CompactComplexSurface}
  {q : RamificationSupport.FiniteSurjectiveHolomorphicMap X Y} {p : X}

/-- The actual finite holomorphic map written in the actual cyclic source
and target charts. -/
def writtenMap (A : SurfaceCyclicChart q p) : ℂ × ℂ → ℂ × ℂ :=
  A.target ∘ q.map ∘ A.source.symm

theorem writtenMap_identity (A : SurfaceCyclicChart q p) :
    Set.EqOn (writtenMap A) (localBranchMap A.exponent A.graph) A.source.target := by
  intro z hz
  have hid := A.identity (A.source.symm z) (A.source.map_target hz)
  rw [A.source.right_inv hz] at hid
  exact hid

/-- The actual transverse-coordinate Jacobian order of this chart. It is
defined only by actual derivatives and actual analytic order. -/
def divisorCoefficient (A : SurfaceCyclicChart q p) (x : X) : ℕ :=
  analyticOrderNatAt (fun y : ℂ => complexJacobian (writtenMap A) ((A.source x).1, y)) 0

theorem surface_jacobian_germ (A : SurfaceCyclicChart q p) {x : X}
    (hx : x ∈ A.source.source) (hcritical : x ∈ criticalSet q) :
    (fun y : ℂ => complexJacobian (writtenMap A) ((A.source x).1, y)) =ᶠ[𝓝 0]
      fun y => (A.exponent : ℂ) * y ^ (A.exponent - 1) := by
  have hy := (A.axis x hx).mp hcritical
  have ht : ((A.source x).1, (0 : ℂ)) ∈ A.source.target := by
    rw [← hy]
    exact A.source.map_source hx
  exact transverse_jacobian_germ A.source.open_target ht (writtenMap_identity A)
    (A.graph_analytic x hx)

theorem surface_jacobian_order (A : SurfaceCyclicChart q p) {x : X}
    (hx : x ∈ A.source.source) (hcritical : x ∈ criticalSet q) :
    analyticOrderAt (fun y : ℂ => complexJacobian (writtenMap A) ((A.source x).1, y)) 0 =
      (A.exponent - 1 : ℕ) := by
  rw [analyticOrderAt_congr (surface_jacobian_germ A hx hcritical)]
  exact analyticOrderAt_cyclic_jacobian _ (by have hn := A.exponent_ge_two; omega)

theorem divisorCoefficient_eq (A : SurfaceCyclicChart q p) {x : X}
    (hx : x ∈ A.source.source) (hcritical : x ∈ criticalSet q) :
    divisorCoefficient A x = A.exponent - 1 := by
  unfold divisorCoefficient
  simp only [analyticOrderNatAt, surface_jacobian_order A hx hcritical, ENat.toNat_coe]

/-- The divisor coefficient is the local degree minus one. Its relation to
the local degree is proved from the actual cyclic determinant computation. -/
theorem divisorCoefficient_add_one (A : SurfaceCyclicChart q p) (degrees : FiniteLocalDegreeTheory)
    {x : X} (hx : x ∈ A.source.source) (hcritical : x ∈ criticalSet q) :
    divisorCoefficient A x + 1 = degrees.localDegree X Y q x := by
  rw [divisorCoefficient_eq A hx hcritical, A.degree_at_critical degrees hx hcritical]
  have hn := A.exponent_ge_two
  omega

/-- In particular, every actual chart on a connected component with the
already proved uniform index `n` reads divisor coefficient `n-1`. -/
theorem component_divisorCoefficient (D : EmbeddedCurve X) (n : ℕ)
    (hD : D.support ⊆ criticalSet q)
    (hindex : ∀ t : D.curve, ∀ A : SurfaceCyclicChart q (D.inclusion t), A.exponent = n)
    (t : D.curve) (A : SurfaceCyclicChart q (D.inclusion t)) :
    divisorCoefficient A (D.inclusion t) = n - 1 := by
  rw [divisorCoefficient_eq A A.source_mem (hD ⟨t, rfl⟩), hindex t A]

end Surfaces

section Retractions

variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r s : D.Retraction U} {n : ℕ}

/-- The pair of actual retractions, in the same actual base chart and the
actual normal source chart of their constructed atlas. -/
def normalAtlasWrittenMap (A : RetractionCoordinateGerms.NormalAtlas D U r s n)
    (i p : D.curve) : ℂ × ℂ → ℂ × ℂ := fun z =>
  ((chartAt ℂ i) (r.toFun ((A.chart i p).coordinates.symm z)),
    (chartAt ℂ i) (s.toFun ((A.chart i p).coordinates.symm z)))

theorem normalAtlasWrittenMap_identity (A : RetractionCoordinateGerms.NormalAtlas D U r s n)
    (i p : D.curve) :
    Set.EqOn (normalAtlasWrittenMap A i p) (localBranchMap n id) (A.chart i p).coordinates.target := by
  intro z hz
  have hq := (A.chart i p).coordinates.map_target hz
  have hr := (A.chart i p).r_normal _ hq
  have hs := (A.chart i p).s_normal _ hq
  rw [(A.chart i p).coordinates.right_inv hz] at hr hs
  apply Prod.ext
  · exact hr
  · simpa only [localBranchMap, id_eq, add_comm] using hs

theorem normalAtlas_jacobian_germ (A : RetractionCoordinateGerms.NormalAtlas D U r s n)
    (i p : D.curve) (hp : p ∈ D.curve.chartDomain i) :
    (fun y : ℂ => complexJacobian (normalAtlasWrittenMap A i p) ((chartAt ℂ i) p, y)) =ᶠ[𝓝 0]
      fun y => (n : ℂ) * y ^ (n - 1) := by
  have ht : ((chartAt ℂ i) p, (0 : ℂ)) ∈ (A.chart i p).coordinates.target := by
    rw [← A.centre i p hp]
    exact (A.chart i p).coordinates.map_source (A.source_mem i p hp)
  exact transverse_jacobian_germ (A.chart i p).coordinates.open_target ht
    (normalAtlasWrittenMap_identity A i p) analyticAt_id

theorem normalAtlas_jacobian_order (A : RetractionCoordinateGerms.NormalAtlas D U r s n)
    (hn : 0 < n) (i p : D.curve) (hp : p ∈ D.curve.chartDomain i) :
    analyticOrderAt
      (fun y : ℂ => complexJacobian (normalAtlasWrittenMap A i p) ((chartAt ℂ i) p, y)) 0 =
      (n - 1 : ℕ) := by
  rw [analyticOrderAt_congr (normalAtlas_jacobian_germ A i p hp)]
  exact analyticOrderAt_cyclic_jacobian n hn

theorem normalAtlas_divisorCoefficient (A : RetractionCoordinateGerms.NormalAtlas D U r s n)
    (hn : 0 < n) (i p : D.curve) (hp : p ∈ D.curve.chartDomain i) :
    analyticOrderNatAt
      (fun y : ℂ => complexJacobian (normalAtlasWrittenMap A i p) ((chartAt ℂ i) p, y)) 0 =
      n - 1 := by
  simp only [analyticOrderNatAt, normalAtlas_jacobian_order A hn i p hp, ENat.toNat_coe]

end Retractions

end Paper27.Geometry.RamificationDivisorOrder
