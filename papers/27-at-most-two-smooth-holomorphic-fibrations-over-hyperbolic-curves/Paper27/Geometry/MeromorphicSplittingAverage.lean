import Paper27.Geometry.RetractionCoefficientHolomorphic
import Paper27.Geometry.NeighbourhoodSplittings
import Paper27.Geometry.Obstruction
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Actual meromorphic splitting coefficients and formula (6)

The scalar Laurent interface is universal for ordinary meromorphic germs.
Pole bounds and principal coefficients of the actual retractions are proved
from their actual coordinate derivatives and the analytic normal factor.
-/
noncomputable section
open scoped Manifold Topology BigOperators
open Filter Polynomial Finset

namespace Paper27.Geometry.MeromorphicSplittingAverage
open RetractionCoordinateGerms RetractionCoefficientHolomorphic

/-- Ordinary scalar Laurent coefficient extraction and the removable-pole
criterion, independent of all curves, retractions and averaging arguments.
The linear map on all functions is a linear extension of extraction on the
subspace of meromorphic germs; only meromorphic functions are used below. -/
structure LaurentCalculus where
  coeff : (ℂ → ℂ) →ₗ[ℂ] CyclicLaurent.Coefficients
  congr : ∀ {f g : ℂ → ℂ}, f =ᶠ[𝓝[≠] 0] g → coeff f = coeff g
  monomial : ∀ (c : ℂ) (e k : ℤ),
    coeff (fun z => c * z ^ e) k = if k = e then c else 0
  below : ∀ (h : ℂ → ℂ) (e k : ℤ), AnalyticAt ℂ h 0 → k < e →
    coeff (fun z => z ^ e * h z) k = 0
  leading : ∀ (h : ℂ → ℂ) (e : ℤ), AnalyticAt ℂ h 0 →
    coeff (fun z => z ^ e * h z) e = h 0
  rotation : ∀ (f : ℂ → ℂ) (α : ℂ), MeromorphicAt f 0 → α ≠ 0 → ∀ k : ℤ,
    coeff (fun z => α * f (α⁻¹ * z)) k = α ^ (1 - k) * coeff f k
  removable : ∀ f : ℂ → ℂ, MeromorphicAt f 0 →
    (∀ k : ℤ, k < 0 → coeff f k = 0) →
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g =ᶠ[𝓝[≠] 0] f ∧ g 0 = coeff f 0

variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ r₃ : D.Retraction U} {n : ℕ}

end Paper27.Geometry.MeromorphicSplittingAverage

namespace Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
open RetractionCoefficientHolomorphic MeromorphicSplittingAverage
variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ r₃ : D.Retraction U} {n : ℕ}
  (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)

/-- Actual horizontal and normal partial derivatives of a retraction's actual
written-coordinate function on the actual normal slice. -/
def horizontalPartial (r : D.Retraction U) (i p : D.curve) (y : ℂ) : ℂ :=
  fderiv ℂ (A.coordinate r i p) ((chartAt ℂ i) p, y) (1, 0)

def normalPartial (r : D.Retraction U) (i p : D.curve) (y : ℂ) : ℂ :=
  fderiv ℂ (A.coordinate r i p) ((chartAt ℂ i) p, y) (0, 1)

/-- The actual scalar coefficient of the kernel splitting in normal coordinates. -/
def verticalSplitting (r : D.Retraction U) (i p : D.curve) (y : ℂ) : ℂ :=
  -A.horizontalPartial r i p y / A.normalPartial r i p y

 theorem coordinate_analytic (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (r : D.Retraction U) (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    AnalyticAt ℂ (A.coordinate r i p) ((chartAt ℂ i) p, 0) := by
  have hh := ((A.centered i p hi).family_analytic r regularity hi).add analyticAt_fst
  convert hh using 1
  ext w
  change (chartAt ℂ i) (r.toFun ((A.chart i p).coordinates.symm w)) =
    ((chartAt ℂ i) (r.toFun ((A.chart i p).coordinates.symm w)) - w.1) + w.1
  ring

 theorem horizontalPartial_analytic (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (r : D.Retraction U) (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    AnalyticAt ℂ (A.horizontalPartial r i p) 0 := by
  exact NormalizedDifferentials.analytic_coefficientOne
    (A.coordinate_analytic regularity r i p hi) (analyticAt_const.prod analyticAt_id)

 theorem normalPartial_analytic (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (r : D.Retraction U) (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    AnalyticAt ℂ (A.normalPartial r i p) 0 := by
  exact NormalizedDifferentials.analytic_coefficientTwo
    (A.coordinate_analytic regularity r i p hi) (analyticAt_const.prod analyticAt_id)

/-- The axis identity is a consequence of actual chart inverse identities and
r restricting to the identity on the actual embedded curve. -/
 theorem coordinate_axis_germ (r : D.Retraction U) (i p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) :
    (fun x => A.coordinate r i p (x, 0)) =ᶠ[𝓝 ((chartAt ℂ i) p)] id := by
  have hto : Tendsto (chartAt ℂ i).symm (𝓝 ((chartAt ℂ i) p)) (𝓝 p) := by
    simpa only [(chartAt ℂ i).left_inv hi] using
      ((chartAt ℂ i).continuousAt_symm ((chartAt ℂ i).map_source hi)).tendsto
  have hinc : Tendsto (fun x => D.inclusion ((chartAt ℂ i).symm x))
      (𝓝 ((chartAt ℂ i) p)) (𝓝 (D.inclusion p)) :=
    D.inclusion.holomorphic.continuous.continuousAt.tendsto.comp hto
  filter_upwards [(chartAt ℂ i).open_target.mem_nhds ((chartAt ℂ i).map_source hi),
    hinc ((A.chart i p).coordinates.open_source.mem_nhds (A.source_mem i p hi))] with x hx hcx
  have hcentre := (A.centered i p hi).centre_at ((chartAt ℂ i).symm x) hcx
  change (A.chart i p).coordinates (D.inclusion ((chartAt ℂ i).symm x)) = _ at hcentre
  rw [(chartAt ℂ i).right_inv hx] at hcentre
  change (chartAt ℂ i) (r.toFun ((A.chart i p).coordinates.symm (x, 0))) = x
  rw [← hcentre, (A.chart i p).coordinates.left_inv hcx, r.retract,
    (chartAt ℂ i).right_inv hx]

 theorem horizontalPartial_zero (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (r : D.Retraction U) (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    A.horizontalPartial r i p 0 = 1 := by
  have hline : HasDerivAt (fun x : ℂ => (x, (0 : ℂ))) (1, 0) ((chartAt ℂ i) p) :=
    (hasDerivAt_id _).prodMk (hasDerivAt_const _ (0 : ℂ))
  have hc := (A.coordinate_analytic regularity r i p hi).differentiableAt.hasFDerivAt.comp_hasDerivAt
    ((chartAt ℂ i) p) hline
  exact hc.deriv.symm.trans ((A.coordinate_axis_germ r i p hi).deriv_eq.trans (deriv_id _))

 theorem normalPartial_third_derivative (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (r : D.Retraction U) (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    A.normalPartial r i p =ᶠ[𝓝 0] deriv (A.third r i p) := by
  have hline : AnalyticAt ℂ (fun y : ℂ => ((chartAt ℂ i) p, y)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hnear := hline.continuousAt.tendsto.eventually
    (A.coordinate_analytic regularity r i p hi).eventually_analyticAt
  filter_upwards [hnear] with y hy
  have hder : HasDerivAt (A.third r i p)
      (A.normalPartial r i p y) y := by
    exact (hy.differentiableAt.hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_const y ((chartAt ℂ i) p)).prodMk (hasDerivAt_id y))).sub_const _
  exact hder.deriv.symm

/-- Differentiate the actual normal factor, retaining every higher coefficient. -/
 theorem third_derivative_factor (r : D.Retraction U) (ho : A.HasThirdOrder r)
    (hn : 0 < n) (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    deriv (A.third r i p) =ᶠ[𝓝 0] fun y => y ^ (n - 1) *
      ((n : ℂ) * A.thirdFactor r ho i p y + y * deriv (A.thirdFactor r ho i p) y) := by
  have hh := (A.thirdFactor_spec r ho i p hi).1
  filter_upwards [(A.thirdFactor_spec r ho i p hi).2.2.deriv, hh.eventually_analyticAt] with y hy hhy
  have hp := ((hasDerivAt_pow n y).mul hhy.differentiableAt.hasDerivAt).deriv
  have hyn : y ^ n = y ^ (n - 1) * y := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    exact pow_succ _ _
  calc
    deriv (A.third r i p) y = (n : ℂ) * y ^ (n - 1) * A.thirdFactor r ho i p y +
        y ^ n * deriv (A.thirdFactor r ho i p) y := hy.trans hp
    _ = _ := by rw [hyn]; ring

/-- The analytic denominator unit in the actual quotient -rx/ry. -/
def derivativeUnit (r : D.Retraction U) (ho : A.HasThirdOrder r) (i p : D.curve) (y : ℂ) : ℂ :=
  (n : ℂ) * A.thirdFactor r ho i p y + y * deriv (A.thirdFactor r ho i p) y

 theorem derivativeUnit_analytic (r : D.Retraction U) (ho : A.HasThirdOrder r)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    AnalyticAt ℂ (A.derivativeUnit r ho i p) 0 := by
  have hh := (A.thirdFactor_spec r ho i p hi).1
  exact (analyticAt_const.mul hh).add (analyticAt_id.mul hh.deriv)

 theorem derivativeUnit_zero (r : D.Retraction U) (ho : A.HasThirdOrder r)
    (i p : D.curve) : A.derivativeUnit r ho i p 0 = (n : ℂ) * A.leading r ho i p := by
  simp only [derivativeUnit, zero_mul, add_zero, leading]

/-- The actual splitting coefficient is a monomial y^(1-n) times an analytic
unit. In particular its pole bound and leading coefficient are conclusions. -/
 theorem verticalSplitting_factor (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (r : D.Retraction U) (ho : A.HasThirdOrder r) (hn : 0 < n)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h 0 = -(1 / ((n : ℂ) * A.leading r ho i p)) ∧
      A.verticalSplitting r i p =ᶠ[𝓝[≠] 0] fun y => y ^ (1 - (n : ℤ)) * h y := by
  let h : ℂ → ℂ := fun y => -A.horizontalPartial r i p y / A.derivativeUnit r ho i p y
  have hunit : A.derivativeUnit r ho i p 0 ≠ 0 := by
    rw [A.derivativeUnit_zero]
    exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hn)) (A.leading_ne_zero r ho i p hi)
  refine ⟨h, (A.horizontalPartial_analytic regularity r i p hi).neg.div
    (A.derivativeUnit_analytic r ho i p hi) hunit, ?_, ?_⟩
  · dsimp only [h]
    rw [A.horizontalPartial_zero regularity r i p hi, A.derivativeUnit_zero]
    ring
  · filter_upwards [(A.normalPartial_third_derivative regularity r i p hi).filter_mono nhdsWithin_le_nhds,
      (A.third_derivative_factor r ho hn i p hi).filter_mono nhdsWithin_le_nhds] with y hy hdy
    change -A.horizontalPartial r i p y / A.normalPartial r i p y = _
    rw [hy, hdy]
    have he : 1 - (n : ℤ) = -((n - 1 : ℕ) : ℤ) := by omega
    rw [he, zpow_neg, zpow_natCast]
    dsimp only [h, derivativeUnit]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

 theorem verticalSplitting_meromorphic (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (r : D.Retraction U) (ho : A.HasThirdOrder r) (hn : 0 < n)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) : MeromorphicAt (A.verticalSplitting r i p) 0 := by
  exact (A.horizontalPartial_analytic regularity r i p hi).neg.meromorphicAt.div
    (A.normalPartial_analytic regularity r i p hi).meromorphicAt

 theorem verticalSplitting_pole_leading (L : LaurentCalculus)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (r : D.Retraction U) (ho : A.HasThirdOrder r) (hn : 0 < n)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    CyclicLaurent.PoleBound n (L.coeff (A.verticalSplitting r i p)) ∧
      L.coeff (A.verticalSplitting r i p) (1 - (n : ℤ)) =
        -(1 / ((n : ℂ) * A.leading r ho i p)) := by
  obtain ⟨h, hh, hh0, hfactor⟩ := A.verticalSplitting_factor regularity r ho hn i p hi
  rw [L.congr hfactor]
  exact ⟨fun k hk => L.below h _ k hh hk, (L.leading h _ hh).trans hh0⟩

/-- The second actual retraction has exactly the pure monomial coefficient. -/
 theorem second_verticalSplitting_germ (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (hn : 0 < n) (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    A.verticalSplitting r₂ i p =ᶠ[𝓝[≠] 0]
      fun y => -(1 / (n : ℂ)) * y ^ (1 - (n : ℤ)) := by
  have hF : A.coordinate r₂ i p =ᶠ[𝓝 ((chartAt ℂ i) p, (0 : ℂ))]
      fun w : ℂ × ℂ => w.1 + w.2 ^ n := by
    have ht : ((chartAt ℂ i) p, (0 : ℂ)) ∈ (A.chart i p).coordinates.target := by
      rw [← A.centre i p hi]
      exact (A.chart i p).coordinates.map_source (A.source_mem i p hi)
    filter_upwards [(A.chart i p).coordinates.open_target.mem_nhds ht] with w hw
    change (chartAt ℂ i) (r₂.toFun ((A.chart i p).coordinates.symm w)) = _
    rw [(A.chart i p).s_normal _ ((A.chart i p).coordinates.map_target hw),
      (A.chart i p).coordinates.right_inv hw]
  have hd := hF.fderiv (𝕜 := ℂ)
  have ht : Tendsto (fun y : ℂ => ((chartAt ℂ i) p, y)) (𝓝 0)
      (𝓝 ((chartAt ℂ i) p, (0 : ℂ))) := (continuousAt_const.prodMk continuousAt_id).tendsto
  have hdline : ∀ᶠ y in 𝓝 (0 : ℂ),
      fderiv ℂ (A.coordinate r₂ i p) ((chartAt ℂ i) p, y) =
        fderiv ℂ (fun w : ℂ × ℂ => w.1 + w.2 ^ n) ((chartAt ℂ i) p, y) := ht hd
  filter_upwards [hdline.filter_mono nhdsWithin_le_nhds] with y hy
  have hder := ((hasFDerivAt_fst (𝕜 := ℂ) (p := ((chartAt ℂ i) p, y))).add
    ((hasFDerivAt_snd (𝕜 := ℂ) (p := ((chartAt ℂ i) p, y))).pow n)).fderiv
  change -fderiv ℂ (A.coordinate r₂ i p) ((chartAt ℂ i) p, y) (1, 0) /
    fderiv ℂ (A.coordinate r₂ i p) ((chartAt ℂ i) p, y) (0, 1) = _
  change fderiv ℂ (fun w : ℂ × ℂ => w.1 + w.2 ^ n) ((chartAt ℂ i) p, y) = _ at hder
  have hder' : fderiv ℂ (fun w : ℂ × ℂ => w.1 + w.2 ^ n) ((chartAt ℂ i) p, y) =
      (ContinuousLinearMap.fst ℂ ℂ ℂ) + ((n : ℂ) * y ^ (n - 1)) • ContinuousLinearMap.snd ℂ ℂ ℂ := by
    simpa only [nsmul_eq_mul] using hder
  rw [hy, hder']
  change -(1 + (n : ℂ) * y ^ (n - 1) * 0) / (0 + (n : ℂ) * y ^ (n - 1) * 1) = _
  simp only [mul_zero, add_zero, zero_add, mul_one]
  have he : 1 - (n : ℤ) = -((n - 1 : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

 theorem second_vertical_coefficients (L : LaurentCalculus)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity) (hn : 0 < n)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) (k : ℤ) :
    L.coeff (A.verticalSplitting r₂ i p) k =
      if k = 1 - (n : ℤ) then -(1 / (n : ℂ)) else 0 := by
  rw [L.congr (A.second_verticalSplitting_germ regularity hn i p hi)]
  exact L.monomial _ _ _

end Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas

namespace Paper27.Geometry.MeromorphicSplittingAverage

/-- The scalar coefficient of the actual finite differential rotation average. -/
def scalarAverage (n : ℕ) (ζ : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  (n : ℂ)⁻¹ • ∑ j ∈ range n, (fun y => ζ ^ j * f ((ζ ^ j)⁻¹ * y))

def scalarAffine (a : ℂ) (f g : ℂ → ℂ) : ℂ → ℂ :=
  (a - 1)⁻¹ • (a • g - f)

 theorem coefficient_scalarAverage (L : LaurentCalculus) {n : ℕ} {ζ : ℂ}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (f : ℂ → ℂ) (hf : MeromorphicAt f 0) :
    L.coeff (scalarAverage n ζ f) = CyclicLaurent.average n ζ (L.coeff f) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (Nat.ne_of_gt hn)
  funext k
  simp only [scalarAverage, map_smul, map_sum, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, CyclicLaurent.average, CyclicLaurent.pushforward]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [L.rotation f (ζ ^ j) hf (pow_ne_zero j hζ0)]
  congr 1
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  ring

 theorem coefficient_scalarAffine (L : LaurentCalculus) (a : ℂ) (f g : ℂ → ℂ) :
    L.coeff (scalarAffine a f g) = CyclicLaurent.affineCombination a (L.coeff f) (L.coeff g) := by
  funext k
  simp only [scalarAffine, map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    CyclicLaurent.affineCombination, div_eq_mul_inv, mul_comm]

 theorem meromorphic_scalarAverage (n : ℕ) (ζ : ℂ) (f : ℂ → ℂ) (hf : MeromorphicAt f 0) :
    MeromorphicAt (scalarAverage n ζ f) 0 := by
  have hterm (j : ℕ) : MeromorphicAt (fun y => ζ ^ j * f ((ζ ^ j)⁻¹ * y)) 0 := by
    have hlin : AnalyticAt ℂ (fun y : ℂ => (ζ ^ j)⁻¹ * y) 0 := analyticAt_const.mul analyticAt_id
    have hcomp := (show MeromorphicAt f ((fun y : ℂ => (ζ ^ j)⁻¹ * y) 0) from
      by simpa only [mul_zero] using hf).comp_analyticAt hlin
    exact (MeromorphicAt.const _ _).mul hcomp
  have hsum : ∀ s : Finset ℕ, MeromorphicAt (∑ j ∈ s, (fun y => ζ ^ j * f ((ζ ^ j)⁻¹ * y))) 0 := by
    intro s
    induction s using Finset.induction with
    | empty => simpa only [Finset.sum_empty] using MeromorphicAt.const (0 : ℂ) (0 : ℂ)
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact (hterm j).add ih
  exact (MeromorphicAt.const _ _).smul (hsum (range n))

 theorem meromorphic_scalarAffine (a : ℂ) {f g : ℂ → ℂ}
    (hf : MeromorphicAt f 0) (hg : MeromorphicAt g 0) : MeromorphicAt (scalarAffine a f g) 0 :=
  (MeromorphicAt.const _ _).smul (((MeromorphicAt.const _ _).smul hg).sub hf)

end Paper27.Geometry.MeromorphicSplittingAverage

namespace Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
open RetractionCoefficientHolomorphic MeromorphicSplittingAverage
variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ r₃ : D.Retraction U} {n : ℕ}
  (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)

/-- Formula (6) on the actual normal slice, using the computed actual quotients. -/
def localFormulaSix (r₃ : D.Retraction U) (ζ a : ℂ) (i p : D.curve) : ℂ → ℂ :=
  scalarAffine a (A.verticalSplitting r₂ i p) (scalarAverage n ζ (A.verticalSplitting r₃ i p))

 theorem localFormulaSix_tangent (L : LaurentCalculus)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃) (hn : 0 < n)
    {ζ a : ℂ} (hζ : IsPrimitiveRoot ζ n) (ha0 : a ≠ 0)
    (ha : ∀ i p, p ∈ D.curve.chartDomain i → A.leading r₃ ho i p = a)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    CyclicLaurent.TangentRegular (L.coeff (A.localFormulaSix r₃ ζ a i p)) := by
  rw [localFormulaSix, coefficient_scalarAffine,
    coefficient_scalarAverage L hn hζ _ (A.verticalSplitting_meromorphic regularity r₃ ho hn i p hi)]
  have hh := A.verticalSplitting_pole_leading L regularity r₃ ho hn i p hi
  rw [ha i p hi, mul_comm (n : ℂ) a] at hh
  exact CyclicLaurent.affine_average_tangent hn hζ ha0 _ _ hh.1
    (fun k hk => A.second_vertical_coefficients L regularity hn i p hi k) hh.2

/-- Pole cancellation in formula (6) gives a genuine analytic coefficient germ
vanishing at the embedded curve. The pole and leading hypotheses were proved
from the actual derivative quotients, rather than supplied to this theorem. -/
 theorem localFormulaSix_extension (L : LaurentCalculus)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃) (hn : 0 < n)
    {ζ a : ℂ} (hζ : IsPrimitiveRoot ζ n) (ha0 : a ≠ 0)
    (ha : ∀ i p, p ∈ D.curve.chartDomain i → A.leading r₃ ho i p = a)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h =ᶠ[𝓝[≠] 0] A.localFormulaSix r₃ ζ a i p ∧ h 0 = 0 := by
  have ht := A.localFormulaSix_tangent L regularity r₃ ho hn hζ ha0 ha i p hi
  have hm : MeromorphicAt (A.localFormulaSix r₃ ζ a i p) 0 :=
    meromorphic_scalarAffine a
      ((A.horizontalPartial_analytic regularity r₂ i p hi).neg.meromorphicAt.div
        (A.normalPartial_analytic regularity r₂ i p hi).meromorphicAt)
      (meromorphic_scalarAverage n ζ _ (A.verticalSplitting_meromorphic regularity r₃ ho hn i p hi))
  obtain ⟨h, hh, heq, hh0⟩ := L.removable _ hm (fun k hk => ht k (le_of_lt hk))
  exact ⟨h, hh, heq, hh0.trans (ht 0 le_rfl)⟩

end Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
