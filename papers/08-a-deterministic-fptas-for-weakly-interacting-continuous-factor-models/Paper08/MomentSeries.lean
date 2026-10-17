import Paper08.ZeroFree
import Paper08.Analytic
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Actual integral moments and the analytic series of the partition function

The coefficient is the normalized raw integral moment in (2.13), with
no coefficient-identification hypothesis. Mathlib's complex MGF derivative
theorem applies because the original log factors are continuous on a compact cube.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal
open Set Metric MeasureTheory

namespace Paper08.MomentSeries
open Integral

/-- The normalized moment `M_j(B) = E[(sum ell)^j]/j!`. -/
def moment {n r : ℕ} {ι : Type*} (E : ι → Factor n r) (B : Finset ι) (j : ℕ) : ℂ :=
  (∫ x in cube n, (ZeroFree.sumEll E B x : ℂ) ^ j) / (j.factorial : ℂ)

@[simp] theorem moment_zero {n r : ℕ} {ι : Type*} (E : ι → Factor n r) (B : Finset ι) :
    moment E B 0 = 1 := by
  simp [moment, Measure.real, volume_cube]

/-- Every exponential moment of the actual log-factor sum is integrable. -/
theorem integrableExpSet_sumEll {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K : ℝ} (hE : ∀ i ∈ B, (E i).RangeOk q)
    (hLip : ∀ i ∈ B, (E i).LipOk K) :
    ProbabilityTheory.integrableExpSet (ZeroFree.sumEll E B) (volume.restrict (cube n)) = univ := by
  apply Set.eq_univ_of_forall
  intro t
  exact (Real.continuous_exp.comp_continuousOn
    (continuousOn_const.mul (ZeroFree.continuousOn_sumEll E B hE hLip))).integrableOn_compact
      (ZeroFree.isCompact_cube n)

/-- The derivative of every order at zero is the corresponding actual raw moment. -/
theorem iteratedDeriv_Q_zero {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K : ℝ} (hE : ∀ i ∈ B, (E i).RangeOk q)
    (hLip : ∀ i ∈ B, (E i).LipOk K) (j : ℕ) :
    iteratedDeriv j (ZeroFree.Q E B) 0 = ∫ x in cube n, (ZeroFree.sumEll E B x : ℂ) ^ j := by
  have hz : (0 : ℂ).re ∈ interior
      (ProbabilityTheory.integrableExpSet (ZeroFree.sumEll E B) (volume.restrict (cube n))) := by
    rw [integrableExpSet_sumEll E B hE hLip, interior_univ]
    trivial
  simpa [ZeroFree.Q, ProbabilityTheory.complexMGF] using
    ProbabilityTheory.iteratedDeriv_complexMGF hz j

/-- The actual partition function has exactly the integral-moment series. -/
theorem hasFPowerSeriesAt_Q {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K : ℝ} (hq : 0 ≤ q)
    (hE : ∀ i ∈ B, (E i).RangeOk q) (hLip : ∀ i ∈ B, (E i).LipOk K) :
    HasFPowerSeriesAt (ZeroFree.Q E B) (FormalMultilinearSeries.ofScalars ℂ (moment E B)) 0 := by
  have h := (ZeroFree.analyticAt_Q E B hq hE hLip 0).hasFPowerSeriesAt
  have heq : (fun j => iteratedDeriv j (ZeroFree.Q E B) 0 / (j.factorial : ℂ)) = moment E B := by
    funext j
    rw [iteratedDeriv_Q_zero E B hE hLip j]
    rfl
  simpa only [heq] using h

/-- Cauchy integral coefficient extraction gives precisely the actual moment. -/
theorem cauchyCoeff_Q_eq_moment {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hE : ∀ i ∈ B, (E i).RangeOk q) (hLip : ∀ i ∈ B, (E i).LipOk K) (j : ℕ) :
    Analytic.cauchyCoeff (ZeroFree.Q E B) R j = moment E B j := by
  lift R to ℝ≥0 using hR.le
  have hc := ((ZeroFree.differentiable_Q E B hq hE hLip).differentiableOn.hasFPowerSeriesOnBall
    (c := (0 : ℂ)) hR).hasFPowerSeriesAt
  have heq := hc.eq_formalMultilinearSeries (hasFPowerSeriesAt_Q E B hq hE hLip)
  exact congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff j) heq |>.trans
    (FormalMultilinearSeries.coeff_ofScalars)

/-- The same normalized raw moment in the real scalar field. -/
def realMoment {n r : ℕ} {ι : Type*} (E : ι → Factor n r) (B : Finset ι) (j : ℕ) : ℝ :=
  cubeIntegral (fun x => ZeroFree.sumEll E B x ^ j) / (j.factorial : ℝ)

/-- Coercing the real integral moment gives the complex analytic coefficient. -/
theorem ofReal_realMoment {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) (j : ℕ) : (realMoment E B j : ℂ) = moment E B j := by
  unfold realMoment moment cubeIntegral
  rw [Complex.ofReal_div]
  congr 1
  · simp_rw [← Complex.ofReal_pow]
    exact (integral_ofReal (𝕜 := ℂ)).symm

@[simp] theorem realMoment_zero {n r : ℕ} {ι : Type*} (E : ι → Factor n r) (B : Finset ι) :
    realMoment E B 0 = 1 := by simp [realMoment]


end Paper08.MomentSeries
