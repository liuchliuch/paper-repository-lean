import Paper26.OneCopySubmatrix
import Paper26.DensityProjection
import Mathlib.Probability.Independence.Integration

/-! The actual independent one-copy sample mean has the exact source
Frobenius expectation. Cross terms vanish by native product independence.
Projection onto actual density matrices preserves the expectation bound. -/
noncomputable section
open scoped BigOperators ComplexOrder ENNReal
open MeasureTheory ProbabilityTheory

namespace Paper26.OneCopyMeanVariance
open QuantumModel OneCopyObservation OneCopySubmatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

variable (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
  (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
  (hw : (Matrix.trace R).re ≤ 1)

def centeredSum (N : ℕ) (z : Fin N → Outcome ι) : Matrix ι ι ℂ :=
  ∑ i, sampleCentered R i z

include H hR hw

theorem cross_entry_independent {N : ℕ} (i j : Fin N) (hij : i ≠ j) (a b c e : ι) :
    IndepFun (fun z => sampleCentered R i z a b)
      (fun z => sampleCentered R j z c e) (sampleMeasure μ R N) := by
  have h := (sampleCentered_independent μ H R hR hw N).indepFun hij
  exact h.comp ((measurable_pi_apply b).comp (measurable_pi_apply a))
    ((measurable_pi_apply e).comp (measurable_pi_apply c))

theorem cross_product_entry_integrable {N : ℕ} (i j : Fin N) (a b : ι) :
    Integrable (fun z => (sampleCentered R i z * sampleCentered R j z) a b)
      (sampleMeasure μ R N) := by
  by_cases hij : i=j
  · subst j
    exact sample_square_entry_integrable μ H R hR hw i a b
  · simp_rw [Matrix.mul_apply]
    exact integrable_finset_sum Finset.univ fun c _ =>
      (cross_entry_independent μ H R hR hw i j hij a c c b).integrable_mul
        (sample_entry_integrable μ H R hR hw i a c)
        (sample_entry_integrable μ H R hR hw j c b)

theorem cross_product_entry_integral {N : ℕ} (i j : Fin N) (a b : ι) :
    (∫ z, (sampleCentered R i z * sampleCentered R j z) a b ∂sampleMeasure μ R N) =
      if i=j then varianceMatrix R a b else 0 := by
  by_cases hij : i=j
  · subst j
    simpa only [ite_true] using congrArg (fun M : Matrix ι ι ℂ => M a b)
      (sample_variance_eq μ H R hR hw i)
  · simp only [hij, ite_false, Matrix.mul_apply]
    have hh (c : ι) : Integrable (fun z => sampleCentered R i z a c * sampleCentered R j z c b)
        (sampleMeasure μ R N) :=
      (cross_entry_independent μ H R hR hw i j hij a c c b).integrable_mul
        (sample_entry_integrable μ H R hR hw i a c)
        (sample_entry_integrable μ H R hR hw j c b)
    rw [integral_finset_sum Finset.univ (fun c _ => hh c)]
    apply Finset.sum_eq_zero
    intro c _
    rw [(cross_entry_independent μ H R hR hw i j hij a c c b).integral_fun_mul_eq_mul_integral
      (sample_entry_integrable μ H R hR hw i a c).aestronglyMeasurable
      (sample_entry_integrable μ H R hR hw j c b).aestronglyMeasurable]
    have hi := congrArg (fun M : Matrix ι ι ℂ => M a c) (sample_mean_zero μ H R hR hw i)
    change (∫ z, sampleCentered R i z a c ∂sampleMeasure μ R N) = 0 at hi
    rw [hi, zero_mul]

theorem centeredSum_square_integrable (N : ℕ) (a b : ι) :
    Integrable (fun z => (centeredSum R N z * centeredSum R N z) a b)
      (sampleMeasure μ R N) := by
  simp_rw [centeredSum, Matrix.sum_mul, Matrix.mul_sum, Matrix.sum_apply]
  exact integrable_finset_sum Finset.univ fun i _ =>
    integrable_finset_sum Finset.univ fun j _ =>
      cross_product_entry_integrable μ H R hR hw i j a b

theorem centeredSum_second_moment (N : ℕ) :
    matrixExpectation (sampleMeasure μ R N)
      (fun z => centeredSum R N z * centeredSum R N z) = (N : ℂ) • varianceMatrix R := by
  ext a b
  change (∫ z, (centeredSum R N z * centeredSum R N z) a b ∂sampleMeasure μ R N) = _
  simp_rw [centeredSum, Matrix.sum_mul, Matrix.mul_sum, Matrix.sum_apply]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ fun j _ =>
      cross_product_entry_integrable μ H R hR hw i j a b)]
  simp_rw [integral_finset_sum Finset.univ (fun j _ =>
    cross_product_entry_integrable μ H R hR hw _ j a b),
    cross_product_entry_integral μ H R hR hw]
  simp

omit H hw in
theorem centeredSum_hermitian (N : ℕ) (z : Fin N → Outcome ι) :
    (centeredSum R N z).IsHermitian :=
  hermitian_sum _ fun i => (observation_hermitian (z i)).sub hR.isHermitian

theorem centeredSum_frobenius_integrable (N : ℕ) :
    Integrable (fun z => ShellAccounting.frobeniusSq (centeredSum R N z))
      (sampleMeasure μ R N) := by
  have he (z : Fin N → Outcome ι) : ShellAccounting.frobeniusSq (centeredSum R N z) =
      (Matrix.trace (centeredSum R N z * centeredSum R N z)).re := by
    rw [ShellAccounting.frobeniusSq_eq_trace, (centeredSum_hermitian R hR N z).eq]
  simp only [he, Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  exact integrable_finset_sum Finset.univ fun a _ =>
    (centeredSum_square_integrable μ H R hR hw N a a).re

theorem centeredSum_frobenius_integral (N : ℕ) :
    (∫ z, ShellAccounting.frobeniusSq (centeredSum R N z) ∂sampleMeasure μ R N) =
      (N : ℝ) * (Matrix.trace (varianceMatrix R)).re := by
  have he (z : Fin N → Outcome ι) : ShellAccounting.frobeniusSq (centeredSum R N z) =
      (Matrix.trace (centeredSum R N z * centeredSum R N z)).re := by
    rw [ShellAccounting.frobeniusSq_eq_trace, (centeredSum_hermitian R hR N z).eq]
  simp only [he, Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  have hh (a : ι) : Integrable (fun z => ((centeredSum R N z * centeredSum R N z) a a).re)
      (sampleMeasure μ R N) := by
    simpa only [RCLike.re_eq_complex_re] using
      (centeredSum_square_integrable μ H R hR hw N a a).re
  rw [integral_finset_sum Finset.univ (fun a _ => hh a)]
  have hi := centeredSum_second_moment μ H R hR hw N
  have heval (a : ι) : (∫ z, (centeredSum R N z * centeredSum R N z) a a
      ∂sampleMeasure μ R N) = (N : ℂ) * varianceMatrix R a a := by
    simpa only [matrixExpectation, Matrix.smul_apply, smul_eq_mul] using
      congrArg (fun M : Matrix ι ι ℂ => M a a) hi
  have hp (a : ι) : (∫ z, ((centeredSum R N z * centeredSum R N z) a a).re
      ∂sampleMeasure μ R N) = (N : ℝ) * (varianceMatrix R a a).re := by
    calc
      _ = ((∫ z, (centeredSum R N z * centeredSum R N z) a a ∂sampleMeasure μ R N)).re := by
        simpa only [RCLike.re_eq_complex_re] using
          integral_re (centeredSum_square_integrable μ H R hR hw N a a)
      _ = _ := by
        rw [heval a]
        simp
  simp_rw [hp]
  rw [Finset.mul_sum]

omit H hR hw in
theorem average_error_scale (N : ℕ) (hN : 0 < N) (z : Fin N → Outcome ι) :
    ShellAccounting.frobeniusSq (sampleAverage N z-R) =
      ((N : ℝ)^2)⁻¹ * ShellAccounting.frobeniusSq (centeredSum R N z) := by
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have he : sampleAverage N z-R = (N : ℂ)⁻¹ • centeredSum R N z := by
    rw [centeredSum, sample_sum_centered_eq N hN R z, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [he]
  simp only [ShellAccounting.frobeniusSq, Matrix.smul_apply, smul_eq_mul, norm_mul,
    norm_inv, Complex.norm_natCast, mul_pow, inv_pow, ← Finset.mul_sum]

theorem average_error_integrable (N : ℕ) (hN : 0 < N) :
    Integrable (fun z => ShellAccounting.frobeniusSq (sampleAverage N z-R)) (sampleMeasure μ R N) := by
  simp_rw [average_error_scale R N hN]
  exact (centeredSum_frobenius_integrable μ H R hR hw N).const_mul _

theorem average_error_integral (N : ℕ) (hN : 0 < N) :
    (∫ z, ShellAccounting.frobeniusSq (sampleAverage N z-R) ∂sampleMeasure μ R N) =
      (Matrix.trace (varianceMatrix R)).re / (N : ℝ) := by
  simp_rw [average_error_scale R N hN]
  rw [integral_const_mul, centeredSum_frobenius_integral μ H R hR hw]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  field_simp

omit hR hw in
theorem equation_54 (ρ : Density ι) (N : ℕ) (hN : 0 < N) :
    (∫ z, ShellAccounting.frobeniusSq (sampleAverage N z-ρ.matrix)
      ∂sampleMeasure μ ρ.matrix N) =
      ((Fintype.card ι : ℝ)^2+Fintype.card ι-1-(Matrix.trace (ρ.matrix*ρ.matrix)).re)/(N : ℝ) := by
  rw [average_error_integral μ H ρ.matrix ρ.positive (by simp [ρ.trace_one]) N hN]
  congr 1
  simp [varianceMatrix, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, ρ.trace_one]
  ring

end Paper26.OneCopyMeanVariance
