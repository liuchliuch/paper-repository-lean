import Paper10.Poincare
import Paper10.CubicMoment
import Paper10.MetricCalculus
import Paper10.SASCProof

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace Paper10
variable {q m : ℕ}
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-- The cubic matrix trace is an actual multivariate polynomial. -/
def cubicTracePolynomial (B : Fin m → Matrix (Fin q) (Fin q) ℝ) : MvPolynomial (Fin m) ℝ :=
  ∑ a, ∑ b, ∑ c, MvPolynomial.C (Matrix.trace (B a * B b * B c)) *
    MvPolynomial.X a * MvPolynomial.X b * MvPolynomial.X c

theorem cubicTracePolynomial_eval (B : Fin m → Matrix (Fin q) (Fin q) ℝ) (ω : Fin m → ℝ) :
    MvPolynomial.eval ω (cubicTracePolynomial B) = Matrix.trace (gaussianMatrix B ω ^ 3) := by
  rw [trace_gaussianMatrix_cube]
  simp only [cubicTracePolynomial, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- A Gaussian coordinate change differentiates the actual matrix sample in the stated direction. -/
theorem hasDerivAt_gaussianMatrix_update (B : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (i : Fin m) (ω : Fin m → ℝ) :
    HasDerivAt (fun t : ℝ => gaussianMatrix B (Function.update ω i t)) (B i) (ω i) := by
  classical
  have hc (a : Fin m) : HasDerivAt (fun t : ℝ => (Function.update ω i t) a • B a)
      (if a = i then B a else 0) (ω i) := by
    by_cases hai : a = i
    · subst a
      simpa using (hasDerivAt_id (ω i)).smul_const (B i)
    · simpa only [Function.update_of_ne hai, if_neg hai] using
        hasDerivAt_const (ω i) (ω a • B a)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ => hc a)
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true, gaussianMatrix] using hs

/-- Equation (15): the actual coordinate derivative is 3 Tr(A² Bᵢ). -/
theorem cubic_trace_partial (B : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (i : Fin m) (ω : Fin m → ℝ) :
    Hermite.coordinateDerivative (fun η => Matrix.trace (gaussianMatrix B η ^ 3)) ω i =
      3 * frob (B i) (gaussianMatrix B ω ^ 2) := by
  have hc := hasDerivAt_gaussianMatrix_update B i ω
  have hm := (hc.mul hc).mul hc
  let tr : Matrix (Fin q) (Fin q) ℝ →L[ℝ] ℝ :=
    (Matrix.traceLinearMap (Fin q) ℝ ℝ).toContinuousLinearMap
  have ht := tr.hasFDerivAt.comp_hasDerivAt (ω i) hm
  have he : Function.update ω i (ω i) = ω := Function.update_eq_self i ω
  simp only [Pi.mul_apply, he] at ht
  have hd : HasDerivAt (fun t : ℝ => Matrix.trace (gaussianMatrix B (Function.update ω i t) ^ 3))
      (3 * frob (B i) (gaussianMatrix B ω ^ 2)) (ω i) := by
    convert ht using 1
    · funext t
      simp [tr, pow_succ]
    · change 3 * frob (B i) (gaussianMatrix B ω ^ 2) =
        Matrix.trace ((B i * gaussianMatrix B ω + gaussianMatrix B ω * B i) * gaussianMatrix B ω +
          gaussianMatrix B ω * gaussianMatrix B ω * B i)
      simp only [Matrix.add_mul, Matrix.trace_add, frob, pow_two]
      rw [Matrix.trace_mul_cycle (gaussianMatrix B ω) (gaussianMatrix B ω) (B i),
        Matrix.trace_mul_cycle (gaussianMatrix B ω) (B i) (gaussianMatrix B ω),
        Matrix.trace_mul_cycle (gaussianMatrix B ω) (gaussianMatrix B ω) (B i)]
      simp only [Matrix.mul_assoc]
      ring
  exact hd.deriv

/-- The standard Gaussian vector is invariant under global sign reversal. -/
theorem stdGaussianMeasure_neg (m : ℕ) :
    MeasurePreserving (fun ω : Fin m → ℝ => -ω) (stdGaussianMeasure m) (stdGaussianMeasure m) := by
  have hn : MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_neg, by simpa using (gaussianReal_map_neg (μ := 0) (v := 1))⟩
  exact measurePreserving_pi (fun _ : Fin m => gaussianReal 0 1) (fun _ : Fin m => gaussianReal 0 1)
    (fun _ => hn)

/-- The cubic trace has actual mean zero, including singular Gaussian covariances. -/
theorem cubic_trace_mean (B : Fin m → Matrix (Fin q) (Fin q) ℝ) :
    (∫ ω, Matrix.trace (gaussianMatrix B ω ^ 3) ∂stdGaussianMeasure m) = 0 := by
  have hn : ∀ ω, gaussianMatrix B (-ω) = -gaussianMatrix B ω := by
    intro ω
    simp [gaussianMatrix, ← Finset.sum_neg_distrib]
  have hh := (stdGaussianMeasure_neg m).integral_comp (Homeomorph.neg (Fin m → ℝ)).measurableEmbedding
    (fun ω => Matrix.trace (gaussianMatrix B ω ^ 3))
  simp only [hn, Odd.neg_pow (by decide : Odd (3 : ℕ)), Matrix.trace_neg, integral_neg] at hh
  linarith

/-- The variance-to-quartic bound in equation (15), with the exact coefficient 9. -/
theorem cubic_variance_le_quartic (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) (σ : Fin m → ℝ) (hσ : ∀ a, 0 ≤ σ a ∧ σ a ≤ 1) :
    (∫ ω, Matrix.trace (gaussianMatrix (fun a => σ a • F a) ω ^ 3) ^ 2 ∂stdGaussianMeasure m) ≤
      9 * (∫ ω, Matrix.trace (gaussianMatrix (fun a => σ a • F a) ω ^ 4) ∂stdGaussianMeasure m) := by
  let B := fun a => σ a • F a
  have hp := Hermite.gaussian_poincare_poly (cubicTracePolynomial B)
  have hf : (fun ω => MvPolynomial.eval ω (cubicTracePolynomial B)) =
      fun ω => Matrix.trace (gaussianMatrix B ω ^ 3) := funext (cubicTracePolynomial_eval B)
  rw [hf, variance_of_integral_eq_zero (by simp_rw [trace_gaussianMatrix_cube]; fun_prop) (cubic_trace_mean B)] at hp
  apply hp.trans
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact ae_of_all _ (fun ω => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  · exact (integrable_trace_gaussianMatrix_four B).const_mul 9
  · apply ae_of_all
    intro ω
    simp_rw [cubic_trace_partial, mul_pow, ← Finset.mul_sum]
    have hB : ∀ a, (B a).IsSymm := fun a => (hF.1 a).smul (σ a)
    have hA := gaussianMatrix_isSymm B hB ω
    have hsquare : (gaussianMatrix B ω ^ 2).IsSymm := by
      unfold Matrix.IsSymm
      rw [Matrix.transpose_pow, hA]
    have hb := covariance_bessel F hF σ hσ (gaussianMatrix B ω ^ 2) hsquare
    have he : frobNormSq (gaussianMatrix B ω ^ 2) = Matrix.trace (gaussianMatrix B ω ^ 4) := by
      simp [frobNormSq, frob, ← pow_add]
    rw [he] at hb
    change 3 ^ 2 * (∑ i, frob (B i) (gaussianMatrix B ω ^ 2) ^ 2) ≤ _
    nlinarith

end Paper10
