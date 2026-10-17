import Paper10.WickSix
import Paper10.CubicAlgebra

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
namespace Paper10
set_option maxHeartbeats 0
set_option maxRecDepth 4096
variable {q m : ℕ}

/-- Cubic trace expansion, with all matrix factor orders retained. -/
theorem trace_gaussianMatrix_cube (B : Fin m → Matrix (Fin q) (Fin q) ℝ) (ω : Fin m → ℝ) :
    Matrix.trace (gaussianMatrix B ω ^ 3) =
      ∑ a, ∑ b, ∑ c, (ω a * ω b * ω c) * Matrix.trace (B a * B b * B c) := by
  have he : gaussianMatrix B ω ^ 3 =
      ∑ a, ∑ b, ∑ c, (ω a * ω b * ω c) • (B a * B b * B c) := by
    rw [show gaussianMatrix B ω ^ 3 = gaussianMatrix B ω * gaussianMatrix B ω * gaussianMatrix B ω by simp [pow_succ]]
    unfold gaussianMatrix
    simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [sum_three_reverse]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    congr 1 <;> ring
  rw [he]
  simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

/-- Square of the cubic trace as a finite degree-six polynomial. -/
theorem trace_gaussianMatrix_cube_sq (B : Fin m → Matrix (Fin q) (Fin q) ℝ) (ω : Fin m → ℝ) :
    (Matrix.trace (gaussianMatrix B ω ^ 3)) ^ 2 =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, (ω a * ω b * ω c * ω d * ω e * ω f) *
        (Matrix.trace (B a * B b * B c) * Matrix.trace (B d * B e * B f)) := by
  rw [trace_gaussianMatrix_cube, pow_two]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  ring

/-- Square integrability of the cubic trace. -/
theorem integrable_trace_gaussianMatrix_cube_sq (B : Fin m → Matrix (Fin q) (Fin q) ℝ) :
    Integrable (fun ω => Matrix.trace (gaussianMatrix B ω ^ 3) ^ 2) (stdGaussianMeasure m) := by
  simp_rw [trace_gaussianMatrix_cube_sq]
  exact integrable_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ =>
    integrable_finset_sum _ (fun c _ => integrable_finset_sum _ (fun d _ =>
      integrable_finset_sum _ (fun e _ => integrable_finset_sum _ (fun f _ =>
        (integrable_wick_six a b c d e f).mul_const _))))))

/-- Exact sixth-moment contraction formula for the symmetric cubic matrix trace. -/
theorem cubic_moment_expansion (B : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hB : ∀ a, (B a).IsSymm) :
    (∫ ω, Matrix.trace (gaussianMatrix B ω ^ 3) ^ 2 ∂stdGaussianMeasure m) =
      6 * (∑ a, ∑ b, ∑ c, Matrix.trace (B a * B b * B c) ^ 2) +
      9 * (∑ a, (Matrix.trace (B a * ∑ b, B b * B b)) ^ 2) := by
  simp_rw [trace_gaussianMatrix_cube_sq]
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ =>
    integrable_finset_sum _ (fun c _ => integrable_finset_sum _ (fun d _ =>
      integrable_finset_sum _ (fun e _ => integrable_finset_sum _ (fun f _ =>
        (integrable_wick_six a b c d e f).mul_const _))))))]
  simp_rw [integral_finset_sum _ (fun b _ => integrable_finset_sum _ (fun c _ =>
    integrable_finset_sum _ (fun d _ => integrable_finset_sum _ (fun e _ =>
      integrable_finset_sum _ (fun f _ => (integrable_wick_six _ b c d e f).mul_const _)))))]
  simp_rw [integral_finset_sum _ (fun c _ => integrable_finset_sum _ (fun d _ =>
    integrable_finset_sum _ (fun e _ => integrable_finset_sum _ (fun f _ =>
      (integrable_wick_six _ _ c d e f).mul_const _))))]
  simp_rw [integral_finset_sum _ (fun d _ => integrable_finset_sum _ (fun e _ =>
    integrable_finset_sum _ (fun f _ => (integrable_wick_six _ _ _ d e f).mul_const _)))]
  simp_rw [integral_finset_sum _ (fun e _ => integrable_finset_sum _ (fun f _ =>
    (integrable_wick_six _ _ _ _ e f).mul_const _))]
  simp_rw [integral_finset_sum _ (fun f _ => (integrable_wick_six _ _ _ _ _ f).mul_const _)]
  simp_rw (config := { maxSteps := 2000000 }) [integral_mul_const, wick_six, delta, add_mul, Finset.sum_add_distrib]
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have hswap23 : ∀ a b c, Matrix.trace (B a * B b * B c) = Matrix.trace (B a * B c * B b) :=
    fun a b c => trace_triple_swap (hB a) (hB b) (hB c)
  have hswap12 : ∀ a b c, Matrix.trace (B a * B b * B c) = Matrix.trace (B b * B a * B c) := by
    intro a b c
    calc
      _ = Matrix.trace (B a * B c * B b) := hswap23 a b c
      _ = _ := Matrix.trace_mul_cycle _ _ _
  have hj : (∑ a, ∑ b, ∑ c,
      Matrix.trace (B a * B a * B b) * Matrix.trace (B b * B c * B c)) =
      ∑ a, (Matrix.trace (B a * ∑ b, B b * B b)) ^ 2 := by
    rw [Finset.sum_comm]
    have hrep : ∀ a b, Matrix.trace (B b * B b * B a) = Matrix.trace (B a * B b * B b) :=
      fun a b => Matrix.trace_mul_cycle _ _ _
    simp_rw [hrep]
    simp only [Matrix.mul_sum, Matrix.trace_sum, ← Matrix.mul_assoc, pow_two,
      Finset.sum_mul, Finset.mul_sum]
    simp only [mul_comm]
  have hk : (∑ a, ∑ b, ∑ c,
      Matrix.trace (B a * B b * B b) * Matrix.trace (B a * B c * B c)) =
      ∑ a, (Matrix.trace (B a * ∑ b, B b * B b)) ^ 2 := by
    simp only [Matrix.mul_sum, Matrix.trace_sum, ← Matrix.mul_assoc, pow_two,
      Finset.sum_mul, Finset.mul_sum]
    simp only [mul_comm]
  simp only [hswap12, hswap23] at hj hk ⊢
  rw [hj, hk]
  simp only [pow_two]
  ring

/-- Proposition 2.4: the actual cubic trace second moment, uniformly over covariance contractions.
The direct Wick proof gives the slightly stronger constant 15 in place of 27. -/
theorem prop_2_4_cubic (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) (σ : Fin m → ℝ) (hσ : ∀ a, 0 ≤ σ a ∧ σ a ≤ 1) :
    (∫ ω, Matrix.trace (gaussianMatrix (fun a => σ a • F a) ω ^ 3) ^ 2
      ∂stdGaussianMeasure m) ≤ 27 * (n q : ℝ) * c q := by
  let B := fun a => σ a • F a
  have hB : ∀ a, (B a).IsSymm := fun a => (hF.1 a).smul (σ a)
  have htensor := cubic_tensor_le F hF σ hσ
  have hcontract := cubic_contraction_le F hF σ hσ
  have hc : (c q • oneMat q).PosSemidef := Matrix.PosSemidef.one.smul (c_pos q).le
  have hsum := trace_sq_mono (sum_sq_posSemidef B hB) hc
    (gaussian_coeff_square_bound F hF σ hσ)
  have he : Matrix.trace ((c q • oneMat q) * (c q • oneMat q)) = (n q : ℝ) * c q := by
    simp only [oneMat, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      smul_smul, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    rw [n_mul_c]
    ring
  rw [he] at hsum
  have hn : 0 ≤ (n q : ℝ) * c q := mul_nonneg (Nat.cast_nonneg _) (c_pos q).le
  rw [cubic_moment_expansion _ hB]
  change (6 * (∑ a, ∑ b, ∑ c, Matrix.trace (B a * B b * B c) ^ 2) +
    9 * (∑ a, (Matrix.trace (B a * ∑ b, B b * B b)) ^ 2)) ≤ _
  linarith

end Paper10
