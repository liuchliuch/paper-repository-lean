import Paper10.Main
import Paper10.CubicMoment
import Paper10.MetricBridge

noncomputable section
open Matrix MeasureTheory
namespace Paper10
variable {q m : ℕ}
instance stdGaussianMeasure_isProbability (m : ℕ) : IsProbabilityMeasure (stdGaussianMeasure m) := by
  unfold stdGaussianMeasure
  infer_instance

/-- The uniform radius enforces the normalized time interval used in feasibility. -/
theorem tOf_bounds (hq : 0 < q) {s ε r : ℝ} (hs : c q ≤ s)
    (hε : 0 < ε) (hε1 : ε < 1) (hr : 0 < r) (hr1 : r ≤ rEps ε) :
    0 < tOf (q := q) r s ∧ tOf (q := q) r s ≤ 1 := by
  have hn : (1 : ℝ) ≤ n q := by exact_mod_cast n_pos hq
  have hs1 : 1 ≤ s := (one_le_c hq).trans hs
  have hnsp : 1 ≤ (n q : ℝ) * s := by nlinarith
  have hsqrt : 1 ≤ Real.sqrt ((n q : ℝ) * s) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (n q : ℝ) * s by positivity), Real.sqrt_nonneg ((n q : ℝ) * s)]
  have hradeps : rEps ε < 1 := by
    have hc := rEps_sq hε
    have he3 : ε ^ 3 ≤ 1 := pow_le_one₀ hε.le hε1.le
    have hp := rEps_pos hε
    nlinarith
  have hsqrtp : 0 < Real.sqrt ((n q : ℝ) * s) := by linarith
  refine ⟨div_pos hr hsqrtp, ?_⟩
  have ht : tOf (q := q) r s ≤ r := by
    unfold tOf
    rw [div_le_iff₀ hsqrtp]
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hsqrt)]
  linarith

/-- Scaling relation in (21). -/
theorem tOf_scale (hq : 0 < q) {s : ℝ} (hs : c q ≤ s) (r : ℝ) :
    s * (tOf (q := q) r s) ^ 2 = r ^ 2 / (n q : ℝ) := by
  have hn : (0 : ℝ) < n q := Nat.cast_pos.mpr (n_pos hq)
  have hs0 := lt_of_lt_of_le (c_pos q) hs
  unfold tOf
  rw [div_pow, Real.sq_sqrt (show 0 ≤ (n q : ℝ) * s by positivity)]
  field_simp

/-- A symmetric Gaussian coefficient family produces symmetric sample matrices. -/
theorem gaussianMatrix_isSymm (B : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hB : ∀ a, (B a).IsSymm) (ω : Fin m → ℝ) : (gaussianMatrix B ω).IsSymm := by
  unfold Matrix.IsSymm gaussianMatrix
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.transpose_smul, show (B a)ᵀ = B a from hB a]

/-- Uniform two-sided local-norm guarantee for every normalized Gaussian covariance contraction.
This has the actual endpoint and actual log-determinant local norms, at every invertible
base-point factor. The auxiliary-precision spectral construction is connected separately. -/
theorem sasc_of_covariance_eigenmodes (hq : 0 < q)
    (F : Fin m → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F)
    (σ : Fin m → ℝ) (hσ : ∀ a, 0 ≤ σ a ∧ σ a ≤ 1)
    (R : Matrix (Fin q) (Fin q) ℝ) (hR : IsUnit R)
    {s ε r : ℝ} (hs : c q ≤ s) (hε : 0 < ε) (hε1 : ε < 1)
    (hr : 0 < r) (hr1 : r ≤ rEps ε) :
    let X := R * Rᴴ
    let H := fun ω => R * ((tOf (q := q) r s) •
      gaussianMatrix (fun a => σ a • F a) ω) * Rᴴ
    1 - ε ≤ (stdGaussianMeasure m).real {ω |
      sascEventTwoSided s X (X + H ω) (H ω) ε r} := by
  let B := fun a => σ a • F a
  let A := gaussianMatrix B
  let t := tOf (q := q) r s
  let X := R * Rᴴ
  let H := fun ω => R * (t • A ω) * Rᴴ
  have hB : ∀ a, (B a).IsSymm := fun a => (hF.1 a).smul (σ a)
  have hA : ∀ ω, (A ω).IsSymm := gaussianMatrix_isSymm B hB
  have ht := tOf_bounds hq hs hε hε1 hr hr1
  let C := fun ω => Matrix.trace (A ω ^ 3)
  let Q := fun ω => Matrix.trace (A ω ^ 4)
  have hC : Measurable C := by dsimp [C, A]; simp_rw [trace_gaussianMatrix_cube]; fun_prop
  have hQ : Measurable Q := by dsimp [Q, A]; simp_rw [trace_gaussianMatrix_four]; fun_prop
  have hQ0 : ∀ ω, 0 ≤ Q ω := by
    intro ω
    dsimp [Q]
    rw [trace_pow_spectral (A ω) (hA ω) 4]
    apply Finset.sum_nonneg
    intro i _
    positivity
  have hm3 : t ^ 2 * (∫ ω, C ω ^ 2 ∂stdGaussianMeasure m) ≤ 27 * r ^ 2 :=
    eq_18_scale hq r s _ 27 hs (by norm_num) (prop_2_4_cubic F hF σ hσ)
  have hm4 : t ^ 2 * (∫ ω, Q ω ∂stdGaussianMeasure m) ≤ 3 * r ^ 2 :=
    eq_18_scale hq r s _ 3 hs (by norm_num) (prop_2_4_quartic F hF σ hσ)
  have hp := concentration_from_moments C Q hC hQ
    (integrable_trace_gaussianMatrix_cube_sq B) (integrable_trace_gaussianMatrix_four B)
    hQ0 ht.1 hε hε1 hr hr1 hm3 hm4
  apply hp.trans
  apply measureReal_mono _ (by finiteness)
  intro ω hω
  have hg := normalized_good_event (A ω) (hA ω) ht.1 ht.2 hε hε1.le hω.1 hω.2
  change (X + H ω).PosDef ∧ |localNormSq s (X + H ω) (H ω) - localNormSq s X (H ω)| ≤ _
  constructor
  · have hz : X + H ω = R * (1 + t • A ω) * Rᴴ := by
      dsimp [X, H]
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    rw [hz]
    exact hg.1.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hR)
  · change |localNormSq s (R * Rᴴ + R * (t • A ω) * Rᴴ) (R * (t • A ω) * Rᴴ) -
      localNormSq s (R * Rᴴ) (R * (t • A ω) * Rᴴ)| ≤ _
    rw [metric_change_congruence R (A ω) hR s t, abs_mul,
      abs_of_nonneg (show 0 ≤ s * t ^ 2 by have := (one_le_c hq).trans hs; positivity)]
    calc
      _ ≤ (s * t ^ 2) * (2 * ε) := mul_le_mul_of_nonneg_left hg.2 (by have := (one_le_c hq).trans hs; positivity)
      _ = _ := by rw [show s * t ^ 2 = r ^ 2 / (n q : ℝ) from tOf_scale hq hs r]; ring

end Paper10
