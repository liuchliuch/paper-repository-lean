import Paper10

/-!
# Proofs of the separately reviewed paper statements

Does not import the challenge. Each declaration has the fixed interface of
`Verification/Challenge.lean` and is witnessed by a closed proof from the
mathematical library.
-/

noncomputable section

open Matrix MeasureTheory ProbabilityTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace Paper10.Challenge

/-- Lemma 2.3 first inequality (9). -/
theorem lemma_2_3_first {q : ℕ} {ι : Type*} [Fintype ι]
    (B : ι → Matrix (Fin q) (Fin q) ℝ)
    (hB : ∀ a, (B a).IsSymm) :
    ∑ a, ∑ b, |Matrix.trace (B a * B b * B a * B b)|
      ≤ Matrix.trace ((∑ a, B a * B a) * (∑ a, B a * B a)) :=
  Paper10.lemma_2_3_first B hB

/-- Lemma 2.3 second inequality (9). -/
theorem lemma_2_3_second {q : ℕ} {ι : Type*} [Fintype ι]
    (Bfn : ι → Matrix (Fin q) (Fin q) ℝ)
    (Ψ : Matrix (Fin q) (Fin q) ℝ)
    (hΨ : Ψ.PosSemidef)
    (hB : ∀ a, (Bfn a).IsSymm)
    (hle : (Ψ - ∑ a, Bfn a * Bfn a).PosSemidef) :
    Matrix.trace ((∑ a, Bfn a * Bfn a) * (∑ a, Bfn a * Bfn a))
      ≤ Matrix.trace (Ψ * Ψ) :=
  Paper10.lemma_2_3_second Bfn Ψ hΨ hB hle

/-- Lemma 3.1 scalar remainder identity. -/
theorem scalar_remainder_id (y : ℝ) (hy : |y| ≤ 1 / 2) :
    y ^ 2 * ((1 + y) ^ (-2 : ℤ) - 1)
      = -2 * y ^ 3 + y ^ 4 * (3 + 2 * y) / (1 + y) ^ 2 :=
  Paper10.scalar_remainder_id y hy

/-- Proposition 4.1 operator bound. -/
theorem prop_4_1_op_bound {q : ℕ} (K : Matrix (Fin q) (Fin q) ℝ) (hK : K.IsSymm) :
    (q + 2 : ℝ) * frobNormSq K + (Matrix.trace K) ^ 2
      ≤ 2 * (q + 1 : ℝ) * frobNormSq K :=
  Paper10.prop_4_1_op_bound K hK

/-- SSC threshold. -/
theorem ssc_threshold {q : ℕ} (s : ℝ) (hq : 0 < q) (hs : 0 < s) :
    (∀ K : Matrix (Fin q) (Fin q) ℝ, K.IsSymm →
      (q + 2 : ℝ) * frobNormSq K + (Matrix.trace K) ^ 2 ≤ 4 * s * frobNormSq K)
      ↔ c q ≤ s :=
  Paper10.ssc_threshold_iff q s hq hs

/-- Dimension estimate. -/
theorem n_c_le_q_cube {q : ℕ} (hq : 0 < q) :
    ((n q : ℕ) : ℝ) * c q ≤ (q : ℝ) ^ 3 :=
  Paper10.n_c_le_q_cube q hq

/-- Sum of squares identity (12). -/
theorem sum_squares_standard (q : ℕ) :
    (∑ i : Fin q, (eii i) * (eii i)) +
      (∑ p : {x : Fin q × Fin q // x.1 < x.2},
        (eijSymm p.val.1 p.val.2) * (eijSymm p.val.1 p.val.2))
      = (c q) • (oneMat q) :=
  Paper10.sum_squares_standard q

/-- Scalar coefficient bound. -/
theorem scalar_coeff_bound (y : ℝ) (hy : |y| ≤ 1 / 2) :
    0 ≤ (3 + 2 * y) / (1 + y) ^ 2 ∧ (3 + 2 * y) / (1 + y) ^ 2 ≤ 8 :=
  Paper10.scalar_coeff_bound y hy

/-- Fixed source-facing contract: main_two_sided. -/
theorem main_two_sided (q : ℕ) (hq : 0 < q) (X : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef)
    {s ε r : ℝ} (hs : c q ≤ s) (hε : 0 < ε) (hε1 : ε < 1) (hr : 0 < r) (hr1 : r ≤ rEps ε)
    (E : Matrix (Fin (n q)) (Fin (n q)) ℝ) (hE : E.PosSemidef) :
    let H := proposalStep (canonicalF q) (CFC.sqrt X) s r E (lt_of_lt_of_le (c_pos q) hs) hE
    1 - ε ≤ (stdGaussianMeasure (n q)).real {ω | sascEventTwoSided s X (X + H ω) (H ω) ε r} := 
  Paper10.Main.thm_1_3_two_sided q hq X hX hs hε hε1 hr hr1 E hE

/-- Fixed source-facing contract: main_sasc. -/
theorem main_sasc (q : ℕ) (hq : 0 < q) {s : ℝ} (hs : c q ≤ s) : SASC q s := 
  Paper10.Main.thm_1_3_sasc q hq hs

/-- Fixed source-facing contract: main_uniform. -/
theorem main_uniform : UniformSASC := 
  Paper10.Main.thm_1_3_uniform

/-- Fixed source-facing contract: main_ssc. -/
theorem main_ssc (q : ℕ) (hq : 0 < q) {s : ℝ} (hs : 0 < s) : SSC q s ↔ c q ≤ s := 
  Paper10.Main.thm_1_3_ssc q hq hs

/-- Fixed source-facing contract: main_min_scale. -/
theorem main_min_scale (q : ℕ) (hq : 0 < q) : IsLeast {s : ℝ | 0 < s ∧ SSC q s ∧ SASC q s} (c q) := 
  Paper10.Main.thm_1_3_min_scale q hq

/-- Fixed source-facing contract: covariance_contraction. -/
theorem covariance_contraction {d : ℕ} (T D : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T)
    (hD : D.PosSemidef) {s : ℝ} (hs : 0 < s) :
    let Q := s • (T * (s • (Tᴴ * T) + D)⁻¹ * Tᴴ)
    Q.PosSemidef ∧ ((1 : Matrix (Fin d) (Fin d) ℝ) - Q).PosSemidef := 
  Paper10.lemma_2_1_contraction T D hT hD hs

/-- Fixed source-facing contract: quartic_gaussian. -/
theorem quartic_gaussian {q m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F)
    (σ : Fin m → ℝ) (hσ : ∀ a, 0 ≤ σ a ∧ σ a ≤ 1) :
    (∫ ω, Matrix.trace (gaussianMatrix (fun a => σ a • F a) ω ^ 4) ∂stdGaussianMeasure m)
      ≤ 3 * (n q : ℝ) * c q := 
  Paper10.prop_2_4_quartic F hF σ hσ

/-- Fixed source-facing contract: cubic_gaussian. -/
theorem cubic_gaussian {q m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F)
    (σ : Fin m → ℝ) (hσ : ∀ a, 0 ≤ σ a ∧ σ a ≤ 1) :
    (∫ ω, Matrix.trace (gaussianMatrix (fun a => σ a • F a) ω ^ 3) ^ 2 ∂stdGaussianMeasure m)
      ≤ 27 * (n q : ℝ) * c q := 
  Paper10.prop_2_4_cubic F hF σ hσ

/-- Fixed source-facing contract: quartic_wick_expansion. -/
theorem quartic_wick_expansion {q m : ℕ} (B : Fin m → Matrix (Fin q) (Fin q) ℝ) :
    (∫ ω, Matrix.trace (gaussianMatrix B ω ^ 4) ∂stdGaussianMeasure m) =
      2 * Matrix.trace ((∑ a, B a * B a) * (∑ a, B a * B a)) +
      ∑ a, ∑ b, Matrix.trace (B a * B b * B a * B b) := 
  Paper10.fourth_moment_expansion B

/-- Fixed source-facing contract: cubic_wick_expansion. -/
theorem cubic_wick_expansion {q m : ℕ} (B : Fin m → Matrix (Fin q) (Fin q) ℝ) (hB : ∀ a, (B a).IsSymm) :
    (∫ ω, Matrix.trace (gaussianMatrix B ω ^ 3) ^ 2 ∂stdGaussianMeasure m) =
      6 * (∑ a, ∑ b, ∑ c, Matrix.trace (B a * B b * B c) ^ 2) +
      9 * (∑ a, (Matrix.trace (B a * ∑ b, B b * B b)) ^ 2) := 
  Paper10.cubic_moment_expansion B hB

/-- Fixed source-facing contract: matrix_remainder. -/
theorem matrix_remainder {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.IsSymm) {t : ℝ}
    (ht : 0 < t) (hsmall : t * ‖A‖ ≤ 1 / 2) :
    |Ft t A| ≤ 2 * t * |Matrix.trace (A ^ 3)| + 8 * t ^ 2 * Matrix.trace (A ^ 4) := 
  Paper10.lemma_3_1_opNorm A hA ht hsmall

/-- Fixed source-facing contract: derivative_identity. -/
theorem derivative_identity {q m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F)
    (R K : Matrix (Fin q) (Fin q) ℝ) (hR : IsUnit R) (hK : K.IsSymm) {s : ℝ} (hs : 0 < s) :
    metricDerivativeHSNormSq F R K s = (q + 2 : ℝ) * frobNormSq K + (Matrix.trace K) ^ 2 := 
  Paper10.prop_4_1_derivative_identity F hF R K hR hK hs

/-- Fixed source-facing contract: isotropic_quartic. -/
theorem isotropic_quartic {q m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F) :
    (∫ ω, Matrix.trace (gaussianMatrix F ω ^ 4) ∂stdGaussianMeasure m) =
      (q : ℝ) * (2 * (q : ℝ) ^ 2 + 5 * (q : ℝ) + 5) / 4 := 
  Paper10.iso_quartic F hF

/-- Fixed source-facing contract: isotropic_cubic. -/
theorem isotropic_cubic {q m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F) :
    (∫ ω, Matrix.trace (gaussianMatrix F ω ^ 3) ^ 2 ∂stdGaussianMeasure m) =
      3 * (q : ℝ) * (4 * (q : ℝ) ^ 2 + 9 * (q : ℝ) + 7) / 4 := 
  Paper10.iso_cubic_sq F hF

/-- Fixed source-facing contract: quartic_maximum. -/
theorem quartic_maximum {q m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F)
    (σ : Fin m → ℝ) (hσ : ∀ a, 0 ≤ σ a ∧ σ a ≤ 1) :
    (∫ ω, Matrix.trace (gaussianMatrix (fun a => σ a • F a) ω ^ 4) ∂stdGaussianMeasure m) ≤
      (q : ℝ) * (2 * (q : ℝ) ^ 2 + 5 * (q : ℝ) + 5) / 4 := 
  Paper10.iso_quartic_max F hF σ hσ

/-- Fixed source-facing contract: proposal_covariance. -/
theorem proposal_covariance {q m : ℕ} (hq : 0 < q) {s : ℝ} (hs : c q ≤ s) (r : ℝ)
    (E : Matrix (Fin m) (Fin m) ℝ) (hE : E.PosSemidef) :
    let hs0 := lt_of_lt_of_le (c_pos q) hs
    let L := proposalCoefficientMatrix (q := q) s r E hs0 hE
    L * Lᵀ = (r ^ 2 / (n q : ℝ)) • (s • (1 : Matrix (Fin m) (Fin m) ℝ) + E)⁻¹ := 
  Paper10.proposalCoefficientMatrix_covariance hq hs r E hE

/-- Fixed source-facing contract: proposal_gaussian. -/
theorem proposal_gaussian {q m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (R : Matrix (Fin q) (Fin q) ℝ) (s r : ℝ) (E : Matrix (Fin m) (Fin m) ℝ)
    (hs : 0 < s) (hE : E.PosSemidef) :
    IsGaussian ((stdGaussianMeasure m).map (proposalStep F R s r E hs hE)) := 
  Paper10.proposalStep_isGaussian F R s r E hs hE

/-- Fixed source-facing contract: metric_calculus. -/
theorem metric_calculus {q : ℕ} (s : ℝ) (X H U V : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef) :
    HasDerivAt (fun t : ℝ => g s (X + t • H) U V) (metricDerivative s X H U V) 0 := 
  Paper10.hasDerivAt_metric s X H U V hX

/-- Fixed source-facing contract: gradient_parameter. -/
theorem gradient_parameter {q : ℕ} (X : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef) {s : ℝ} (hs : 0 < s) :
    frob (barrierGradient s X) (metricInverse s X (barrierGradient s X)) = s * (q : ℝ) := 
  Paper10.gradient_parameter X hX hs

/-- Fixed source-facing contract: canonical_basis. -/
theorem canonical_basis (q : ℕ) : OrthonormalFrob (canonicalF q) := 
  Paper10.canonicalF_orthonormal q

/-- Fixed source-facing contract: sum_FUF. -/
theorem sum_FUF {q : ℕ} {ι : Type*} [Fintype ι] (F : ι → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F)
    (U : Matrix (Fin q) (Fin q) ℝ) :
    ∑ a, F a * U * F a = (1 / 2 : ℝ) • (Uᵀ + Matrix.trace U • (1 : Matrix _ _ ℝ)) := 
  Paper10.sum_FUF F hF U

/-- Fixed source-facing contract: congruence_domain. -/
theorem congruence_domain {q : ℕ} (X H : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef) (hH : H.IsSymm) :
    ∃ R K : Matrix (Fin q) (Fin q) ℝ, IsUnit R ∧ K.IsSymm ∧ X = R * Rᴴ ∧ H = R * K * Rᴴ := 
  Paper10.congruence_coordinates_complete X H hX hH


/-- Independent source-facing supplemental contract: poincare_poly. -/
theorem poincare_poly {m : ℕ} (p : MvPolynomial (Fin m) ℝ) :
    ProbabilityTheory.variance (fun ω => MvPolynomial.eval ω p) (stdGaussianMeasure m) ≤
      ∫ ω, ∑ i, (Hermite.coordinateDerivative (fun η => MvPolynomial.eval η p) ω i) ^ 2
        ∂stdGaussianMeasure m := 
  Paper10.Hermite.gaussian_poincare_poly p

/-- Independent source-facing supplemental contract: hermite_orthogonality. -/
theorem hermite_orthogonality (j k : ℕ) :
    (∫ x, (Hermite.hp j).eval x * (Hermite.hp k).eval x ∂gaussianReal 0 1) =
      if j = k then (j.factorial : ℝ) else 0 := 
  Paper10.Hermite.orthogonal j k

/-- Independent source-facing supplemental contract: hermite_variance. -/
theorem hermite_variance {m : ℕ} (s : Finset (Fin m → ℕ)) (a : (Fin m → ℕ) → ℝ) :
    ProbabilityTheory.variance (fun ω => ∑ α ∈ s, a α * Hermite.multi α ω) (stdGaussianMeasure m) =
      ∑ α ∈ s, if α = 0 then 0 else a α ^ 2 * Hermite.factorial α := 
  Paper10.Hermite.expansion_variance s a

/-- Independent source-facing supplemental contract: hermite_energy. -/
theorem hermite_energy {m : ℕ} (s : Finset (Fin m → ℕ)) (a : (Fin m → ℕ) → ℝ) :
    (∫ ω, ∑ i, (Hermite.coordinateDerivative (fun η => ∑ α ∈ s, a α * Hermite.multi α η) ω i) ^ 2
      ∂stdGaussianMeasure m) = ∑ α ∈ s, (Hermite.order α : ℝ) * a α ^ 2 * Hermite.factorial α := 
  Paper10.Hermite.expansion_energy s a

/-- Independent source-facing supplemental contract: quartic_convex. -/
theorem quartic_convex {q : ℕ} :
    ConvexOn ℝ {A : Matrix (Fin q) (Fin q) ℝ | A.IsSymm} (fun A => Matrix.trace (A ^ 4)) := 
  Paper10.trace_four_convexOn

/-- Independent source-facing supplemental contract: cubic_quartic. -/
theorem cubic_quartic {q m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) (σ : Fin m → ℝ) (hσ : ∀ a, 0 ≤ σ a ∧ σ a ≤ 1) :
    (∫ ω, Matrix.trace (gaussianMatrix (fun a => σ a • F a) ω ^ 3) ^ 2 ∂stdGaussianMeasure m) ≤
      9 * (∫ ω, Matrix.trace (gaussianMatrix (fun a => σ a • F a) ω ^ 4) ∂stdGaussianMeasure m) := 
  Paper10.cubic_variance_le_quartic F hF σ hσ

/-- Independent source-facing supplemental contract: sasc_rescaling. -/
theorem sasc_rescaling {q : ℕ} {s d : ℝ} (h : SASC q s) (hd : 0 < d) : SASC q (d * s) := 
  Paper10.sasc_rescale h hd

/-- Independent source-facing supplemental contract: uniform_rescaling. -/
theorem uniform_rescaling {d : ℝ} (hd : 0 < d) (h : UniformSASC) : UniformScaledSASC d hd := 
  Paper10.uniform_sasc_rescale hd h

/-- Independent source-facing supplemental contract: all_positive_sasc. -/
theorem all_positive_sasc {q : ℕ} (hq : 0 < q) {s : ℝ} (hs : 0 < s) : SASC q s := 
  Paper10.sasc_all_positive hq hs

/-- Independent source-facing supplemental contract: logdet_hessian. -/
theorem logdet_hessian {q : ℕ} (X H U : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef) :
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ => phi (X + t • H + u • U)) 0) (G X H U) 0 := 
  Paper10.hasDerivAt_phi_hessian X H U hX

/-- Independent source-facing supplemental contract: inverse_metric. -/
theorem inverse_metric {q : ℕ} (X U V : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef)
    {s : ℝ} (hs : 0 < s) : g s X (metricInverse s X V) U = frob V U := 
  Paper10.metricInverse_riesz X U V hX hs

/-- Independent source-facing supplemental contract: congruence_frame_span. -/
theorem congruence_frame_span {q m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F)
    (R H : Matrix (Fin q) (Fin q) ℝ) (hR : IsUnit R) (hH : H.IsSymm) :
    ∃ v : Fin m → ℝ, H = ∑ i, v i • (R * F i * Rᴴ) := 
  Paper10.congruence_frame_complete F hF R H hR hH

/-- Independent source-facing supplemental contract: frobenius_fourth. -/
theorem frobenius_fourth {q m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F) :
    (∫ ω, frobNormSq (gaussianMatrix F ω) ^ 2 ∂stdGaussianMeasure m) = (m : ℝ) * (m + 2) := 
  Paper10.isotropic_frobenius_fourth F hF

/-- Independent source-facing supplemental contract: metric_positive. -/
theorem metric_positive {q : ℕ} (X H : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef) (hH : H.IsSymm)
    {s : ℝ} (hs : 0 < s) (hH0 : H ≠ 0) : 0 < localNormSq s X H := 
  Paper10.localNormSq_pos X H hX hH hs hH0

/-- Independent source-facing supplemental contract: metric_smooth. -/
theorem metric_smooth {q : ℕ} (s : ℝ) (U V X : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef) (k : ℕ) :
    ContDiffAt ℝ k (fun Y : Matrix (Fin q) (Fin q) ℝ => g s Y U V) X := 
  Paper10.contDiffAt_metric s U V X hX k

/-- Independent source-facing supplemental contract: proposal_coordinate_mean. -/
theorem proposal_coordinate_mean {m : ℕ} (L : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    (∫ ω, linearGaussian L ω i ∂stdGaussianMeasure m) = 0 := 
  Paper10.linearGaussian_mean L i


/-- Actual matrix-valued centering of the Gaussian proposal. -/
theorem proposal_matrix_mean {q m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (R : Matrix (Fin q) (Fin q) ℝ) (s r : ℝ) (E : Matrix (Fin m) (Fin m) ℝ)
    (hs : 0 < s) (hE : E.PosSemidef) :
    (∫ ω, proposalStep F R s r E hs hE ω ∂stdGaussianMeasure m) = 0 := 
  Paper10.proposalStep_mean F R s r E hs hE

end Paper10.Challenge
