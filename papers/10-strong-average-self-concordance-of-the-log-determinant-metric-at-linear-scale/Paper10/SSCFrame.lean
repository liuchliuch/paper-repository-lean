import Paper10.MetricCalculus
import Paper10.CanonicalBasis

noncomputable section
open Matrix
namespace Paper10
variable {q m : ℕ}

/-- Polarization of the actual log-determinant quadratic form. -/
theorem localNormSq_add (s : ℝ) (X U V : Matrix (Fin q) (Fin q) ℝ) :
    localNormSq s X (U + V) = localNormSq s X U + 2 * g s X U V + localNormSq s X V := by
  unfold localNormSq g
  rw [G_add, G_add_right, G_add_right, G_eq_swap X V U]
  ring

/-- The bilinear metric is invariant under invertible congruence. -/
theorem g_congruence (R U V : Matrix (Fin q) (Fin q) ℝ) (hR : IsUnit R) (s : ℝ) :
    g s (R * Rᴴ) (R * U * Rᴴ) (R * V * Rᴴ) = g s 1 U V := by
  have h1 := localNormSq_congruence R 1 (U + V) hR s
  have h2 := localNormSq_congruence R 1 U hR s
  have h3 := localNormSq_congruence R 1 V hR s
  simp only [Matrix.mul_one, Matrix.mul_add, Matrix.add_mul] at h1 h2 h3
  rw [localNormSq_add, localNormSq_add] at h1
  linarith

/-- The congruence basis has metric Gram matrix sI; dividing by √s is a metric orthonormal frame. -/
theorem g_congruence_basis (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) (R : Matrix (Fin q) (Fin q) ℝ) (hR : IsUnit R) (s : ℝ) (i j : Fin m) :
    g s (R * Rᴴ) (R * F i * Rᴴ) (R * F j * Rᴴ) = s * (if i = j then 1 else 0) := by
  rw [g_congruence R _ _ hR]
  simp only [g, G, inv_one, Matrix.one_mul, Matrix.mul_one]
  change s * frob (F i) (F j) = _
  rw [hF.2.1]
  by_cases hij : i = j <;> simp [hij]

/-- Hilbert–Schmidt square of the normalized actual metric derivative, in a metric orthonormal frame. -/
def metricDerivativeHSNormSq (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (R K : Matrix (Fin q) (Fin q) ℝ) (s : ℝ) : ℝ :=
  ∑ i, ∑ j, (s⁻¹ * metricDerivative s (R * Rᴴ) (R * K * Rᴴ)
    (R * F i * Rᴴ) (R * F j * Rᴴ)) ^ 2

theorem anticomm_isSymm {K U : Matrix (Fin q) (Fin q) ℝ} (hK : K.IsSymm) (hU : U.IsSymm) :
    (anticomm K U).IsSymm := by
  unfold Matrix.IsSymm anticomm
  rw [Matrix.transpose_neg, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
    show Kᵀ = K from hK, show Uᵀ = U from hU, add_comm]

/-- Proposition 4.1 for the actual derivative and the actual metric orthonormal frame. -/
theorem prop_4_1_derivative_identity (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) (R K : Matrix (Fin q) (Fin q) ℝ) (hR : IsUnit R)
    (hK : K.IsSymm) {s : ℝ} (hs : 0 < s) :
    metricDerivativeHSNormSq F R K s = (q + 2 : ℝ) * frobNormSq K + (Matrix.trace K) ^ 2 := by
  have hc : ∀ i j, s⁻¹ * metricDerivative s (R * Rᴴ) (R * K * Rᴴ)
      (R * F i * Rᴴ) (R * F j * Rᴴ) = frob (anticomm K (F i)) (F j) := by
    intro i j
    rw [metricDerivative_congruence R K (F i) (F j) hR]
    field_simp
  have hp : ∀ i, (∑ j, frob (anticomm K (F i)) (F j) ^ 2) = frobNormSq (anticomm K (F i)) := by
    intro i
    have he : ∀ j, frob (anticomm K (F i)) (F j) = frob (F j) (anticomm K (F i)) :=
      fun j => Matrix.trace_mul_comm _ _
    simp_rw [he]
    exact frob_parseval F hF _ (anticomm_isSymm hK (hF.1 i))
  unfold metricDerivativeHSNormSq
  simp_rw [hc, hp]
  exact hsNormSqAnticomm_eq F hF K hK

/-- Local norm in the congruence frame. -/
theorem localNormSq_frame (R K : Matrix (Fin q) (Fin q) ℝ) (hR : IsUnit R) (s : ℝ) :
    localNormSq s (R * Rᴴ) (R * K * Rᴴ) = s * frobNormSq K := by
  have hh := localNormSq_congruence R 1 K hR s
  simpa [localNormSq, g, G, frobNormSq, frob] using hh

/-- Actual cubic metric derivative in a single direction. -/
theorem metricDerivative_diagonal (R K : Matrix (Fin q) (Fin q) ℝ) (hR : IsUnit R) (s : ℝ) :
    metricDerivative s (R * Rᴴ) (R * K * Rᴴ) (R * K * Rᴴ) (R * K * Rᴴ) =
      -(2 * s * Matrix.trace (K * K * K)) := by
  rw [metricDerivative_congruence R K K K hR]
  simp only [frob, anticomm, Matrix.neg_mul, Matrix.add_mul, Matrix.trace_neg, Matrix.trace_add]
  ring

/-- SSC for the actual log-det metric, in exhaustive congruence coordinates and a metric
orthonormal frame. The first conjunct is the ordinary self-concordance prerequisite. -/
def SSC (q : ℕ) (s : ℝ) : Prop :=
  (∀ R K : Matrix (Fin q) (Fin q) ℝ, IsUnit R → K.IsSymm →
    |metricDerivative s (R * Rᴴ) (R * K * Rᴴ) (R * K * Rᴴ) (R * K * Rᴴ)| ≤
      2 * (localNormSq s (R * Rᴴ) (R * K * Rᴴ)) ^ (3 / 2 : ℝ)) ∧
  (∀ R K : Matrix (Fin q) (Fin q) ℝ, IsUnit R → K.IsSymm →
    metricDerivativeHSNormSq (canonicalF q) R K s ≤ 4 * localNormSq s (R * Rᴴ) (R * K * Rᴴ))

/-- The exact SSC threshold, including the ordinary self-concordance prerequisite. -/
theorem thm_1_3_ssc (hq : 0 < q) {s : ℝ} (hs : 0 < s) : SSC q s ↔ c q ≤ s := by
  constructor
  · intro h
    apply (ssc_threshold_iff q s hq hs).mp
    intro K hK
    have hh := h.2 1 K isUnit_one hK
    rw [prop_4_1_derivative_identity (canonicalF q) (canonicalF_orthonormal q) 1 K isUnit_one hK hs,
      localNormSq_frame 1 K isUnit_one] at hh
    nlinarith
  · intro hscale
    constructor
    · intro R K hR hK
      rw [metricDerivative_diagonal R K hR, abs_neg, localNormSq_frame R K hR]
      exact ordinary_sc K hK hscale hq
    · intro R K hR hK
      rw [prop_4_1_derivative_identity (canonicalF q) (canonicalF_orthonormal q) R K hR hK hs,
        localNormSq_frame R K hR]
      have hh := (ssc_threshold_iff q s hq hs).mpr hscale K hK
      nlinarith

end Paper10
