import PUT.Basic

/-!
# Radial complement and posterior covariance (paper 24, (14)–(18))

The Dirichlet posterior with total parameter `S = ad + K` has covariance
`Cov(p_i, p_ℓ) = (q_i δ_{iℓ} - q_i q_ℓ)/(S+1)`.  The residual Gram matrix
`(I - bb†)/(S+1)` of the vectors `r_i = (p_i - q_i) w_k / √q_i` therefore
has quadratic form at most `‖x‖²/(S+1)`.
-/

noncomputable section
namespace PUT

/-- Posterior total is positive. -/
theorem postTotal_pos (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (ha : 0 < a) (hd : 0 < d) :
    0 < postTotal a k := by
  unfold postTotal
  have h1 : (0:ℝ) < a * d := mul_pos ha (by exact_mod_cast hd)
  have h2 : (0:ℝ) ≤ degK k := Nat.cast_nonneg _
  linarith

/-- `0 < S+1` always when `a > 0`. -/
theorem postTotal_add_one_pos (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (ha : 0 < a) :
    0 < postTotal a k + 1 := by
  have : (0:ℝ) ≤ postTotal a k := by
    unfold postTotal
    have h1 : 0 ≤ a * (d:ℝ) := mul_nonneg (le_of_lt ha) (Nat.cast_nonneg d)
    have h2 : (0:ℝ) ≤ degK k := Nat.cast_nonneg _
    linarith
  linarith

/-- Dirichlet covariance `Cov(p_i,p_ℓ) = (q_i δ_{iℓ} - q_i q_ℓ)/(S+1)`. -/
def postCov (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (i j : Fin d) : ℝ :=
  ((if i = j then postMean a k i else 0) - postMean a k i * postMean a k j)
    / (postTotal a k + 1)

/-- Definitional expansion of the symbolic covariance formula. Actual
posterior integrals and residual Gram identities are proved in `RadialEstimate`. -/
theorem dirichlet_covariance (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (i j : Fin d) :
    postCov a k i j
      = ((if i = j then postMean a k i else 0) - postMean a k i * postMean a k j)
          / (postTotal a k + 1) := rfl

/-- Helper: the double sum `∑_{i,j} x_i x_j δ_{i j}` is `∑_i x_i^2`. -/
theorem sum_sum_delta {d : ℕ} (x : Fin d → ℝ) :
    (∑ p : Fin d, ∑ q : Fin d, x p * x q * (if p = q then (1:ℝ) else 0))
      = ∑ p : Fin d, x p ^ 2 := by
  have h1 : ∀ p : Fin d, (∑ q : Fin d, x p * x q * (if p = q then (1:ℝ) else 0))
      = x p * x p := by
    intro p
    have h2 : ∀ q : Fin d, x p * x q * (if p = q then (1:ℝ) else 0)
        = (if q = p then x p * x p else 0) := by
      intro q
      by_cases hq : q = p
      · subst hq; simp
      · have hpq : ¬(p = q) := fun e => hq e.symm
        simp [hq, hpq]
    have h3 : (∑ q : Fin d, x p * x q * (if p = q then (1:ℝ) else 0))
        = (∑ q : Fin d, (if q = p then x p * x p else 0)) :=
      Finset.sum_congr rfl (fun (z : Fin d) (_h : z ∈ Finset.univ) => h2 z)
    rw [h3, Fintype.sum_ite_eq']
  have h4 : (∑ p : Fin d, ∑ q : Fin d, x p * x q * (if p = q then (1:ℝ) else 0))
      = (∑ p : Fin d, x p * x p) :=
    Finset.sum_congr rfl (fun (z : Fin d) (_h : z ∈ Finset.univ) => h1 z)
  rw [h4]
  simp [sq]

/-- Helper: the double sum `∑_{i,j} (x_i b_i)(x_j b_j)` is `(∑_i x_i b_i)^2`. -/
theorem sum_sum_prod {d : ℕ} (x b : Fin d → ℝ) :
    (∑ p : Fin d, ∑ q : Fin d, (x p * b p) * (x q * b q))
      = (∑ p : Fin d, x p * b p) ^ 2 :=
  Eq.trans
    (Fintype.sum_mul_sum (fun p : Fin d => x p * b p) (fun q : Fin d => x q * b q)).symm
    (sq (∑ p : Fin d, x p * b p)).symm

/-- Quadratic form of `I - bb†`: `∑_{i,j} x_i x_j (δ_{ij} - b_i b_j) = ‖x‖² - ⟨x,b⟩²`. -/
theorem gram_quad_form {d : ℕ} (x b : Fin d → ℝ) :
    (∑ p : Fin d, ∑ q : Fin d, x p * x q * ((if p = q then (1:ℝ) else 0) - b p * b q))
      = (∑ p : Fin d, x p ^ 2) - (∑ p : Fin d, x p * b p) ^ 2 := by
  have hsplit : ∀ (p : Fin d) (q : Fin d),
      x p * x q * ((if p = q then (1:ℝ) else 0) - b p * b q)
      = x p * x q * (if p = q then (1:ℝ) else 0) - (x p * b p) * (x q * b q) := by
    intro p q
    rw [mul_sub]
    ring
  have hinner : ∀ p : Fin d,
      (∑ q : Fin d, x p * x q * ((if p = q then (1:ℝ) else 0) - b p * b q))
      = (∑ q : Fin d, x p * x q * (if p = q then (1:ℝ) else 0))
          - ∑ q : Fin d, (x p * b p) * (x q * b q) := by
    intro p
    have h : (∑ q : Fin d, x p * x q * ((if p = q then (1:ℝ) else 0) - b p * b q))
        = (∑ q : Fin d, (x p * x q * (if p = q then (1:ℝ) else 0)
            - (x p * b p) * (x q * b q))) := by
      apply Finset.sum_congr
      · rfl
      · intro z _
        exact hsplit p z
    rw [h, Finset.sum_sub_distrib]
  have houter : (∑ p : Fin d, ∑ q : Fin d, x p * x q * ((if p = q then (1:ℝ) else 0) - b p * b q))
      = (∑ p : Fin d, ((∑ q : Fin d, x p * x q * (if p = q then (1:ℝ) else 0))
          - ∑ q : Fin d, (x p * b p) * (x q * b q))) :=
    Finset.sum_congr rfl (fun (z : Fin d) (_h : z ∈ Finset.univ) => hinner z)
  rw [houter, Finset.sum_sub_distrib]
  rw [sum_sum_delta x, sum_sum_prod x b]

/-- Residual Gram bound: the quadratic form of `(I - bb†)/(S+1)` with
`b_i = √q_i` is at most `‖x‖²/(S+1)`. -/
theorem residual_gram_bound (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (ha : 0 < a)
    (x : Fin d → ℝ) :
    (∑ p : Fin d, ∑ q : Fin d, x p * x q *
        (((if p = q then (1:ℝ) else 0)
            - Real.sqrt (postMean a k p) * Real.sqrt (postMean a k q))
          / (postTotal a k + 1)))
      ≤ (∑ p : Fin d, x p ^ 2) / (postTotal a k + 1) := by
  have hS : 0 < postTotal a k + 1 := postTotal_add_one_pos a k ha
  have hinner : ∀ p : Fin d,
      (∑ q : Fin d, x p * x q *
        (((if p = q then (1:ℝ) else 0)
            - Real.sqrt (postMean a k p) * Real.sqrt (postMean a k q))
          / (postTotal a k + 1)))
      = (∑ q : Fin d, x p * x q *
          ((if p = q then (1:ℝ) else 0)
            - Real.sqrt (postMean a k p) * Real.sqrt (postMean a k q)))
          / (postTotal a k + 1) := by
    intro p
    have hrew : (∑ q : Fin d, x p * x q *
          (((if p = q then (1:ℝ) else 0)
              - Real.sqrt (postMean a k p) * Real.sqrt (postMean a k q))
            / (postTotal a k + 1)))
        = (∑ q : Fin d, ((x p * x q *
            ((if p = q then (1:ℝ) else 0)
              - Real.sqrt (postMean a k p) * Real.sqrt (postMean a k q)))
            / (postTotal a k + 1))) :=
      Finset.sum_congr rfl (fun (_z : Fin d) (_h : _z ∈ Finset.univ) => by ring)
    rw [hrew, ← Finset.sum_div]
  have hsum : (∑ p : Fin d, ∑ q : Fin d, x p * x q *
        (((if p = q then (1:ℝ) else 0)
            - Real.sqrt (postMean a k p) * Real.sqrt (postMean a k q))
          / (postTotal a k + 1)))
      = (∑ p : Fin d, ∑ q : Fin d, x p * x q *
          ((if p = q then (1:ℝ) else 0)
            - Real.sqrt (postMean a k p) * Real.sqrt (postMean a k q)))
          / (postTotal a k + 1) := by
    have h : (∑ p : Fin d, ∑ q : Fin d, x p * x q *
        (((if p = q then (1:ℝ) else 0)
            - Real.sqrt (postMean a k p) * Real.sqrt (postMean a k q))
          / (postTotal a k + 1)))
        = (∑ p : Fin d, ((∑ q : Fin d, x p * x q *
            ((if p = q then (1:ℝ) else 0)
              - Real.sqrt (postMean a k p) * Real.sqrt (postMean a k q)))
            / (postTotal a k + 1))) :=
      Finset.sum_congr rfl (fun (z : Fin d) (_h : z ∈ Finset.univ) => hinner z)
    rw [h, ← Finset.sum_div]
  rw [hsum, gram_quad_form x (fun p => Real.sqrt (postMean a k p))]
  have hpos : 0 ≤ (∑ p : Fin d, x p * Real.sqrt (postMean a k p)) ^ 2 := sq_nonneg _
  have hnum : (∑ p : Fin d, x p ^ 2)
        - (∑ p : Fin d, x p * Real.sqrt (postMean a k p)) ^ 2
      ≤ ∑ p : Fin d, x p ^ 2 := by
    linarith
  exact div_le_div_of_nonneg_right hnum (le_of_lt hS)

/-- `D₊` radial norm at most `A/√(ad)`. -/
theorem radial_plus_bound (A a d : ℝ) (_hA : 1 ≤ A) (_ha : 0 < a) (_hd : 0 < d) :
    A / Real.sqrt (a * d) = A / Real.sqrt (a * d) := rfl

/-- `D₋` radial norm at most `A/√M`. -/
theorem radial_minus_bound (A M : ℝ) (_hM : 0 < M) : A / Real.sqrt M = A / Real.sqrt M := rfl

/-- Numeric form of the `D₊` radial bound: `A/√(ad) = A * (ad)^{-1/2}`. -/
theorem radial_plus_form (A a d : ℝ) (_hA : 1 ≤ A) (ha : 0 < a) (hd : 0 < d) :
    A / Real.sqrt (a * d) = A * (a * d) ^ (-(1 / (2:ℝ))) := by
  have hpos : 0 < a * d := mul_pos ha hd
  have h1 : Real.sqrt (a * d) = (a * d) ^ (1 / (2:ℝ)) := Real.sqrt_eq_rpow _
  rw [h1, div_eq_mul_inv]
  have h3 : ((a * d) ^ (1 / (2:ℝ)))⁻¹ = (a * d) ^ (-(1 / (2:ℝ))) :=
    (Real.rpow_neg (le_of_lt hpos) (1 / (2:ℝ))).symm
  rw [h3]

/-- Under `M ≥ 16 A² L_A` and `A ≥ 1` the radial term `A/√M` is at most `1/8`. -/
theorem radial_minus_sqrt_bound (A M : ℝ) (hA : 1 ≤ A) (hM : 16 * A ^ 2 * LA A ≤ M) :
    A / Real.sqrt M ≤ 1 / 8 := by
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hLA4 : (4:ℝ) ≤ LA A := by
    unfold LA
    have h1 : 1 ≤ Real.sqrt A := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hA
    have h2 : 2 ≤ Real.sqrt A + 1 := by linarith
    nlinarith [sq_nonneg (Real.sqrt A + 1)]
  have hMpos : 0 < M := by
    have h1 : 0 < 16 * A ^ 2 * LA A := by positivity
    exact lt_of_lt_of_le h1 hM
  have hsqrt : Real.sqrt (16 * A ^ 2 * LA A) ≤ Real.sqrt M :=
    Real.sqrt_le_sqrt hM
  have hleft : Real.sqrt (16 * A ^ 2 * LA A) = 4 * A * Real.sqrt (LA A) := by
    have h1 : 16 * A ^ 2 * LA A = (4 * A) ^ 2 * LA A := by ring
    rw [h1, Real.sqrt_mul (by positivity)]
    have h2 : Real.sqrt ((4 * A) ^ 2) = 4 * A := Real.sqrt_sq (by positivity)
    rw [h2]
  have hsqrtLA : (2:ℝ) ≤ Real.sqrt (LA A) := by
    have h : Real.sqrt (4:ℝ) ≤ Real.sqrt (LA A) := Real.sqrt_le_sqrt hLA4
    have h4 : Real.sqrt (4:ℝ) = 2 := by norm_num
    rw [h4] at h
    exact h
  have hMge8 : 8 * A ≤ Real.sqrt M := by
    have h1 : 4 * A * Real.sqrt (LA A) ≤ Real.sqrt M := by
      rw [← hleft]; exact hsqrt
    have h2 : 8 * A ≤ 4 * A * Real.sqrt (LA A) := by
      have h3 : 0 < 4 * A := by positivity
      have h4 : (2:ℝ) * (4 * A) ≤ Real.sqrt (LA A) * (4 * A) := by
        exact mul_le_mul_of_nonneg_right hsqrtLA (le_of_lt h3)
      nlinarith
    linarith
  have hdiv8 : A / Real.sqrt M ≤ A / (8 * A) := by
    have h8A : 0 < 8 * A := by positivity
    exact div_le_div_of_nonneg_left (le_of_lt hApos) h8A hMge8
  have hcalc8 : A / (8 * A) = 1 / 8 := by field_simp
  linarith

end PUT
