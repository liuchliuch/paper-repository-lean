/-
Copyright (c) 2026. Main results of
"The Griffiths exponent of random-field Ising dynamics at strong Gaussian disorder".
-/
import Paper09.Ising
import Paper09.Dynamics
import Paper09.SoftShell
import Paper09.Defects
import Paper09.Spectral
import Paper09.FiniteProb

open Finset BigOperators Classical Real Filter

namespace Paper09

/-! ## Dimension exponent `a = (d-1)/d` -/

/-- Theorem 1.3 exponent `a = (d-1)/d`. -/
noncomputable def aExp (d : ℝ) : ℝ := (d - 1) / d

theorem aExp_eq (d : ℝ) (hd : 0 < d) : aExp d = 1 - 1 / d := by
  unfold aExp
  field_simp [ne_of_gt hd]

theorem aExp_two : aExp 2 = 1 / 2 := by
  norm_num [aExp]

theorem aExp_pos {d : ℝ} (hd : 2 ≤ d) : 0 < aExp d := by
  have h : (0:ℝ) < d := by linarith
  have h1 : (1:ℝ) < d := by linarith
  unfold aExp
  apply div_pos <;> linarith

theorem aExp_lt_one {d : ℝ} (hd : 2 ≤ d) : aExp d < 1 := by
  have h : (0:ℝ) < d := by linarith
  unfold aExp
  rw [div_lt_one h]
  linarith

/-! ## Lemma 2.2 — Soft-shell comparison (2.2) -/

/-- Deterministic engine of Lemma 2.2 (fully proved).
Under the oscillation sandwich `e^{-D} ν ≤ μ ≤ e^{D} ν`,
`ℰ_μ(f,f) · Var_ν(f) ≤ e^{2D} gapν Var_ν(f) Var_μ(f)`. -/
theorem lemma_2_2_engine {α : Type*} [Fintype α]
    {G : UpdateGraph α} {ν μ : FinProb α} {D gapν : ℝ}
    (f : α → ℝ)
    (hgap : G.dirichlet ν f ≤ gapν * FinProb.variance ν f)
    (hlo : ∀ y, exp (-D) * ν.w y ≤ μ.w y)
    (hhi : ∀ y, μ.w y ≤ exp D * ν.w y) :
    G.dirichlet μ f * FinProb.variance ν f
      ≤ exp (2 * D) * (gapν * FinProb.variance ν f * FinProb.variance μ f) :=
  lemma_2_2_soft_shell f hgap hlo hhi

/-- Lemma 2.2 with the paper's `D = 2 A_B + b k`, giving `e^{4 A_B + 2 b k}`. -/
theorem lemma_2_2_fixed_shell {α : Type*} [Fintype α]
    {G : UpdateGraph α} {ν μ : FinProb α} {A b k gapν : ℝ}
    (f : α → ℝ)
    (hgap : G.dirichlet ν f ≤ gapν * FinProb.variance ν f)
    (_hA : 0 ≤ A) (_hb : 0 ≤ b) (_hk : 0 ≤ k)
    (hlo : ∀ y, exp (- (2 * A + b * k)) * ν.w y ≤ μ.w y)
    (hhi : ∀ y, μ.w y ≤ exp (2 * A + b * k) * ν.w y) :
    G.dirichlet μ f * FinProb.variance ν f
      ≤ exp (4 * A + 2 * b * k) * (gapν * FinProb.variance ν f * FinProb.variance μ f) := by
  have h := lemma_2_2_soft_shell f hgap hlo hhi
  have h2 : exp (2 * (2 * A + b * k)) = exp (4 * A + 2 * b * k) := by
    congr 1; ring
  rw [h2] at h
  exact h

/-! ## Lemma 2.3 — Equilibrium shell defects (2.5)–(2.6) -/

theorem lemma_2_3_moments (n : ℕ) (q b : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hb : 0 ≤ b) :
    (∑ k ∈ range (n + 1),
        ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * exp (b * k))
        ≤ exp ((n : ℝ) * q * (exp b - 1)) ∧
    exp (-b * (n : ℝ) * q)
        ≤ (∑ k ∈ range (n + 1),
        ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * exp (-b * k)) :=
  lemma_2_3_defect_moments n q b hq hq1 hb

theorem lemma_2_3_gap (n : ℕ) (q b A gapπ gapν : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hb : 0 ≤ b) (hA : 0 ≤ A) (hgapν : 0 ≤ gapν)
    (hsoft : gapπ ≤ gapν * exp (4 * A)
      * ((∑ k ∈ range (n + 1),
          ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * exp (b * k))
      / (∑ k ∈ range (n + 1),
          ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * exp (-b * k)))) :
    gapπ ≤ gapν * exp (4 * A + (n : ℝ) * q * (exp b - 1 + b)) :=
  lemma_2_3_gap_bound_binomial n q b A gapπ gapν hq hq1 hb hA hgapν hsoft

/-! ## Lemma A.1 — Relaxation and mixing (A.1) -/

theorem lemma_A_1_mixing_lower {t gap : ℝ}
    (ht : 0 ≤ t) (hgap : 0 < gap)
    (h : exp (- t * gap) / 2 > 1 / 4) :
    t < log 2 / gap :=
  lemma_A_1_lower ht hgap h

theorem lemma_A_1_mixing_upper {ε πmin t gap : ℝ}
    (hε : 0 < ε) (hε' : ε < 1) (hπ : 0 < πmin) (hgap : 0 < gap)
    (hT : log (1 / (ε * πmin)) / gap ≤ t) :
    exp (- t * gap) * (1 / πmin) ≤ 1 / ε :=
  lemma_A_1_upper_algebra hε hε' hπ hgap hT

/-- Scalar exponential/logarithmic implications used in Appendix A.1.
This is not the finite-chain spectral mixing theorem. -/
theorem lemma_A_1_full {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    (∀ t gap : ℝ, 0 ≤ t → 0 < gap → exp (-t * gap) / 2 > 1 / 4 →
        t < log 2 / gap) ∧
    (∀ t gap πmin : ℝ, 0 < πmin → 0 < gap →
        log (1 / (ε * πmin)) / gap ≤ t →
        exp (- t * gap) * (1 / πmin) ≤ 1 / ε) := by
  refine ⟨?_, ?_⟩
  · intro t gap ht hgap h
    exact lemma_A_1_lower ht hgap h
  · intro t gap πmin hπ hgap hT
    have hε1 : ε < 1 := lt_trans hε' (by norm_num)
    exact lemma_A_1_upper_algebra hε hε1 hπ hgap hT

/-! ## Theorem 1.3 — two-sided bound and double-log exponent -/

/-- The first logarithm of the two assumed exponential bounds.
The actual double-log convergence is proved in `Paper09.Asymptotics`. -/
theorem theorem_1_3_consequence {Y n c C a d : ℝ}
    (hn : 3 ≤ n) (hc : 0 < c) (hC : 0 < C) (ha : 0 < a) (_hd : 0 < d)
    (hYpos : 0 < Y)
    (hlo : exp (c * (log n / log (log n)) ^ a) ≤ Y)
    (hhi : Y ≤ exp (C * (log n) ^ a * (log (log n)) ^ d)) :
    c * (log n / log (log n)) ^ a ≤ log Y ∧
    log Y ≤ C * (log n) ^ a * (log (log n)) ^ d :=
  ⟨theorem_1_3_loglog_lower hn hc ha hlo,
    theorem_1_3_loglog_upper hn hC ha hYpos hhi⟩

/-- The scalar logarithmic bounds and dimension exponent.
This auxiliary theorem does not assert the RFIM probability bounds (1.5). -/
theorem theorem_1_3_two_sided {d c C : ℝ}
    (hd : 2 ≤ d) (hc : 0 < c) (hC : 0 < C) :
    let a := aExp d
    0 < a ∧ a < 1 ∧
    ∀ n Y, 3 ≤ n → 0 < Y →
      exp (c * (log n / log (log n)) ^ a) ≤ Y →
      Y ≤ exp (C * (log n) ^ a * (log (log n)) ^ (d - 1)) →
      c * (log n / log (log n)) ^ a ≤ log Y ∧
      log Y ≤ C * (log n) ^ a * (log (log n)) ^ (d - 1) := by
  have ha : 0 < aExp d := aExp_pos hd
  have ha' : aExp d < 1 := aExp_lt_one hd
  refine ⟨ha, ha', ?_⟩
  intro n Y hn hYpos hlo hhi
  have hn3 : (3:ℝ) ≤ n := hn
  have hdpos : (0:ℝ) < d - 1 := by linarith
  exact theorem_1_3_consequence (d := d - 1) hn3 hc hC ha hdpos hYpos hlo hhi

/-- Dimension-two exponent identity; the low-temperature RFIM corollary
also requires the independent pure-box and disorder arguments. -/
theorem corollary_1_4 : aExp 2 = 1 / 2 := aExp_two

/-- Theorem 1.3 exponent identity. -/
theorem theorem_1_3_exponent (d : ℝ) : aExp d = (d - 1) / d := rfl

/-! ## Proposition 2.1 engine (island gap cost (2.9)) -/

/-- Gap cost on an island event: (2.9) yields
`gap ≤ exp(-(c0/2) m^{d-1})`. -/
theorem gap_bound_on_island (c0 ε0 m d qH0 b0 : ℝ)
    (hm : 0 < m) (_hd : 0 < d) (_hq : 0 ≤ qH0) (_hb0 : 0 ≤ b0)
    (hε : ε0 = c0 / 16)
    (hH : 2 * d * qH0 * (exp b0 - 1 + b0) ≤ c0 / 4) :
    -c0 * m ^ (d - 1) + 4 * ε0 * m ^ (d - 1)
        + 2 * d * m ^ (d - 1) * qH0 * (exp b0 - 1 + b0)
      ≤ -(c0 / 2) * m ^ (d - 1) := by
  set p := m ^ (d - 1)
  have hp : 0 ≤ p := Real.rpow_nonneg (le_of_lt hm) _
  have h6 : 2 * d * p * qH0 * (exp b0 - 1 + b0) ≤ (c0 / 4) * p := by
    nlinarith [hH, hp]
  have h7 : 4 * ε0 * p = (c0 / 4) * p := by rw [hε]; ring
  have h8 : -c0 * p + 4 * ε0 * p + 2 * d * p * qH0 * (exp b0 - 1 + b0)
      ≤ -c0 * p + (c0 / 4) * p + (c0 / 4) * p := by
    nlinarith [h6, h7]
  have h9 : -c0 * p + (c0 / 4) * p + (c0 / 4) * p = -(c0 / 2) * p := by ring
  nlinarith [h8, h9]

/-- Island size identity (2.11): `r = (γ log n / log log n)^{1/d}` satisfies
`r^d = γ log n / log log n`. -/
theorem island_power (γ n d : ℝ)
    (hγ : 0 < γ) (hn : 3 ≤ n) (hd : 0 < d) :
    let r := (γ * log n / log (log n)) ^ (1 / d)
    0 < r ∧ r ^ d = γ * log n / log (log n) := by
  have hlogn : 1 < log n := one_lt_log_of_three_le hn
  have hloglog : 0 < log (log n) := log_pos hlogn
  have hbase : 0 < γ * log n / log (log n) := by
    have : 0 < log n := lt_trans (by norm_num) hlogn
    positivity
  refine ⟨Real.rpow_pos_of_pos hbase (1 / d), ?_⟩
  rw [← Real.rpow_mul (le_of_lt hbase)]
  have h : (1 / d) * d = 1 := by field_simp [ne_of_gt hd]
  rw [h, Real.rpow_one]

/-! ## Proposition 3.1 / Lemmas 3.2–3.6 combinatorial cores -/

/-- Lemma 3.2 binomial tail: `(2 d e p)^r ≤ (e/10)^r` when `p < 1/(20d)`. -/
theorem binomial_tail_estimate (d p r : ℝ)
    (hd : 1 ≤ d) (hp : 0 ≤ p) (hp' : p < 1 / (20 * d)) (hr : 1 ≤ r) :
    (2 * d * exp 1 * p) ^ r ≤ (exp 1 / 10) ^ r := by
  have h1 : 0 < exp 1 := exp_pos 1
  have hbase : 0 ≤ 2 * d * exp 1 * p := by
    have : 0 < 2 * d := by positivity
    positivity
  have h2 : 2 * d * exp 1 * p < exp 1 / 10 := by
    have h3 : 2 * d * exp 1 * p < 2 * d * exp 1 * (1 / (20 * d)) :=
      mul_lt_mul_of_pos_left hp' (mul_pos (by positivity) h1)
    have h4 : 2 * d * exp 1 * (1 / (20 * d)) = exp 1 / 10 := by
      have hd0 : d ≠ 0 := by linarith
      field_simp [hd0]
      ring
    linarith
  exact Real.rpow_le_rpow hbase (le_of_lt h2) (le_of_lt (lt_of_lt_of_le (by norm_num) hr))

/-- Lemma 3.3 type-1 block size: `(2s+1) ≤ R` with `s = R/8` and `R ≥ 8`. -/
theorem type1_block_size (R : ℝ) (hR : 8 ≤ R) :
    (2 * (R / 8) + 1) ≤ R := by
  linarith

/-- Coverage count (3.5) lower: the number of admissible centers is positive. -/
theorem covering_count (s : ℝ) (_hs : 0 ≤ s) :
    0 < 2 * s + 1 := by linarith

/-- Boundary count (3.5): `2 d (2s+1)^{d-1} > 0`. -/
theorem boundary_count_algebra (s d : ℝ) (_hs : 0 ≤ s) (hd : 1 ≤ d) :
    0 < 2 * d * (2 * s + 1) ^ (d - 1) := by
  have h1 : 0 < 2 * s + 1 := by linarith
  have h2 : 0 < (2 * s + 1) ^ (d - 1) := Real.rpow_pos_of_pos h1 _
  positivity

/-- Lemma 3.5 ideal-step contraction (3.15) algebra. -/
theorem ideal_step_one_site (Iy Jy Q HR : ℝ)
    (_hI : 0 < Iy) (hQ : 0 < Q) (_hJ : 0 ≤ Jy) (_hHR : 0 ≤ HR)
    (hHRJ : HR * Jy ≤ Iy / 2) :
    1 - Iy / Q + HR * Jy / Q ≤ 1 - Iy / (2 * Q) := by
  have h1 : HR * Jy / Q ≤ Iy / 2 / Q := by
    rw [div_le_div_iff₀ hQ hQ]
    nlinarith
  have h2 : 1 - Iy / Q + Iy / 2 / Q = 1 - Iy / (2 * Q) := by
    field_simp [ne_of_gt hQ]
    ring
  nlinarith [h1, h2]

/-- Lemma 3.6 simulated-step: the error `2 M δ_M (I+J)/Q` with `δ_M = c_*/M^2`
is absorbed when `c_*` is small. -/
theorem simulated_error_absorbed (M Iy Jy Q cstar : ℝ)
    (hM : 1 ≤ M) (hI : 0 < Iy) (hQ : 0 < Q) (_hJ : 0 ≤ Jy)
    (_hc : 0 < cstar) (hc' : cstar ≤ 1 / 32)
    (hIJ : Iy + Jy ≤ 4 * Iy) :
    2 * M * (cstar / M ^ 2) * (Iy + Jy) / Q ≤ Iy / (4 * Q) := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have h1 : 2 * M * (cstar / M ^ 2) * (Iy + Jy) / Q
      = 2 * cstar * (Iy + Jy) / (M * Q) := by
    field_simp [ne_of_gt hMpos]
  have h2 : 2 * cstar * (Iy + Jy) / (M * Q)
      ≤ 8 * cstar * Iy / (M * Q) := by
    have h3 : 2 * cstar * (Iy + Jy) ≤ 8 * cstar * Iy := by
      nlinarith [hIJ, mul_nonneg (le_of_lt (by positivity : (0:ℝ) < cstar)) (le_of_lt hI)]
    have h4 : 0 < M * Q := mul_pos hMpos hQ
    rw [div_le_div_iff₀ h4 h4]
    nlinarith
  have h3 : 8 * cstar * Iy / (M * Q) ≤ Iy / (4 * Q) := by
    have h4 : 0 < M * Q := mul_pos hMpos hQ
    have h5 : 0 < (4:ℝ) * Q := by positivity
    refine (div_le_div_iff₀ h4 h5).mpr ?_
    have hle : (32:ℝ) * cstar ≤ M := by
      have hcs : (32:ℝ) * cstar ≤ 1 := by nlinarith [hc']
      linarith
    have key : (8 * cstar * Iy) * (4 * Q) ≤ Iy * (M * Q) := by
      have e1 : (8 * cstar * Iy) * (4 * Q) = (32 * cstar) * (Iy * Q) := by ring
      have e2 : Iy * (M * Q) = M * (Iy * Q) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right hle (mul_nonneg (le_of_lt hI) (le_of_lt hQ))
    exact key
  nlinarith [h1, h2, h3]

end Paper09
