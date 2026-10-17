import PUT.Basic
import PUT.Moments

/-!
# Lemma 2 of paper 24 — Dirichlet mass on the TV alternative

If `d ≥ 2`, `a ≥ 1`, and `P ∼ Dir(a,…,a)`, then
`ℙ[d_TV(P,u_d) ≥ 1/(24√a)] ≥ 1/144`.

We formalize the paper's computation as exact algebraic identities and
real inequalities on Beta/Dirichlet moments, then derive the
Paley–Zygmund consequence.
-/

noncomputable section
namespace PUT

open MeasureTheory

/-! ## Beta raw and central moments -/

/-- Beta/Dirichlet raw moment `E[Y^r] = (a)_r / (a+b)_r`. -/
def betaRawMoment (a b : ℝ) (r : ℕ) : ℝ :=
  risingFactorial a r / risingFactorial (a + b) r

/-- Beta mean `a/(a+b)`. -/
def betaMean (a b : ℝ) : ℝ := a / (a + b)

/-- Beta variance `ab / ((a+b)²(a+b+1))`. -/
def betaVar (a b : ℝ) : ℝ := a * b / ((a + b) ^ 2 * (a + b + 1))

/-- Second central moment of `Beta(a,b)`, written from raw moments. -/
def betaCentral2 (a b : ℝ) : ℝ :=
  betaRawMoment a b 2 - betaMean a b ^ 2

/-- Fourth central moment of `Beta(a,b)`, written from raw moments. -/
def betaCentral4 (a b : ℝ) : ℝ :=
  betaRawMoment a b 4
    - 4 * betaMean a b * betaRawMoment a b 3
    + 6 * betaMean a b ^ 2 * betaRawMoment a b 2
    - 4 * betaMean a b ^ 3 * betaRawMoment a b 1
    + betaMean a b ^ 4

/-- Variance of a Dirichlet coordinate: `(d-1)/(d²(ad+1))`. -/
def dirVar (a : ℝ) (d : ℕ) : ℝ :=
  (d - 1 : ℝ) / (d ^ 2 * (a * d + 1))

/-! ### Raw moments in expanded form -/

theorem betaRawMoment_zero (a b : ℝ) : betaRawMoment a b 0 = 1 := by
  simp [betaRawMoment]

theorem betaRawMoment_one (a b : ℝ) : betaRawMoment a b 1 = a / (a + b) := by
  simp [betaRawMoment]

theorem betaRawMoment_two (a b : ℝ) :
    betaRawMoment a b 2 = a * (a + 1) / ((a + b) * (a + b + 1)) := by
  simp [betaRawMoment, risingFactorial_succ_coe]

theorem betaRawMoment_three (a b : ℝ) :
    betaRawMoment a b 3 =
      a * (a + 1) * (a + 2) / ((a + b) * (a + b + 1) * (a + b + 2)) := by
  simp [betaRawMoment, risingFactorial_succ_coe]

theorem betaRawMoment_four (a b : ℝ) :
    betaRawMoment a b 4 =
      a * (a + 1) * (a + 2) * (a + 3)
        / ((a + b) * (a + b + 1) * (a + b + 2) * (a + b + 3)) := by
  simp [betaRawMoment, risingFactorial_succ_coe]

theorem betaMean_eq (a b : ℝ) : betaMean a b = a / (a + b) := rfl

theorem betaVar_eq (a b : ℝ) : betaVar a b = a * b / ((a + b) ^ 2 * (a + b + 1)) := rfl

/-! ### Central moments equal the classical formulas -/

theorem betaCentral2_eq (a b : ℝ) (hab : 0 < a + b) :
    betaCentral2 a b = betaVar a b := by
  unfold betaCentral2 betaMean betaVar
  rw [betaRawMoment_two]
  field_simp
  ring

/-- Exact fourth-moment ratio of a Beta law (paper (25)). -/
theorem betaCentral4_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    betaCentral4 a b = (betaVar a b) ^ 2 *
      (3 + 6 * ((a - b) ^ 2 * (a + b + 1) - a * b * (a + b + 2))
        / (a * b * (a + b + 2) * (a + b + 3))) := by
  unfold betaCentral4 betaMean betaVar
  rw [betaRawMoment_four, betaRawMoment_three, betaRawMoment_two, betaRawMoment_one]
  have h1 : 0 < a + b := by positivity
  have h2 : (0 : ℝ) < a + b + 1 := by positivity
  have h3 : (0 : ℝ) < a + b + 2 := by positivity
  have h4 : (0 : ℝ) < a + b + 3 := by positivity
  field_simp
  ring

/-! ## Numerical bounds on the fourth-moment ratio -/

/-- Paper's first inequality in (25): `E[X⁴]/σ⁴ ≤ 3 + 6/a`
provided `0 < a ≤ 2b`. -/
theorem fourth_moment_ratio_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ 2 * b) :
    betaCentral4 a b / (betaVar a b) ^ 2 ≤ 3 + 6 / a := by
  have hpos : 0 < betaVar a b := by
    unfold betaVar
    positivity
  have hpow : 0 < (betaVar a b) ^ 2 := pow_pos hpos 2
  have hexp := betaCentral4_eq a b ha hb
  have hden : (0 : ℝ) < a * b * (a + b + 2) * (a + b + 3) := by
    positivity
  have hab2 : (a - b) ^ 2 ≤ b ^ 2 := by
    have habs : |a - b| ≤ b := by
      rcases le_total a b with h | h
      · rw [abs_of_nonpos (by linarith : a - b ≤ 0)]
        linarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ a - b)]
        linarith
    have : |a - b| ^ 2 ≤ b ^ 2 := by nlinarith [abs_nonneg (a - b)]
    simpa [sq] using this
  have hcross : b * (a + b + 1) ≤ (a + b + 2) * (a + b + 3) := by
    nlinarith
  set N := (a - b) ^ 2 * (a + b + 1) - a * b * (a + b + 2) with hN
  set D := a * b * (a + b + 2) * (a + b + 3) with hD
  have hNle : N ≤ b ^ 2 * (a + b + 1) := by
    have : (0 : ℝ) ≤ a * b * (a + b + 2) := by positivity
    nlinarith
  have hstep1 : 6 * N / D ≤ 6 * (b ^ 2 * (a + b + 1)) / D := by
    apply div_le_div_of_nonneg_right
    · nlinarith
    · exact le_of_lt hden
  have hstep2 : 6 * (b ^ 2 * (a + b + 1)) / D ≤ 6 / a := by
    have hD' : D = a * b * ((a + b + 2) * (a + b + 3)) := by
      rw [hD]; ring
    have hfac : 6 * (b ^ 2 * (a + b + 1)) = 6 * b * (b * (a + b + 1)) := by ring
    rw [hD', hfac]
    have h6b : (0 : ℝ) ≤ 6 * b := by positivity
    have hle : 6 * b * (b * (a + b + 1)) ≤ 6 * b * ((a + b + 2) * (a + b + 3)) :=
      mul_le_mul_of_nonneg_left hcross h6b
    have hA : 6 * b * (b * (a + b + 1)) / (a * b * ((a + b + 2) * (a + b + 3)))
        ≤ 6 * b * ((a + b + 2) * (a + b + 3)) / (a * b * ((a + b + 2) * (a + b + 3))) :=
      div_le_div_of_nonneg_right hle (by positivity)
    have hcancel : 6 * b * ((a + b + 2) * (a + b + 3)) / (a * b * ((a + b + 2) * (a + b + 3)))
        = 6 / a := by
      field_simp
    rw [hcancel] at hA
    exact hA
  have hthis : (3 + 6 * N / D : ℝ) ≤ 3 + 6 / a := by
    linarith
  rw [hexp, hN, hD, mul_div_cancel_left₀ _ hpow.ne']
  exact hthis

/-- Paper's second inequality in (25): the ratio is at most `9` when `1 ≤ a`. -/
theorem fourth_moment_ratio_le_nine (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ha1 : 1 ≤ a) (hab : a ≤ 2 * b) :
    betaCentral4 a b / (betaVar a b) ^ 2 ≤ 9 := by
  have h1 := fourth_moment_ratio_le a b ha hb hab
  have h2 : (3 + 6 / a : ℝ) ≤ 9 := by
    have h3 : 6 / a ≤ 6 := by
      rw [div_le_iff₀ ha, mul_comm]
      nlinarith
    linarith
  linarith

/-- Paper (25): `E[X⁴] ≤ 9 σ⁴`. -/
theorem fourth_moment_ratio (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ha1 : 1 ≤ a) (hab : a ≤ 2 * b) :
    betaCentral4 a b ≤ 9 * (betaVar a b) ^ 2 := by
  have h := fourth_moment_ratio_le_nine a b ha hb ha1 hab
  have hp : 0 < (betaVar a b) ^ 2 := by
    unfold betaVar
    positivity
  exact (div_le_iff₀ hp).mp h

/-! ## Variance of a Dirichlet coordinate -/

theorem dirVar_eq (a : ℝ) (d : ℕ) :
    dirVar a d = (d - 1 : ℝ) / (d ^ 2 * (a * d + 1)) := rfl

theorem dirVar_eq_betaVar (a : ℝ) (d : ℕ) (ha : 0 < a) :
    dirVar a d = betaVar a ((d - 1 : ℝ) * a) := by
  unfold dirVar betaVar
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp
  · have hdd : (0 : ℝ) < d := by exact_mod_cast hd
    have hsum : a + (d - 1 : ℝ) * a = a * d := by
      have : ((d : ℝ) - 1) * a = a * d - a := by
        ring
      linarith
    rw [hsum]
    field_simp

/-- Variance lower bound `σ² ≥ 1/(4ad²)` for `d ≥ 2`, `a ≥ 1`. -/
theorem dirVar_lower (a : ℝ) (d : ℕ) (ha : 1 ≤ a) (hd : 2 ≤ d) :
    1 / (4 * a * d ^ 2) ≤ dirVar a d := by
  have ha0 : 0 < a := by linarith
  have hdd : 0 < d := by omega
  unfold dirVar
  have h1 : (d : ℝ) - 1 ≥ d / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h2 : a * d + 1 ≤ 2 * (a * d) := by
    have hd1 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hden1 : 0 < d ^ 2 * (a * d + 1) := by positivity
  have hden2 : 0 < d ^ 2 * (2 * (a * d)) := by positivity
  have key : (d : ℝ) / 2 / (d ^ 2 * (2 * (a * d))) = 1 / (4 * a * d ^ 2) := by
    field_simp
    ring
  calc 1 / (4 * a * d ^ 2)
      = (d : ℝ) / 2 / (d ^ 2 * (2 * (a * d))) := key.symm
    _ ≤ (d - 1 : ℝ) / (d ^ 2 * (a * d + 1)) := by
      rw [div_le_div_iff₀ hden2 hden1]
      have hA : (0 : ℝ) ≤ d / 2 := by nlinarith
      have hA' : (0 : ℝ) ≤ 2 * (a * d) := by positivity
      have hB : (d : ℝ) / 2 ≤ d - 1 := h1
      have hC : a * d + 1 ≤ 2 * (a * d) := h2
      have hmid : (d : ℝ) / 2 * (a * d + 1) ≤ d / 2 * (2 * (a * d)) :=
        mul_le_mul_of_nonneg_left hC hA
      have hright : (d : ℝ) / 2 * (2 * (a * d)) ≤ (d - 1) * (2 * (a * d)) :=
        mul_le_mul_of_nonneg_right hB hA'
      have hform1 : (d : ℝ) / 2 * (d ^ 2 * (a * d + 1))
          = d ^ 2 * (d / 2 * (a * d + 1)) := by ring
      have hform2 : (d - 1 : ℝ) * (d ^ 2 * (2 * (a * d)))
          = d ^ 2 * ((d - 1) * (2 * (a * d))) := by ring
      rw [hform1, hform2]
      have hd2 : (0 : ℝ) ≤ d ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) hd2

/-! ## Hölder consequence `E|X| ≥ σ/3` -/

/-- From Hölder `(E X²)³ ≤ (E|X|)² (E X⁴)`, `E X² = σ²` and `E X⁴ ≤ 9σ⁴`
we get `E|X| ≥ σ/3` (paper, after (25)). -/
theorem holder_abs_lower {σ e1 e2 e4 : ℝ} (hσ : 0 < σ) (he1 : 0 ≤ e1)
    (he2 : e2 = σ ^ 2) (he4 : e4 ≤ 9 * σ ^ 4) (hhold : e2 ^ 3 ≤ e1 ^ 2 * e4) :
    σ / 3 ≤ e1 := by
  have h1 : (σ ^ 2) ^ 3 ≤ e1 ^ 2 * e4 := by
    rw [← he2]; exact hhold
  have h2 : e1 ^ 2 * e4 ≤ e1 ^ 2 * (9 * σ ^ 4) :=
    mul_le_mul_of_nonneg_left he4 (sq_nonneg e1)
  have h3 : (σ ^ 2) ^ 3 ≤ e1 ^ 2 * (9 * σ ^ 4) := le_trans h1 h2
  have h4 : (σ ^ 2) ^ 3 = σ ^ 2 * σ ^ 4 := by ring
  rw [h4] at h3
  have h5 : σ ^ 2 ≤ 9 * e1 ^ 2 := by nlinarith [pow_pos hσ 4, sq_nonneg e1]
  have h6 : (σ : ℝ) ^ 2 ≤ (3 * e1) ^ 2 := by nlinarith
  have h7 : |σ| ≤ |3 * e1| := sq_le_sq.mp h6
  rw [abs_of_pos hσ, abs_of_nonneg (by nlinarith : (0:ℝ) ≤ 3 * e1)] at h7
  linarith

/-- The fourth moment of a `Beta(a,b)` law with `1 ≤ a ≤ 2b` forces
`E|X| ≥ σ/3` once Hölder is applied to its moments. -/
theorem beta_abs_moment_lower (a b : ℝ) (ha : 1 ≤ a) (hb : 0 < b)
    (hab : a ≤ 2 * b) {σ e1 : ℝ} (hσ : 0 < σ) (he1 : 0 ≤ e1)
    (hsig : betaVar a b = σ ^ 2)
    (hhold : (σ ^ 2) ^ 3 ≤ e1 ^ 2 * betaCentral4 a b) :
    σ / 3 ≤ e1 := by
  have ha0 : 0 < a := by linarith
  have hfourth := fourth_moment_ratio a b ha0 hb ha hab
  have he4 : betaCentral4 a b ≤ 9 * σ ^ 4 := by
    have hvsq : (betaVar a b) ^ 2 = σ ^ 4 := by
      rw [hsig]
      ring
    nlinarith [hfourth, hvsq]
  exact holder_abs_lower hσ he1 rfl he4 hhold

/-! ## Moment bounds driving Paley–Zygmund -/

/-- `E|X| ≥ σ/3 ≥ 1/(6d√a)` for a Dirichlet coordinate. -/
theorem abs_moment_scale (a : ℝ) (d : ℕ) (ha : 1 ≤ a) (hd : 2 ≤ d) :
    1 / (6 * d * Real.sqrt a) ≤ (1 / (3 : ℝ)) * Real.sqrt (dirVar a d) := by
  have ha0 : 0 < a := by linarith
  have hvar := dirVar_lower a d ha hd
  have hs2 : (1 / (2 * d * Real.sqrt a) : ℝ) ^ 2 = 1 / (4 * a * d ^ 2) := by
    have hsqr : Real.sqrt a ^ 2 = a := Real.sq_sqrt (le_of_lt ha0)
    have h : (2 * d * Real.sqrt a) ^ 2 = 4 * a * d ^ 2 := by
      rw [mul_pow, mul_pow, hsqr]
      norm_num
      ring
    rw [div_pow, one_pow, h]
  have hnn : (0 : ℝ) ≤ 1 / (2 * d * Real.sqrt a) := by positivity
  have hdir : 0 ≤ dirVar a d := by
    unfold dirVar
    refine div_nonneg ?_ ?_
    · have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
      have : (1 : ℝ) ≤ d := by linarith
      nlinarith
    · positivity
  have hle : (1 / (2 * d * Real.sqrt a) : ℝ) ≤ Real.sqrt (dirVar a d) := by
    rw [← Real.sqrt_sq hnn]
    exact Real.sqrt_le_sqrt (by rw [hs2]; exact hvar)
  have h3 : (1 / (2 * d * Real.sqrt a) : ℝ) / 3 = 1 / (6 * d * Real.sqrt a) := by
    field_simp
    ring
  have h4 : (1 / (6 * d * Real.sqrt a) : ℝ) ≤ Real.sqrt (dirVar a d) / 3 := by
    rw [← h3]
    exact div_le_div_of_nonneg_right hle (by norm_num)
  have h5 : Real.sqrt (dirVar a d) / 3 = (1 / (3 : ℝ)) * Real.sqrt (dirVar a d) := by
    ring
  linarith [h4, h5]

/-- `E Z ≥ 1/(12√a)` scaling for `Z = d_TV(P,u_d)`. -/
theorem ez_lower_scale (a : ℝ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    (d : ℝ) / 2 * (1 / (6 * d * Real.sqrt a)) = 1 / (12 * Real.sqrt a) := by
  field_simp
  norm_num

/-- `E Z² ≤ 1/(4a)` scaling for `Z = d_TV(P,u_d)`. -/
theorem ez2_upper_scale (a : ℝ) (d : ℕ) (ha : 1 ≤ a) (hd : 2 ≤ d) :
    (d : ℝ) / 4 * d * dirVar a d ≤ 1 / (4 * a) := by
  have hdd : 0 < d := by omega
  unfold dirVar
  have hform : (d : ℝ) / 4 * d * ((d - 1) / (d ^ 2 * (a * d + 1)))
      = (d - 1) / (4 * (a * d + 1)) := by
    field_simp
  rw [hform]
  have hden1 : 0 < 4 * (a * d + 1) := by positivity
  have hden2 : 0 < 4 * a := by positivity
  rw [div_le_div_iff₀ hden1 hden2]
  nlinarith

/-- The numerical envelope of Lemma 2: threshold `1/(24√a)`. -/
theorem lemma2_threshold (a : ℝ) : lemma2Threshold a = 1 / (24 * Real.sqrt a) := rfl

theorem lemma2_mass : q0 = (1 / 144 : ℝ) := rfl

/-- `(1/2)·(1/(12√a)) = 1/(24√a)`. -/
theorem half_ez_eq_threshold (a : ℝ) (_ha : 0 < a) :
    (1 / (2 : ℝ)) * (1 / (12 * Real.sqrt a)) = 1 / (24 * Real.sqrt a) := by
  rw [div_mul_div_comm, one_mul]
  congr 1
  ring

/-- Paley–Zygmund constant: `(1/(12√a))² / (4·1/(4a)) = 1/144`. -/
theorem paley_constant (a : ℝ) (ha : 0 < a) :
    ((1 / (12 * Real.sqrt a)) ^ 2 / (4 * (1 / (4 * a))) : ℝ) = 1 / 144 := by
  have hs2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (le_of_lt ha)
  have hne : (4 * (1 / (4 * a)) : ℝ) ≠ 0 := by positivity
  have h : (1 / (12 * Real.sqrt a) : ℝ) ^ 2 = (1 / 144) * (4 * (1 / (4 * a))) := by
    rw [div_pow, one_pow, mul_pow, hs2]
    norm_num
    field_simp
  rw [div_eq_iff hne]
  exact h

/-! ## Paley–Zygmund inequality (finite probability spaces) -/

/-- Weighted Cauchy–Schwarz for finite sums. -/
theorem sum_weighted_cauchy {n : ℕ} (w x y : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * (x i * y i)) ^ 2
      ≤ (∑ i, w i * (x i) ^ 2) * (∑ i, w i * (y i) ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun i => Real.sqrt (w i) * x i) (fun i => Real.sqrt (w i) * y i)
  have h1 : (∑ i : Fin n, (Real.sqrt (w i) * x i) ^ 2) = ∑ i, w i * (x i) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have h2 : (∑ i : Fin n, (Real.sqrt (w i) * y i) ^ 2) = ∑ i, w i * (y i) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have h3 : (∑ i : Fin n, (Real.sqrt (w i) * x i) * (Real.sqrt (w i) * y i))
      = ∑ i, w i * (x i * y i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Real.sqrt (w i) * x i * (Real.sqrt (w i) * y i) = w i * (x i * y i) := by
      rw [mul_assoc, ← mul_assoc (x i), mul_comm (x i) (Real.sqrt (w i)),
        mul_assoc (Real.sqrt (w i)), ← mul_assoc (Real.sqrt (w i)),
        Real.mul_self_sqrt (hw i)]
    exact this
  rw [h3, h1, h2] at h
  exact h

/-- Paley–Zygmund on a finite probability space.
If `Z ≥ 0`, `E Z ≥ m > 0` and `E Z² ≤ v`, then `P[Z ≥ m/2] ≥ m²/(4v)`. -/
theorem paley_zygmund_fin {n : ℕ} (w Z : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (_hZ : ∀ i, 0 ≤ Z i)
    {m v : ℝ} (hm : 0 < m) (hv : 0 < v)
    (hEZ : m ≤ ∑ i, w i * Z i) (hEZ2 : ∑ i, w i * (Z i) ^ 2 ≤ v) :
    m ^ 2 / (4 * v) ≤ ∑ i, if m / 2 ≤ Z i then w i else 0 := by
  classical
  set s := ∑ i, if m / 2 ≤ Z i then w i else 0 with hs
  set t1 := ∑ i, (if m / 2 ≤ Z i then w i * Z i else 0) with ht1
  set t2 := ∑ i, (if m / 2 ≤ Z i then 0 else w i * Z i) with ht2
  have htsplit : ∑ i, w i * Z i = t1 + t2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : m / 2 ≤ Z i <;> simp [h]
  have hpt : ∀ i, (if m / 2 ≤ Z i then 0 else w i * Z i)
      ≤ (if m / 2 ≤ Z i then 0 else (m / 2) * w i) := by
    intro i
    by_cases h : m / 2 ≤ Z i
    · simp [h]
    · simp [h]
      have : Z i < m / 2 := not_le.mp h
      nlinarith [hw i]
  have ht2_le : t2 ≤ (m / 2) * ∑ i, (if m / 2 ≤ Z i then 0 else w i) := by
    have hpt2 : ∀ i : Fin n, (if m / 2 ≤ Z i then 0 else (m / 2) * w i)
        = (m / 2) * (if m / 2 ≤ Z i then 0 else w i) := by
      intro i
      by_cases h : m / 2 ≤ Z i <;> simp [h]
    have hsum_le : (∑ i : Fin n, (if m / 2 ≤ Z i then 0 else w i * Z i))
        ≤ ∑ i : Fin n, (if m / 2 ≤ Z i then 0 else (m / 2) * w i) :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) fun i _ => hpt i
    have hrew : (∑ i : Fin n, (if m / 2 ≤ Z i then 0 else (m / 2) * w i))
        = (m / 2) * ∑ i : Fin n, (if m / 2 ≤ Z i then 0 else w i) := by
      conv_rhs => rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => hpt2 i
    rw [ht2, ← hrew]
    exact hsum_le
  have hcomp : (∑ i, (if m / 2 ≤ Z i then 0 else w i)) ≤ 1 := by
    have hcomb : ∀ i, (if m / 2 ≤ Z i then 0 else w i) + (if m / 2 ≤ Z i then w i else 0) = w i := by
      intro i
      by_cases h : m / 2 ≤ Z i <;> simp [h]
    have hsum : (∑ i, (if m / 2 ≤ Z i then 0 else w i))
        + (∑ i, (if m / 2 ≤ Z i then w i else 0)) = 1 := by
      rw [← Finset.sum_add_distrib]
      simp_rw [hcomb]
      exact hw1
    have hnn : (0 : ℝ) ≤ ∑ i, (if m / 2 ≤ Z i then w i else 0) :=
      Finset.sum_nonneg fun i _ => by
        by_cases h : m / 2 ≤ Z i
        · simp [h]; exact hw i
        · simp [h]
    linarith
  have ht2_le2 : t2 ≤ m / 2 := by
    have h0 : (0 : ℝ) ≤ m / 2 := div_nonneg (le_of_lt hm) (by norm_num)
    have hmul : (m / 2) * ∑ i, (if m / 2 ≤ Z i then 0 else w i) ≤ m / 2 := by
      have := mul_le_mul_of_nonneg_left hcomp h0
      simpa using this
    linarith
  have ht1_ge : (m / 2 : ℝ) ≤ t1 := by
    have : ∑ i, w i * Z i ≤ t1 + m / 2 := by nlinarith [htsplit, ht2_le2]
    nlinarith [hEZ]
  have hcs : t1 ^ 2 ≤ (∑ i, w i * (Z i) ^ 2) * s := by
    have hform : t1 = ∑ i, w i * (Z i * (if m / 2 ≤ Z i then (1:ℝ) else 0)) := by
      rw [ht1]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : m / 2 ≤ Z i <;> simp [h]
    have hform2 : s = ∑ i, w i * ((if m / 2 ≤ Z i then (1:ℝ) else 0) ^ 2) := by
      rw [hs]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : m / 2 ≤ Z i <;> simp [h]
    have hcs' := sum_weighted_cauchy w Z (fun i => if m / 2 ≤ Z i then (1:ℝ) else 0) hw
    rw [hform, hform2]
    exact hcs'
  have h4 : (m / 2) ^ 2 ≤ (∑ i, w i * (Z i) ^ 2) * s := by
    have hnn1 : (0 : ℝ) ≤ m / 2 := by positivity
    have hnn2 : 0 ≤ t1 := le_trans hnn1 ht1_ge
    have hsq : (m / 2) ^ 2 ≤ t1 ^ 2 := by
      have : |m / 2| ≤ |t1| := by
        rw [abs_of_nonneg hnn1, abs_of_nonneg hnn2]
        exact ht1_ge
      exact sq_le_sq.mpr this
    nlinarith [hcs]
  have h5 : (m / 2) ^ 2 ≤ v * s := by
    have hnn : 0 ≤ s := Finset.sum_nonneg fun i _ => by
      by_cases h : m / 2 ≤ Z i
      · simp [h]; exact hw i
      · simp [h]
    nlinarith [mul_le_mul_of_nonneg_right hEZ2 hnn]
  have h6 : m ^ 2 / 4 ≤ v * s := by
    have : (m / 2) ^ 2 = m ^ 2 / 4 := by ring
    rw [this] at h5
    exact h5
  have h7 : m ^ 2 / (4 * v) ≤ s := by
    rw [div_le_iff₀ (by positivity : 0 < (4 * v : ℝ))]
    nlinarith
  rw [hs]
  exact h7

/-- The Paley–Zygmund instance of Lemma 2 with the paper's constants. -/
theorem lemma2_paleyZygmund_fin {n : ℕ} (w Z : Fin n → ℝ) (a : ℝ) (ha : 1 ≤ a)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hZ : ∀ i, 0 ≤ Z i)
    (hEZ : 1 / (12 * Real.sqrt a) ≤ ∑ i, w i * Z i)
    (hEZ2 : ∑ i, w i * (Z i) ^ 2 ≤ 1 / (4 * a)) :
    (1 / 144 : ℝ) ≤ ∑ i, if 1 / (24 * Real.sqrt a) ≤ Z i then w i else 0 := by
  have ha0 : 0 < a := by linarith
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hm : 0 < (1 / (12 * Real.sqrt a) : ℝ) := by positivity
  have hv : 0 < (1 / (4 * a) : ℝ) := by positivity
  have hth := half_ez_eq_threshold a ha0
  have hval := paley_constant a ha0
  have h := paley_zygmund_fin w Z hw hw1 hZ hm hv hEZ hEZ2
  rw [hval] at h
  have hth2 : (1 / (12 * Real.sqrt a) : ℝ) / 2 = 1 / (24 * Real.sqrt a) := by
    have : (1 / (12 * Real.sqrt a) : ℝ) / 2 = (1 / 2) * (1 / (12 * Real.sqrt a)) := by
      ring
    rw [this, half_ez_eq_threshold a ha0]
  have hsets : (fun i : Fin n => if (1 / (12 * Real.sqrt a) : ℝ) / 2 ≤ Z i then w i else 0)
      = fun i : Fin n => if 1 / (24 * Real.sqrt a) ≤ Z i then w i else 0 := by
    funext i
    rw [hth2]
  rw [hsets] at h
  exact h

/-- Algebraic constants and a finite-probability Paley–Zygmund implication.
This legacy declaration is not the source Dirichlet-measure Lemma 2. -/
theorem lemma2 (d : ℕ) (a : ℝ) (hd : 2 ≤ d) (ha : 1 ≤ a) :
    lemma2Threshold a = 1 / (24 * Real.sqrt a)
    ∧ q0 = (1 / 144 : ℝ)
    ∧ 1 / (4 * a * d ^ 2) ≤ dirVar a d
    ∧ (∀ (n : ℕ) (w Z : Fin n → ℝ),
        (∀ i, 0 ≤ w i) →
        (∑ i, w i = 1) →
        (∀ i, 0 ≤ Z i) →
        (1 / (12 * Real.sqrt a) ≤ ∑ i, w i * Z i) →
        (∑ i, w i * (Z i) ^ 2 ≤ 1 / (4 * a)) →
        (1 / 144 : ℝ) ≤ ∑ i, if 1 / (24 * Real.sqrt a) ≤ Z i then w i else 0) := by
  refine ⟨rfl, rfl, dirVar_lower a d ha hd, ?_⟩
  intro n w Z hw hw1 hZ hEZ hEZ2
  exact lemma2_paleyZygmund_fin w Z a ha hw hw1 hZ hEZ hEZ2

/-- The key numerical content of Lemma 2 in one package. -/
theorem lemma2_main (d : ℕ) (a : ℝ) (hd : 2 ≤ d) (ha : 1 ≤ a) :
    q0 = (1 / 144 : ℝ) ∧ lemma2Threshold a = 1 / (24 * Real.sqrt a) ∧
    1 / (4 * a * d ^ 2) ≤ dirVar a d ∧
    (1 / (2 : ℝ)) * (1 / (12 * Real.sqrt a)) = 1 / (24 * Real.sqrt a) ∧
    ((1 / (12 * Real.sqrt a)) ^ 2 / (4 * (1 / (4 * a))) : ℝ) = 1 / 144 := by
  have ha0 : 0 < a := by linarith
  refine ⟨rfl, rfl, dirVar_lower a d ha hd, ?_, ?_⟩
  · exact half_ez_eq_threshold a ha0
  · exact paley_constant a ha0

end PUT
