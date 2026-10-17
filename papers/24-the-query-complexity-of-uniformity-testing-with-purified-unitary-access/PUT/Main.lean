import PUT.Basic
import PUT.Collision

/-!
# Numerical parameter lemmas for the proposed Theorem 1

There is an absolute `c > 0` such that for every `d ≥ 2` and `0 < ε < 1/2`,
any quantum algorithm distinguishing `u_d` from `d_TV(p,u_d) > ε` with
success probability at least `0.99` on every valid promised preparation
oracle has worst-case query complexity at least
`c · min(d^{1/3}/ε^{4/3}, √d/ε)`, even with controlled `U` and `U†`.

This module contains only algebraic prerequisites, not the operational
query lower bound. In particular `theorem1` below is a legacy name for
positivity of the printed target. The available prerequisites include
the two cutoff regimes of (S4.p5), the substitution `a = (48ε)⁻²`, the
nine-fold amplification, and a constant absorption inequality with `c₀ = 1/3000`. This constant is
not established as a query lower-bound constant after progress/amplification
losses. The complete actual measure/operator/circuit assembly is in `PUT.Paper`;
its principal theorem retains the precisely disclosed standard inputs.
-/

noncomputable section
namespace PUT

/-- Proof constant positivity. -/
theorem c0_pos : 0 < c0 := by
  unfold c0
  norm_num

/-- Parameter regime `1 ≤ a ≤ d`: choose `A = (d a²)^{1/3}`. -/
def cutoffLow (a d : ℝ) : ℝ := (d * a ^ 2) ^ (1 / 3 : ℝ)

/-- Parameter regime `a ≥ d`: choose `A = a`. -/
def cutoffHigh (a _d : ℝ) : ℝ := a

/-- Low-regime first balance: `A/d ≤ 1` when `a ≤ d`. -/
theorem low_regime_div (a d : ℝ) (ha : 0 < a) (hd : 0 < d) (h : a ≤ d) :
    cutoffLow a d / d ≤ 1 := by
  unfold cutoffLow
  have h3 : d * a ^ 2 ≤ d ^ 3 := by
    nlinarith [sq_nonneg (d - a), sq_nonneg a, mul_nonneg (le_of_lt ha) (le_of_lt hd)]
  have h13 : (0 : ℝ) < 1 / 3 := by norm_num
  have hcube : (d * a ^ 2) ^ (1 / 3 : ℝ) ≤ d := by
    have h1 : (d * a ^ 2) ^ (1 / 3 : ℝ) ≤ (d ^ (3 : ℕ)) ^ (1 / 3 : ℝ) :=
      (Real.rpow_le_rpow_iff (by positivity) (by positivity) h13).2 h3
    have h2 : (d ^ (3 : ℕ)) ^ (1 / 3 : ℝ) = d := by
      have hd3eq : (d ^ (3 : ℕ)) = d ^ ((3 : ℝ)) := (Real.rpow_natCast d 3).symm
      rw [hd3eq, ← Real.rpow_mul (le_of_lt hd)]
      have : (3 : ℝ) * (1 / 3) = 1 := by norm_num
      rw [this, Real.rpow_one]
    linarith
  exact (div_le_one hd).2 hcube

/-- Low-regime second balance: `A^{3/2}/(a√d) = 1`. -/
theorem low_regime_mid (a d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    cutoffLow a d ^ (3 / 2 : ℝ) / (a * Real.sqrt d) = 1 := by
  unfold cutoffLow
  have hstep1 : ((d * a ^ 2) ^ (1 / 3 : ℝ)) ^ (3 / 2 : ℝ)
      = (d * a ^ 2) ^ ((1 / 3 : ℝ) * (3 / 2 : ℝ)) := by
    rw [← Real.rpow_mul (by positivity : 0 ≤ d * a ^ 2)]
  have h32 : (1 / 3 : ℝ) * (3 / 2) = 1 / 2 := by norm_num
  have hstep1' : ((d * a ^ 2) ^ (1 / 3 : ℝ)) ^ (3 / 2 : ℝ) = (d * a ^ 2) ^ (1 / 2 : ℝ) := by
    rw [hstep1, h32]
  have hstep2 : (d * a ^ 2) ^ (1 / 2 : ℝ) = a * Real.sqrt d := by
    have hsplit : (d * a ^ 2) ^ (1 / 2 : ℝ) = d ^ (1 / 2 : ℝ) * (a ^ 2) ^ (1 / 2 : ℝ) :=
      Real.mul_rpow (le_of_lt hd) (sq_nonneg a)
    rw [hsplit]
    have hsq : (a ^ 2) ^ (1 / 2 : ℝ) = a := by
      have hnat : (a ^ 2) = a ^ ((2 : ℝ)) := (Real.rpow_natCast a 2).symm
      rw [hnat, ← Real.rpow_mul (le_of_lt ha)]
      have : (2 : ℝ) * (1 / 2) = 1 := by norm_num
      rw [this, Real.rpow_one]
    rw [hsq, Real.sqrt_eq_rpow]
    ring
  rw [hstep1', hstep2]
  field_simp

/-- Low-regime third balance: `A/√(ad) ≤ 1` when `a ≤ d`. -/
theorem low_regime_last (a d : ℝ) (ha : 0 < a) (hd : 0 < d) (h : a ≤ d) :
    cutoffLow a d / Real.sqrt (a * d) ≤ 1 := by
  unfold cutoffLow
  have hA : 0 ≤ (d * a ^ 2) ^ (1 / 3 : ℝ) := by positivity
  have hSpos : 0 < Real.sqrt (a * d) := by positivity
  have hS : 0 ≤ Real.sqrt (a * d) := le_of_lt hSpos
  have hstep : (d * a ^ 2) ^ (1 / 3 : ℝ) ≤ Real.sqrt (a * d) := by
    refine (Real.rpow_le_rpow_iff hA hS (by norm_num : (0 : ℝ) < 6)).1 ?_
    have hL : ((d * a ^ 2) ^ (1 / 3 : ℝ)) ^ ((6 : ℝ)) = (d * a ^ 2) ^ ((2 : ℝ)) := by
      rw [← Real.rpow_mul (by positivity : 0 ≤ d * a ^ 2)]
      have : (1 / 3 : ℝ) * 6 = 2 := by norm_num
      rw [this]
    have hR : (Real.sqrt (a * d)) ^ ((6 : ℝ)) = (a * d) ^ ((3 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ a * d)]
      have : (1 / 2 : ℝ) * 6 = 3 := by norm_num
      rw [this]
    rw [hL, hR]
    have h2 : (d * a ^ 2) ^ ((2 : ℝ)) = ((d * a ^ 2) ^ (2 : ℕ)) := Real.rpow_natCast _ 2
    have h3 : (a * d) ^ ((3 : ℝ)) = ((a * d) ^ (3 : ℕ)) := Real.rpow_natCast _ 3
    rw [h2, h3]
    have e1 : (d * a ^ 2) ^ 2 = d ^ 2 * a ^ 4 := by ring
    have e2 : (a * d) ^ 3 = a ^ 3 * d ^ 3 := by ring
    rw [e1, e2]
    nlinarith [sq_nonneg (d - a), mul_nonneg (le_of_lt ha) (le_of_lt hd),
      mul_nonneg (sq_nonneg a) (sq_nonneg d),
      mul_nonneg (pow_nonneg (le_of_lt ha) 3) (pow_nonneg (le_of_lt hd) 2),
      pow_nonneg (le_of_lt ha) 4, pow_nonneg (le_of_lt hd) 3]
  exact (div_le_one hSpos).2 hstep

/-- Packaged low-regime balance of (S4.p5). -/
theorem low_regime (a d : ℝ) (ha : 0 < a) (hd : 0 < d) (h : a ≤ d) :
    cutoffLow a d / d ≤ 1 ∧
      cutoffLow a d ^ (3 / 2 : ℝ) / (a * Real.sqrt d) = 1 ∧
        cutoffLow a d / Real.sqrt (a * d) ≤ 1 :=
  ⟨low_regime_div a d ha hd h, low_regime_mid a d ha hd, low_regime_last a d ha hd h⟩

/-- High-regime choice `A = a`. -/
theorem high_regime (a d : ℝ) (_ha : 0 < a) (_hd : 0 < d) (_h : d ≤ a) :
    cutoffHigh a d = a := rfl

/-- High-regime first term: `√(1+A/d) = O(√(a/d))` with `A = a`, `a ≥ d`. -/
theorem high_term1 (a d : ℝ) (_ha : 0 < a) (hd : 0 < d) (h : d ≤ a) :
    Real.sqrt (1 + cutoffHigh a d / d) ≤ Real.sqrt 2 * Real.sqrt (a / d) := by
  unfold cutoffHigh
  have h1 : 1 + a / d ≤ 2 * (a / d) := by
    have : 1 ≤ a / d := (one_le_div hd).2 h
    nlinarith
  have h2 : Real.sqrt (1 + a / d) ≤ Real.sqrt (2 * (a / d)) := Real.sqrt_le_sqrt h1
  have h3 : Real.sqrt (2 * (a / d)) = Real.sqrt 2 * Real.sqrt (a / d) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

/-- High-regime second term: `A^{3/2}/(a√d) = √(a/d)` with `A = a`. -/
theorem high_term2 (a d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    cutoffHigh a d ^ (3 / 2 : ℝ) / (a * Real.sqrt d) = Real.sqrt (a / d) := by
  unfold cutoffHigh
  have hstep : a ^ (3 / 2 : ℝ) = a * Real.sqrt a := by
    have : a ^ (3 / 2 : ℝ) = a ^ ((1 : ℝ) + 1 / 2) := by norm_num
    rw [this, Real.rpow_add ha, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hstep]
  have h1 : a * Real.sqrt a / (a * Real.sqrt d) = Real.sqrt a / Real.sqrt d := by
    field_simp
  have h2 : Real.sqrt a / Real.sqrt d = Real.sqrt (a / d) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      Real.div_rpow (le_of_lt ha) (le_of_lt hd)]
  rw [h1, h2]

/-- High-regime third term: `A/√(ad) = √(a/d)` with `A = a`. -/
theorem high_term3 (a d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    cutoffHigh a d / Real.sqrt (a * d) = Real.sqrt (a / d) := by
  unfold cutoffHigh
  have h1 : a / Real.sqrt (a * d) = Real.sqrt a / Real.sqrt d := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.mul_rpow (le_of_lt ha) (le_of_lt hd)]
    field_simp
    have ha_half : a = a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add ha]
      have : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
      rw [this, Real.rpow_one]
    nth_rewrite 1 [ha_half]
    rw [pow_two, Real.sqrt_eq_rpow]
  have h2 : Real.sqrt a / Real.sqrt d = Real.sqrt (a / d) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      Real.div_rpow (le_of_lt ha) (le_of_lt hd)]
  rw [h1, h2]

/-- High-regime: each term of `lemma1RHS` is `O(√(a/d))`. -/
theorem high_regime_bound (a d : ℝ) (ha : 0 < a) (hd : 0 < d) (h : d ≤ a) :
    lemma1RHS (cutoffHigh a d) a d ≤ 20 * (Real.sqrt 2 + 2) * Real.sqrt (a / d) := by
  unfold lemma1RHS
  have t1 := high_term1 a d ha hd h
  have t2 := high_term2 a d ha hd
  have t3 := high_term3 a d ha hd
  have hs : 0 ≤ Real.sqrt (a / d) := by positivity
  have hsq2 : 0 ≤ Real.sqrt 2 := by positivity
  nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) hs,
    mul_nonneg hsq2 hs, mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs]

/-- Nine independent repetitions drive the error below `(q₀/8)²`. -/
theorem amplification :
    (2 ^ 9 : ℝ) * ((1 : ℝ) / 100) ^ 5 < ((q0 : ℝ) / 8) ^ 2 := by
  unfold q0
  norm_num

/-- The printed powers of `48` satisfy `48^{4/3} ≤ 3000`. -/
theorem pow48_le : (48 : ℝ) ^ (4 / 3 : ℝ) ≤ 3000 := by
  have h1 : (48 : ℝ) ^ (4 / 3 : ℝ) = 48 * (48 : ℝ) ^ (1 / 3 : ℝ) := by
    have hadd : (4 / 3 : ℝ) = 1 + 1 / 3 := by norm_num
    rw [hadd, Real.rpow_add (show (0 : ℝ) < 48 by norm_num), Real.rpow_one]
  have h2 : (48 : ℝ) ^ (1 / 3 : ℝ) ≤ 4 := by
    have h : (48 : ℝ) ^ (1 / 3 : ℝ) ≤ (64 : ℝ) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    have h64 : (64 : ℝ) ^ (1 / 3 : ℝ) = 4 := by
      conv_rhs => rw [← Real.rpow_one (4 : ℝ)]
      have e : (64 : ℝ) = ((4 : ℝ) ^ (3 : ℕ)) := by norm_num
      rw [e]
      have e2 : ((4 : ℝ) ^ (3 : ℕ)) = (4 : ℝ) ^ ((3 : ℝ)) := (Real.rpow_natCast 4 3).symm
      rw [e2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (4 : ℝ))]
      have : (3 : ℝ) * (1 / 3) = 1 := by norm_num
      rw [this]
    linarith
  rw [h1]
  nlinarith

/-- Hence `c₀ = 1/3000` is dominated by `48^{-4/3}`. -/
theorem c0_le_pow : (c0 : ℝ) ≤ (48 : ℝ) ^ ((-4 / 3 : ℝ)) := by
  unfold c0
  have hrew : (48 : ℝ) ^ ((-4 / 3 : ℝ)) = ((48 : ℝ) ^ (4 / 3 : ℝ))⁻¹ := by
    rw [show ((-4 / 3 : ℝ)) = -(4 / 3 : ℝ) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 48)]
  rw [hrew]
  have hpos : (0 : ℝ) < (48 : ℝ) ^ (4 / 3 : ℝ) := by positivity
  rw [one_div_le (by norm_num : (0 : ℝ) < 3000) (inv_pos.mpr hpos)]
  rw [one_div, inv_inv]
  exact pow48_le

/-- If `α ≤ β` and `x, y ≥ 0`, then `α · min x y ≤ min (α x) (β y)`. -/
theorem min_absorb (x y α β : ℝ) (hy : 0 ≤ y) (hα : 0 < α) (hβ : α ≤ β) :
    α * min x y ≤ min (α * x) (β * y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    refine le_min le_rfl ?_
    nlinarith [mul_nonneg (le_of_lt hα) hy]
  · rw [min_eq_right h]
    refine le_min ?_ ?_
    · nlinarith [mul_nonneg (le_of_lt hα) (le_of_lt hα)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hβ) hy]

/-- Dirichlet scale `a = (48ε)⁻²` substitutes into
`min(d^{1/3} a^{2/3}, √(ad)) = min(48^{-4/3} d^{1/3} ε^{-4/3}, 48^{-1} √d/ε)`. -/
theorem substitution (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    min (d ^ (1 / 3 : ℝ) * (dirichletScale ε) ^ (2 / 3 : ℝ))
        (Real.sqrt (d * dirichletScale ε))
      = min ((48 : ℝ) ^ ((-4 / 3 : ℝ)) * (d ^ (1 / 3 : ℝ) * ε ^ ((-4 / 3 : ℝ))))
          ((48 : ℝ) ^ ((-1 : ℝ)) * (Real.sqrt d / ε)) := by
  have h48 : 0 < 48 * ε := by positivity
  have hs : dirichletScale ε = (48 * ε) ^ ((-2 : ℝ)) := by
    unfold dirichletScale
    have hcast : ((-2 : ℤ) : ℝ) = (-2 : ℝ) := by norm_num
    rw [← Real.rpow_intCast (48 * ε) (-2 : ℤ), hcast]
  rw [hs]
  have hpow : ((48 * ε) ^ ((-2 : ℝ))) ^ (2 / 3 : ℝ) = (48 * ε) ^ ((-4 / 3 : ℝ)) := by
    rw [← Real.rpow_mul (le_of_lt h48)]
    have : ((-2 : ℝ) * (2 / 3 : ℝ)) = ((-4 / 3 : ℝ)) := by ring
    rw [this]
  rw [hpow]
  have hsplit : (48 * ε) ^ ((-4 / 3 : ℝ)) = (48 : ℝ) ^ ((-4 / 3 : ℝ)) * ε ^ ((-4 / 3 : ℝ)) := by
    have h1 : (48 * ε) ^ ((-4 / 3 : ℝ)) = ((48 * ε) ^ ((4 / 3 : ℝ)))⁻¹ := by
      have e : ((-4 / 3 : ℝ)) = -(4 / 3 : ℝ) := by ring
      rw [e, Real.rpow_neg (le_of_lt h48)]
    have h2 : ((48 * ε) ^ ((4 / 3 : ℝ))) = (48 : ℝ) ^ ((4 / 3 : ℝ)) * ε ^ ((4 / 3 : ℝ)) :=
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 48) (le_of_lt hε)
    have h3 : ((48 : ℝ) ^ ((4 / 3 : ℝ)) * ε ^ ((4 / 3 : ℝ)))⁻¹
        = ((48 : ℝ) ^ ((4 / 3 : ℝ)))⁻¹ * (ε ^ ((4 / 3 : ℝ)))⁻¹ := mul_inv _ _
    have h4 : ((48 : ℝ) ^ ((4 / 3 : ℝ)))⁻¹ = (48 : ℝ) ^ ((-4 / 3 : ℝ)) := by
      have e : ((-4 / 3 : ℝ)) = -(4 / 3 : ℝ) := by ring
      rw [e]
      exact (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 48) _).symm
    have h5 : (ε ^ ((4 / 3 : ℝ)))⁻¹ = ε ^ ((-4 / 3 : ℝ)) := by
      have e : ((-4 / 3 : ℝ)) = -(4 / 3 : ℝ) := by ring
      rw [e]
      exact (Real.rpow_neg (le_of_lt hε) _).symm
    rw [h1, h2, h3, h4, h5]
  rw [hsplit]
  have hL : d ^ (1 / 3 : ℝ) * ((48 : ℝ) ^ ((-4 / 3 : ℝ)) * ε ^ ((-4 / 3 : ℝ)))
      = (48 : ℝ) ^ ((-4 / 3 : ℝ)) * (d ^ (1 / 3 : ℝ) * ε ^ ((-4 / 3 : ℝ))) := by ring
  have hR : Real.sqrt (d * (48 * ε) ^ ((-2 : ℝ)))
      = (48 : ℝ) ^ ((-1 : ℝ)) * (Real.sqrt d / ε) := by
    have hs2 : (48 * ε) ^ ((-2 : ℝ)) = ((48 * ε) ^ (2 : ℕ))⁻¹ := by
      have h : (48 * ε) ^ ((-2 : ℝ)) = ((48 * ε) ^ ((2 : ℝ)))⁻¹ := by
        rw [show ((-2 : ℝ)) = -(2 : ℝ) by ring, Real.rpow_neg (le_of_lt h48)]
      rw [← Real.rpow_natCast]
      exact h
    rw [hs2]
    have hprod : d * ((48 * ε) ^ (2 : ℕ))⁻¹ = d / (48 * ε) ^ (2 : ℕ) := by
      rw [div_eq_mul_inv]
    rw [hprod]
    have hsq : Real.sqrt (d / (48 * ε) ^ (2 : ℕ)) = Real.sqrt d / Real.sqrt ((48 * ε) ^ (2 : ℕ)) :=
      Real.sqrt_div (by positivity : 0 ≤ d) _
    rw [hsq]
    have hsqrt : Real.sqrt ((48 * ε) ^ (2 : ℕ)) = 48 * ε :=
      Real.sqrt_sq (le_of_lt h48)
    rw [hsqrt]
    have : (48 : ℝ) ^ ((-1 : ℝ)) * (Real.sqrt d / ε) = (48 : ℝ)⁻¹ * (√d / ε) := by
      rw [Real.rpow_neg_one]
    rw [this]
    field_simp
  rw [hL, hR]

/-- The adversary lower bound at scale `a = (48ε)⁻²` dominates
`c₀ · min(d^{1/3} ε^{-4/3}, √d/ε)`.  This is the real inequality that makes
`c₀ = 1/3000` work. -/
theorem regime_implies_target (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    theorem1Bound c0 d ε
      ≤ min (d ^ (1 / 3 : ℝ) * (dirichletScale ε) ^ (2 / 3 : ℝ))
          (Real.sqrt (d * dirichletScale ε)) := by
  rw [substitution d ε hd hε]
  have hα : 0 < (48 : ℝ) ^ ((-4 / 3 : ℝ)) := by positivity
  have hβ : (48 : ℝ) ^ ((-4 / 3 : ℝ)) ≤ (48 : ℝ) ^ ((-1 : ℝ)) := by
    have : ((-4 / 3 : ℝ)) ≤ ((-1 : ℝ)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 48) this
  have hab := min_absorb (d ^ (1 / 3 : ℝ) * ε ^ ((-4 / 3 : ℝ))) (Real.sqrt d / ε)
    ((48 : ℝ) ^ ((-4 / 3 : ℝ))) ((48 : ℝ) ^ ((-1 : ℝ)))
    (by positivity) hα hβ
  have hc0 : (c0 : ℝ) ≤ (48 : ℝ) ^ ((-4 / 3 : ℝ)) := c0_le_pow
  have hpos : 0 ≤ min (d ^ (1 / 3 : ℝ) * ε ^ ((-4 / 3 : ℝ))) (Real.sqrt d / ε) := by positivity
  unfold theorem1Bound
  nlinarith [mul_nonneg (le_of_lt hα) hpos, mul_nonneg (sub_nonneg.mpr hc0) hpos]

/-- Legacy reflexive parameter identity. This is not equation (21), since
it contains no query count or asymptotic lower bound. -/
theorem regime_assembly (a d : ℝ) (_ha : 1 ≤ a) (_hd : 2 ≤ d) :
    min (d ^ (1 / 3 : ℝ) * a ^ (2 / 3 : ℝ)) (Real.sqrt (a * d))
      = min (d ^ (1 / 3 : ℝ) * a ^ (2 / 3 : ℝ)) (Real.sqrt (a * d)) := rfl

/-- Positivity of the printed target expression (legacy name). This does
not prove source Theorem 1 or assert anything about algorithms/queries. -/
theorem theorem1 :
    0 < c0 ∧
    ∀ (d : ℕ) (ε : ℝ), 2 ≤ d → 0 < ε → ε < 1 / 2 →
      0 < theorem1Bound c0 d ε := by
  refine ⟨c0_pos, ?_⟩
  intro d ε hd hε hε'
  have hd0 : (0 : ℝ) < d := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le h2 (by exact_mod_cast hd)
  have hmin : 0 < min (d ^ (1 / 3 : ℝ) * ε ^ ((-4 / 3 : ℝ))) (Real.sqrt d / ε) := by
    apply lt_min
    · positivity
    · positivity
  unfold theorem1Bound
  exact mul_pos c0_pos hmin

end PUT
