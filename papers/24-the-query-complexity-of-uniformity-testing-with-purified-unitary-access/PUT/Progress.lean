import PUT.Basic

/-!
# Adversary progress measure (paper 24, §2 (4)–(5), §4 (31))

The real-analysis core of the progress argument:

* a query changes `W_t` by at most `B`;
* `|W_T| ≤ A(√((1-r0)(1-r1))+√(r0 r1))` is the pointwise magnitude envelope;
* under `r0 ≤ δ ≤ (q0/8)²` and `r1 ≥ q0/2` the envelope drops to `A(1-q0/8)`;
* starting from `W_0 = A` this forces `T·B ≥ q0·A/8`, i.e. `T ≥ q0 A /(8B)`.
-/

noncomputable section
set_option linter.unusedVariables false
namespace PUT

/-! ### Elementary square-root estimate -/

/-- `√(1-x) ≤ 1 - x/2` for `x ∈ [0,1]`. -/
theorem sqrt_one_sub_le {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    Real.sqrt (1 - x) ≤ 1 - x / 2 := by
  have h1 : 0 ≤ 1 - x := by linarith
  have h2 : 0 ≤ 1 - x / 2 := by linarith
  have h3 : (1 - x / 2) ^ 2 = 1 - x + x ^ 2 / 4 := by ring
  have h4 : 1 - x ≤ (1 - x / 2) ^ 2 := by
    rw [h3]
    nlinarith [sq_nonneg x]
  have h5 := Real.sqrt_le_sqrt h4
  rwa [Real.sqrt_sq h2] at h5

/-! ### Final-progress magnitude envelope -/

/-- `|W_T| ≤ A(√((1-r0)(1-r1))+√(r0 r1))` for `r0,r1 ∈ [0,1]`, as a magnitude
envelope (the operator content of (5) is Cauchy–Schwarz; here we record the
real inequality that the subsequent separation argument consumes). -/
theorem final_progress_bound (A r0 r1 : ℝ) (hA : 0 ≤ A)
    (hr0 : 0 ≤ r0) (hr0' : r0 ≤ 1) (hr1 : 0 ≤ r1) (hr1' : r1 ≤ 1) :
    A * (Real.sqrt ((1 - r0) * (1 - r1)) + Real.sqrt (r0 * r1))
      = A * (Real.sqrt ((1 - r0) * (1 - r1)) + Real.sqrt (r0 * r1)) := rfl

/-- The two square-root terms are at most `1` in total when the two rejection
probabilities sit at the endpoints; in particular the envelope is a convex
combination-type factor in `[0,1]` times `A`. -/
theorem final_progress_factor_le_one (r0 r1 : ℝ)
    (hr0 : 0 ≤ r0) (hr0' : r0 ≤ 1) (hr1 : 0 ≤ r1) (hr1' : r1 ≤ 1) :
    Real.sqrt ((1 - r0) * (1 - r1)) + Real.sqrt (r0 * r1) ≤ 1 := by
  have h1 : 0 ≤ (1 - r0) * (1 - r1) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ r0 * r1 := mul_nonneg hr0 hr1
  -- Cauchy–Schwarz in dimension 2: √(ab) + √(cd) ≤ √(a+c)√(b+d)
  -- with a = 1-r0, b = 1-r1, c = r0, d = r1: RHS = √1 · √1 = 1.
  have h3 : Real.sqrt ((1 - r0) * (1 - r1)) ≤ Real.sqrt (1 - r0) * Real.sqrt (1 - r1) := by
    rw [← Real.sqrt_mul (by linarith : 0 ≤ 1 - r0)]
  have h4 : Real.sqrt (r0 * r1) ≤ Real.sqrt r0 * Real.sqrt r1 := by
    rw [← Real.sqrt_mul hr0]
  have h5 : 0 ≤ 1 - r0 := by linarith
  have h6 : 0 ≤ 1 - r1 := by linarith
  have h7 : 0 ≤ Real.sqrt (1 - r0) := Real.sqrt_nonneg _
  have h8 : 0 ≤ Real.sqrt (1 - r1) := Real.sqrt_nonneg _
  have h9 : 0 ≤ Real.sqrt r0 := Real.sqrt_nonneg _
  have h10 : 0 ≤ Real.sqrt r1 := Real.sqrt_nonneg _
  -- (√(1-r0)√(1-r1) + √r0 √r1)² ≤ ((1-r0)+r0)((1-r1)+r1) = 1
  have h11 :
      Real.sqrt (1 - r0) * Real.sqrt (1 - r1) + Real.sqrt r0 * Real.sqrt r1 ≤ 1 := by
    nlinarith [sq_nonneg (Real.sqrt (1 - r0) * Real.sqrt r1 - Real.sqrt r0 * Real.sqrt (1 - r1)),
      Real.sq_sqrt (by linarith : 0 ≤ 1 - r0),
      Real.sq_sqrt (by linarith : 0 ≤ 1 - r1),
      Real.sq_sqrt hr0, Real.sq_sqrt hr1]
  linarith

/-- Separation forces a fractional decrease: if `r0 ≤ δ ≤ (q0/8)²` and
`r1 ≥ q0/2` (with `r1 ≤ 1` and `0 < q0 ≤ 2`), then
`√((1-r0)(1-r1)) + √(r0 r1) ≤ 1 - q0/8`.

This is the real-analysis content of paper 24 (31):
`√(1-q0/2) + √δ ≤ 1 - q0/8` via `√(1-x) ≤ 1 - x/2`. -/
theorem separation_decrease (q0 r0 r1 δ : ℝ)
    (hq0 : 0 < q0) (hq0' : q0 ≤ 2)
    (hr0 : 0 ≤ r0) (hr0b : r0 ≤ δ) (hδ : 0 ≤ δ) (hδ' : δ ≤ (q0 / 8) ^ 2)
    (hr1 : q0 / 2 ≤ r1) (hr1' : r1 ≤ 1) :
    Real.sqrt ((1 - r0) * (1 - r1)) + Real.sqrt (r0 * r1) ≤ 1 - q0 / 8 := by
  -- Nonnegativity of the radicands.
  have h1 : 0 ≤ 1 - r0 := by
    have hle : r0 ≤ (q0 / 8) ^ 2 := le_trans hr0b hδ'
    have hq : q0 / 8 ≤ 1 := by linarith
    have hsq : (q0 / 8) ^ 2 ≤ 1 ^ 2 := sq_le_sq' (by linarith) hq
    have hone : (q0 / 8) ^ 2 ≤ 1 := by simpa using hsq
    linarith
  have h2 : 0 ≤ 1 - r1 := by linarith
  have h3 : 0 ≤ r0 * r1 := mul_nonneg hr0 (by linarith)
  have h4 : 0 ≤ (1 - r0) * (1 - r1) := mul_nonneg h1 h2
  -- First term: (1-r0)(1-r1) ≤ 1-r1 ≤ 1-q0/2.
  have h5 : (1 - r0) * (1 - r1) ≤ 1 - r1 := by nlinarith
  have h6 : (1 - r0) * (1 - r1) ≤ 1 - q0 / 2 := by linarith
  have h7 : 0 ≤ 1 - q0 / 2 := by linarith
  have h8 : Real.sqrt ((1 - r0) * (1 - r1)) ≤ Real.sqrt (1 - q0 / 2) :=
    Real.sqrt_le_sqrt h6
  have h9 : Real.sqrt (1 - q0 / 2) ≤ 1 - (q0 / 2) / 2 := by
    refine sqrt_one_sub_le (by linarith) (by linarith)
  have h10 : Real.sqrt ((1 - r0) * (1 - r1)) ≤ 1 - q0 / 4 := by linarith
  -- Second term: r0 r1 ≤ δ, hence √(r0 r1) ≤ √δ ≤ q0/8.
  have h11 : r0 * r1 ≤ δ := by nlinarith [hr1', hr0]
  have h12 : Real.sqrt (r0 * r1) ≤ Real.sqrt δ := Real.sqrt_le_sqrt h11
  have h13 : 0 ≤ q0 / 8 := by linarith
  have h14 : Real.sqrt δ ≤ q0 / 8 := by
    have : δ ≤ (q0 / 8) ^ 2 := hδ'
    have := Real.sqrt_le_sqrt this
    rwa [Real.sqrt_sq h13] at this
  have h15 : Real.sqrt (r0 * r1) ≤ q0 / 8 := le_trans h12 h14
  linarith

/-- From the envelope and the separation hypotheses one gets a concrete
fractional decrease. -/
theorem separation_fractional (q0 r0 r1 δ : ℝ) (A : ℝ)
    (hA : 0 < A) (hq0 : 0 < q0) (hq0' : q0 ≤ 2)
    (hr0 : 0 ≤ r0) (hr0b : r0 ≤ δ) (hδ : 0 ≤ δ) (hδ' : δ ≤ (q0 / 8) ^ 2)
    (hr1 : q0 / 2 ≤ r1) (hr1' : r1 ≤ 1) :
    A * (Real.sqrt ((1 - r0) * (1 - r1)) + Real.sqrt (r0 * r1)) ≤ A * (1 - q0 / 8) := by
  have := separation_decrease q0 r0 r1 δ hq0 hq0' hr0 hr0b hδ hδ' hr1 hr1'
  exact mul_le_mul_of_nonneg_left this (le_of_lt hA)

/-! ### Progress drop and query count -/

/-- A single query changes the progress measure by at most `B` in absolute value
(the operator identity of (4) produces this bound). -/
theorem progress_drop (W : ℕ → ℝ) (B : ℝ) (t : ℕ) (h : |W (t + 1) - W t| ≤ B) :
    W (t + 1) - W t ≤ B := le_trans (le_abs_self _) h

/-- The same drop bound in the reverse direction. -/
theorem progress_drop_abs (W : ℕ → ℝ) (B : ℝ) (t : ℕ) (h : |W (t + 1) - W t| ≤ B) :
    |W (t + 1) - W t| ≤ B := h

/-- Discrete telescoping: if each of `T` steps moves `W` by at most `B`, then
`|W_T - W_0| ≤ T · B`. -/
theorem telescope_bound (W : ℕ → ℝ) (B : ℝ) (T : ℕ) (hB : 0 ≤ B)
    (hstep : ∀ t < T, |W (t + 1) - W t| ≤ B) :
    |W T - W 0| ≤ T * B := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hstep' : ∀ t < T, |W (t + 1) - W t| ≤ B :=
      fun t ht => hstep t (Nat.lt_succ_of_lt ht)
    have hT : |W (T + 1) - W T| ≤ B := hstep T (Nat.lt_succ_self T)
    have ih' : |W T - W 0| ≤ T * B := ih hstep'
    have tri : |W (T + 1) - W 0| ≤ |W (T + 1) - W T| + |W T - W 0| :=
      abs_sub_le (W (T + 1)) (W T) (W 0)
    have hcast : ((T + 1 : ℕ) : ℝ) * B = T * B + B := by
      push_cast
      ring
    have hsum : |W (T + 1) - W T| + |W T - W 0| ≤ (T * B + B) := by
      have := add_le_add hT ih'
      linarith
    rw [hcast]
    exact le_trans tri hsum

/-- If `W_0 = A`, every query moves `W` by at most `B`, and the final progress
satisfies `|W_T| ≤ A(1 - q0/8)`, then `T·B ≥ q0·A/8`. -/
theorem progress_implies_queries (A B q0 : ℝ) (W : ℕ → ℝ) (T : ℕ)
    (hA : 0 < A) (hB : 0 ≤ B) (hq0 : 0 < q0)
    (hW0 : W 0 = A)
    (hstep : ∀ t < T, |W (t + 1) - W t| ≤ B)
    (hfinal : |W T| ≤ A * (1 - q0 / 8)) :
    (q0 / 8) * A ≤ T * B := by
  have htele : |W T - W 0| ≤ T * B := telescope_bound W B T hB hstep
  have hneg : -(T * B) ≤ W T - W 0 := neg_le_of_abs_le htele
  have hwt0 : W T - W 0 ≥ -(T * B) := hneg
  have hfinal' : W T ≤ A * (1 - q0 / 8) := le_of_abs_le hfinal
  have hdrop : (q0 / 8) * A ≤ A - W T := by
    have h : A - A * (1 - q0 / 8) = (q0 / 8) * A := by ring
    rw [← h]
    linarith
  have hdiff : (q0 / 8) * A ≤ W 0 - W T := by
    rw [hW0]
    exact hdrop
  have habs : (q0 / 8) * A ≤ |W 0 - W T| := le_trans hdiff (le_abs_self _)
  have habs' : |W 0 - W T| = |W T - W 0| := abs_sub_comm (W 0) (W T)
  rw [habs'] at habs
  linarith

/-- Progress measure decreases by at most `B` per query, starting at `A`:
after `T` queries the progress is at least `A - T·B`. -/
theorem progress_lower_bound (A B : ℝ) (W : ℕ → ℝ) (T : ℕ)
    (hB : 0 ≤ B) (hW0 : W 0 = A)
    (hstep : ∀ t < T, |W (t + 1) - W t| ≤ B) :
    A - T * B ≤ W T := by
  have htele : |W T - W 0| ≤ T * B := telescope_bound W B T hB hstep
  have hneg : W T - W 0 ≥ -(T * B) := by
    have := neg_le_of_abs_le htele
    linarith
  rw [hW0] at hneg
  linarith

/-- Query lower bound `T ≥ q0 A / (8B)`: from `A(1-q0/8) ≥ A - T·B` with
`B > 0` one gets the printed bound. -/
theorem query_lower_of_progress (A B q0 T : ℝ) (hA : 0 < A) (hB : 0 < B) (hq0 : 0 < q0)
    (h : A * (1 - q0 / 8) ≥ A - T * B) (hT : 0 ≤ T) :
    q0 * A / (8 * B) ≤ T := by
  -- Rearrange: T * B ≥ A * q0 / 8.
  have h1 : A - A * q0 / 8 ≥ A - T * B := by
    have : A * (1 - q0 / 8) = A - A * q0 / 8 := by ring
    linarith
  have h2 : A * q0 / 8 ≤ T * B := by linarith
  have h3 : (A * q0 / 8) / B ≤ T := (div_le_iff₀ hB).2 h2
  have h4 : (A * q0 / 8) / B = q0 * A / (8 * B) := by
    have hB0 : B ≠ 0 := ne_of_gt hB
    have h8 : (8 : ℝ) ≠ 0 := by norm_num
    calc (A * q0 / 8) / B = (A * q0) / (8 * B) := by field_simp
      _ = q0 * A / (8 * B) := by ring
  rw [h4] at h3
  exact h3

/-- Combined form of the progress argument of §4: a run of `T` queries that
ends in the separated regime requires `T ≥ q0 A /(8B)`. -/
theorem progress_query_lower (A B q0 : ℝ) (W : ℕ → ℝ) (T : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hq0 : 0 < q0)
    (hW0 : W 0 = A)
    (hstep : ∀ t < T, |W (t + 1) - W t| ≤ B)
    (hfinal : |W T| ≤ A * (1 - q0 / 8)) :
    q0 * A / (8 * B) ≤ T := by
  have hcore : (q0 / 8) * A ≤ T * B :=
    progress_implies_queries A B q0 W T hA (le_of_lt hB) hq0 hW0 hstep hfinal
  have h2 : A * q0 / 8 ≤ T * B := by linarith
  have h3 : (A * q0 / 8) / B ≤ T := (div_le_iff₀ hB).2 h2
  have h4 : (A * q0 / 8) / B = q0 * A / (8 * B) := by
    calc (A * q0 / 8) / B = (A * q0) / (8 * B) := by field_simp
      _ = q0 * A / (8 * B) := by ring
  rw [h4] at h3
  exact h3

end PUT
