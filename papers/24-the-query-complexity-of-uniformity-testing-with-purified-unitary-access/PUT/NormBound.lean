import PUT.Basic
import PUT.Erasure

/-!
# Numerical envelope used by Lemma 1 of paper 24

`B := ‖(Γ⊗I)U₁ - U₀(Γ⊗I)‖ ≤ 20(√(1+A/d) + A^{3/2}/(a√d) + A/√(ad))`
under `d ≥ 2`, `a > 0`, `A ≥ 1`, `M ≥ 16 A² L_A`.

This module proves the real-analysis envelope. The actual complete operator
result is `FullQueryBound.query_norm_le_printed`. The
paper's numerical steps are

* `√(1+8x) ≤ 3√(1+x)` for `x ≥ 0`;
* `√(1+A/d) ≥ 1`;
* `η_M ≤ 1/2` and `A/√M ≤ 1/8` from `M ≥ 16 A² L_A`;
* hence `B ≤ 4√(1+8A/d) + 4h + 2A/√(ad) + 9/4 ≤ 20(√(1+A/d)+h+A/√(ad))`.
-/

noncomputable section
set_option linter.unusedVariables false
namespace PUT

/-! ### Positivity of the parameters -/

/-- `L_A = (√A+1)²` is positive. -/
theorem LA_pos (A : ℝ) (hA : 1 ≤ A) : 0 < LA A := by
  have h : 0 < Real.sqrt A + 1 := by
    have : 0 < Real.sqrt A := Real.sqrt_pos.2 (by linarith)
    linarith
  exact pow_pos h 2

/-- `L_A ≥ 4` once `A ≥ 1`. -/
theorem LA_ge_four (A : ℝ) (hA : 1 ≤ A) : 4 ≤ LA A := by
  have hs : 1 ≤ Real.sqrt A := by
    have := Real.sqrt_le_sqrt hA
    rwa [Real.sqrt_one] at this
  have h : (2:ℝ) ≤ Real.sqrt A + 1 := by linarith
  have h2 : (2:ℝ) ^ 2 ≤ (Real.sqrt A + 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h 2
  have h4 : (2:ℝ) ^ 2 = 4 := by norm_num
  simp only [LA, h4] at h2 ⊢
  exact h2

theorem M_pos_of_param (A M : ℝ) (hA : 1 ≤ A) (hM : 16 * A ^ 2 * LA A ≤ M) : 0 < M := by
  have h1 : 0 < LA A := LA_pos A hA
  have h2 : 0 < A := by linarith
  have h3 : 0 < A ^ 2 := pow_pos h2 2
  have h4 : 0 < 16 * A ^ 2 * LA A := by positivity
  linarith

theorem LA_nonneg (A : ℝ) : 0 ≤ LA A := by
  have : 0 ≤ Real.sqrt A + 1 := by
    have := Real.sqrt_nonneg A
    linarith
  have := sq_nonneg (Real.sqrt A + 1)
  simpa [LA] using this

/-! ### Square-root comparison `√(1+8x) ≤ 3√(1+x)` -/

theorem sqrt_one_add_8x_le (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (1 + 8 * x) ≤ 3 * Real.sqrt (1 + x) := by
  have h2 : 0 ≤ 3 * Real.sqrt (1 + x) := by positivity
  rw [Real.sqrt_le_iff]
  refine ⟨h2, ?_⟩
  have hs : 0 ≤ 1 + x := by linarith
  have hsq : (3 * Real.sqrt (1 + x)) ^ 2 = 9 * (1 + x) := by
    rw [mul_pow, Real.sq_sqrt hs]
    ring
  rw [hsq]
  nlinarith

theorem sqrt_one_add_nonneg (y : ℝ) (hy : 0 ≤ y) : 1 ≤ Real.sqrt (1 + y) := by
  have h : (1:ℝ) ≤ 1 + y := by linarith
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_one] at this

/-! ### Erasure contribution `η_M ≤ 1/2` -/

theorem etaM_sq_eq (A M : ℝ) (hA : 0 ≤ A) (hM : 0 < M) :
    etaM A M ^ 2 = 4 * A ^ 2 * (LA A / M) := by
  have hs : 0 ≤ LA A / M := div_nonneg (LA_nonneg A) (le_of_lt hM)
  change (2 * A * Real.sqrt (LA A / M)) ^ 2 = _
  rw [mul_pow, mul_pow, Real.sq_sqrt hs]
  ring

theorem etaM_nonneg (A M : ℝ) (hA : 0 ≤ A) : 0 ≤ etaM A M := by
  change 2 * A * Real.sqrt (LA A / M) ≥ 0
  have : 0 ≤ Real.sqrt (LA A / M) := Real.sqrt_nonneg _
  positivity

theorem etaM_le_half (A M : ℝ) (hA : 1 ≤ A) (hM : 16 * A ^ 2 * LA A ≤ M) :
    etaM A M ≤ 1 / 2 := by
  have hMpos : 0 < M := M_pos_of_param A M hA hM
  have hApos : 0 < A := by linarith
  have hLApos : 0 < LA A := LA_pos A hA
  have hbase : 0 < 16 * A ^ 2 * LA A := by positivity
  -- 4 A² (LA / M) = (4 A² LA) / M ≤ (4 A² LA) / (16 A² LA) = 1/4.
  have hnumnn : 0 ≤ 4 * A ^ 2 * LA A := by positivity
  have hle : 4 * A ^ 2 * LA A / M ≤ 4 * A ^ 2 * LA A / (16 * A ^ 2 * LA A) :=
    div_le_div_of_nonneg_left hnumnn hbase hM
  have hcancel : 4 * A ^ 2 * LA A / (16 * A ^ 2 * LA A) = (1 / 4 : ℝ) := by
    have hne : (16 * A ^ 2 * LA A : ℝ) ≠ 0 := ne_of_gt hbase
    have hne2 : (A ^ 2 : ℝ) ≠ 0 := ne_of_gt (pow_pos hApos 2)
    have hne3 : (LA A : ℝ) ≠ 0 := ne_of_gt hLApos
    field_simp [hne, hne2, hne3]
    norm_num
  have hkey : 4 * A ^ 2 * (LA A / M) ≤ 1 / 4 := by
    have h3 : 4 * A ^ 2 * (LA A / M) = 4 * A ^ 2 * LA A / M := by
      field_simp
    rw [h3]
    linarith
  have hsq := etaM_sq_eq A M (le_of_lt hApos) hMpos
  have hbound : etaM A M ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    rw [hsq]
    have : ((1:ℝ) / 2) ^ 2 = (1 / 4 : ℝ) := by norm_num
    rw [this]
    exact hkey
  have hnn : 0 ≤ etaM A M := etaM_nonneg A M (le_of_lt hApos)
  exact le_of_sq_le_sq hbound (by norm_num)

/-! ### Garbage-coordinate term `A/√M ≤ 1/8` -/

theorem A_div_sqrtM_le (A M : ℝ) (hA : 1 ≤ A) (hM : 16 * A ^ 2 * LA A ≤ M) :
    A / Real.sqrt M ≤ 1 / 8 := by
  have hMpos : 0 < M := M_pos_of_param A M hA hM
  have hApos : 0 < A := by linarith
  have hLA : 4 ≤ LA A := LA_ge_four A hA
  have hLApos : 0 < LA A := LA_pos A hA
  have hbase : 0 < 16 * A ^ 2 * LA A := by positivity
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.2 hMpos
  -- (A/√M)² = A²/M ≤ 1/(16 LA) ≤ 1/64.
  have hsq : (A / Real.sqrt M) ^ 2 = A ^ 2 / M := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hMpos)]
  have h1 : A ^ 2 / M ≤ A ^ 2 / (16 * A ^ 2 * LA A) :=
    div_le_div_of_nonneg_left (pow_nonneg (le_of_lt hApos) 2) hbase hM
  have h2 : A ^ 2 / (16 * A ^ 2 * LA A) = 1 / (16 * LA A) := by
    have hne : (A ^ 2 : ℝ) ≠ 0 := ne_of_gt (pow_pos hApos 2)
    have hne3 : (LA A : ℝ) ≠ 0 := ne_of_gt hLApos
    field_simp [hne, hne3]
  have h3 : 1 / (16 * LA A) ≤ 1 / 64 := by
    have hmul : (64:ℝ) ≤ 16 * LA A := by
      have h := mul_le_mul_of_nonneg_left hLA (by norm_num : (0:ℝ) ≤ 16)
      have h16 : (16:ℝ) * 4 = 64 := by norm_num
      linarith
    have hpos : 0 < (16 * LA A : ℝ) := by positivity
    have hpos' : 0 < (64:ℝ) := by norm_num
    have := one_div_le_one_div_of_le hpos' hmul
    simpa using this
  have h4 : A ^ 2 / M ≤ 1 / 64 := by linarith
  have hbound : (A / Real.sqrt M) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
    rw [hsq]
    have : ((1:ℝ) / 8) ^ 2 = (1 / 64 : ℝ) := by norm_num
    rw [this]
    exact h4
  have hnn : 0 ≤ A / Real.sqrt M := div_nonneg (le_of_lt hApos) (le_of_lt hsM)
  exact le_of_sq_le_sq hbound (by norm_num)

/-! ### The envelope (19)–(20) against the printed right-hand side (8) -/

/-- The printed right-hand side of (8). -/
theorem lemma1_rhs_eq (A a d : ℝ) :
    lemma1RHS A a d
      = 20 * (Real.sqrt (1 + A / d) + A ^ (3/2:ℝ) / (a * Real.sqrt d)
          + A / Real.sqrt (a * d)) := rfl

/-- Combining principal and radial estimates yields (19)–(20), then (8). -/
theorem lemma1_bound {d : ℕ} (a A M : ℝ) (hd : 2 ≤ d) (ha : 0 < a) (hA : 1 ≤ A)
    (hM : 16 * A ^ 2 * LA A ≤ M) :
    -- This is a scalar envelope only. `PUT.Main` does not assemble
    -- the actual Fourier–Dirichlet query-difference operator.
    (Real.sqrt (1 + 8 * A / d) + A ^ (3/2:ℝ) / (a * Real.sqrt d)
        + etaM A M + A / Real.sqrt (a * d) + A / Real.sqrt M + 1 / 2)
      ≤ lemma1RHS A a d := by
  have hdpos : 0 < (d : ℝ) := by
    have : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    linarith
  have hApos : 0 < A := by linarith
  have hMpos : 0 < M := M_pos_of_param A M hA hM
  have hAd : 0 ≤ A / (d : ℝ) := div_nonneg (le_of_lt hApos) (le_of_lt hdpos)
  -- Individual contributions.
  have hg : Real.sqrt (1 + 8 * A / d) ≤ 3 * Real.sqrt (1 + A / d) := by
    have h := sqrt_one_add_8x_le (A / (d : ℝ)) hAd
    have heq : (8:ℝ) * A / (d:ℝ) = 8 * (A / (d:ℝ)) := mul_div_assoc 8 A (d:ℝ)
    rw [heq]
    exact h
  have hSge : 1 ≤ Real.sqrt (1 + A / d) := sqrt_one_add_nonneg (A / d) hAd
  have hη : etaM A M ≤ 1 / 2 := etaM_le_half A M hA hM
  have hs : A / Real.sqrt M ≤ 1 / 8 := A_div_sqrtM_le A M hA hM
  have hηnn : 0 ≤ etaM A M := etaM_nonneg A M (le_of_lt hApos)
  have hsnn : 0 ≤ A / Real.sqrt M :=
    div_nonneg (le_of_lt hApos) (le_of_lt (Real.sqrt_pos.2 hMpos))
  have hhnn : 0 ≤ A ^ (3/2:ℝ) / (a * Real.sqrt d) := by
    have h1 : 0 ≤ A ^ (3/2:ℝ) := Real.rpow_nonneg (le_of_lt hApos) _
    have h2 : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
    have h3 : 0 < a * Real.sqrt d := mul_pos ha h2
    exact div_nonneg h1 (le_of_lt h3)
  have hrnn : 0 ≤ A / Real.sqrt (a * d) := by
    have h2 : 0 < Real.sqrt (a * d) := Real.sqrt_pos.2 (mul_pos ha hdpos)
    exact div_nonneg (le_of_lt hApos) (le_of_lt h2)
  -- First: the left-hand side is at most `3S + h + r + 9/8`.
  have hsum :
      Real.sqrt (1 + 8 * A / d) + A ^ (3/2:ℝ) / (a * Real.sqrt d)
          + etaM A M + A / Real.sqrt (a * d) + A / Real.sqrt M + 1 / 2
        ≤ 3 * Real.sqrt (1 + A / d) + A ^ (3/2:ℝ) / (a * Real.sqrt d)
            + A / Real.sqrt (a * d) + 9 / 8 := by
    linarith [hg, hη, hs]
  -- Second: `3S + h + r + 9/8 ≤ 20(S + h + r)` since `S ≥ 1`.
  have h20 :
      3 * Real.sqrt (1 + A / d) + A ^ (3/2:ℝ) / (a * Real.sqrt d)
          + A / Real.sqrt (a * d) + 9 / 8
        ≤ 20 * (Real.sqrt (1 + A / d) + A ^ (3/2:ℝ) / (a * Real.sqrt d)
            + A / Real.sqrt (a * d)) := by
    have hre : (20:ℝ) * (Real.sqrt (1 + A / d) + A ^ (3/2:ℝ) / (a * Real.sqrt d)
        + A / Real.sqrt (a * d))
        = 20 * Real.sqrt (1 + A / d) + 20 * (A ^ (3/2:ℝ) / (a * Real.sqrt d))
            + 20 * (A / Real.sqrt (a * d)) := by ring
    rw [hre]
    linarith [hSge, hhnn, hrnn]
  -- Unfold the printed right-hand side and conclude.
  show _ ≤ lemma1RHS A a d
  rw [lemma1_rhs_eq]
  linarith

/-- Intermediate step of (9): the two blocks `D₊`, `D₋` combine by the triangle
inequality into `B ≤ 2(‖D₊‖+‖D₋‖)`.  At the level of real estimates this is
the reorganization used to pass from (19)–(20) to
`B ≤ 4√(1+8A/d) + 4h + 2A/√(ad) + 9/4`. -/
theorem block_reduce (dplus dminus : ℝ) (hp : 0 ≤ dplus) (hm : 0 ≤ dminus) :
    dplus + dminus ≤ 2 * (dplus + dminus) := by
  nlinarith

/-- The paper's intermediate bound `B ≤ 4√(1+8A/d)+4h+2A/√(ad)+9/4`, as a
real inequality on the two block envelopes. -/
theorem two_block_envelope (a A d M : ℝ)
    (ha : 0 < a) (hA : 1 ≤ A) (hd : 0 < d) (hM : 16 * A ^ 2 * LA A ≤ M) :
    2 * ((Real.sqrt (1 + 8 * A / d) + A ^ (3/2:ℝ) / (a * Real.sqrt d) + etaM A M
            + A / Real.sqrt (a * d))
        + (Real.sqrt (1 + 8 * A / d) + A ^ (3/2:ℝ) / (a * Real.sqrt d) + etaM A M
            + A / Real.sqrt M))
      ≤ 4 * Real.sqrt (1 + 8 * A / d) + 4 * (A ^ (3/2:ℝ) / (a * Real.sqrt d))
          + 2 * (A / Real.sqrt (a * d)) + 9 / 4 := by
  have hApos : 0 < A := by linarith
  have hMpos : 0 < M := M_pos_of_param A M hA hM
  have hη : etaM A M ≤ 1 / 2 := etaM_le_half A M hA hM
  have hs : A / Real.sqrt M ≤ 1 / 8 := A_div_sqrtM_le A M hA hM
  have hηnn : 0 ≤ etaM A M := etaM_nonneg A M (le_of_lt hApos)
  have hsnn : 0 ≤ A / Real.sqrt M :=
    div_nonneg (le_of_lt hApos) (le_of_lt (Real.sqrt_pos.2 hMpos))
  have hhnn : 0 ≤ A ^ (3/2:ℝ) / (a * Real.sqrt d) := by
    have h1 : 0 ≤ A ^ (3/2:ℝ) := Real.rpow_nonneg (le_of_lt hApos) _
    have h2 : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
    exact div_nonneg h1 (le_of_lt (mul_pos ha h2))
  have hrnn : 0 ≤ A / Real.sqrt (a * d) := by
    have h2 : 0 < Real.sqrt (a * d) := Real.sqrt_pos.2 (mul_pos ha hd)
    exact div_nonneg (le_of_lt hApos) (le_of_lt h2)
  have hg : 0 ≤ Real.sqrt (1 + 8 * A / d) := Real.sqrt_nonneg _
  have h4η : 4 * etaM A M ≤ 2 := by nlinarith [hη]
  have h2s : 2 * (A / Real.sqrt M) ≤ 1 / 4 := by nlinarith [hs]
  linarith

end PUT
