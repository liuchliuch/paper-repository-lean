import Paper14.Basic
import Paper14.StrongMixing
/-!
# Scale limit for Theorem 4 hypothesis (ii) (paper S4.p12)

`n((1-α/n)^{-2} - 1) → 2α` as `n → ∞`, for fixed `α > 0`.
Also `ρ_n = (1-α/n)^2 → 1`, and the moment `n(ρ_n^{-1}-1)` is eventually bounded.
-/
open Filter Topology Real
namespace Paper14

/-- Algebraic rewrite: `(1-x)^{-2} - 1 = x*(2-x)/(1-x)^2`. -/
theorem scale_kernel (x : ℝ) (hx : x ≠ 1) :
    ((1 - x) ^ (2 : ℝ))⁻¹ - 1 = x * (2 - x) / (1 - x) ^ 2 :=
  one_sub_sq_inv_sub_one x hx

/-- For `0 < α < n`: `n((1-α/n)^{-2}-1) = α(2-α/n)/(1-α/n)^2`. -/
theorem scale_closed_form {α : ℝ} {n : ℕ} (hα : 0 < α) (hn : (0:ℝ) < n)
    (hαn : α < n) :
    (n:ℝ) * (((1 - α / n) ^ (2 : ℝ))⁻¹ - 1)
      = α * (2 - α / n) / (1 - α / n) ^ 2 := by
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt hn
  have hx : α / n ≠ 1 := by
    intro h
    have : α = n := by field_simp [hn0] at h; linarith
    linarith
  have h1 : ((1 - α / n) ^ (2 : ℝ))⁻¹ - 1
      = (α / n) * (2 - α / n) / (1 - α / n) ^ 2 := scale_kernel (α / n) hx
  calc (n:ℝ) * (((1 - α / n) ^ (2 : ℝ))⁻¹ - 1)
      = (n:ℝ) * ((α / n) * (2 - α / n) / (1 - α / n) ^ 2) := by rw [h1]
    _ = α * (2 - α / n) / (1 - α / n) ^ 2 := by
        have : (n:ℝ) * ((α / n) * (2 - α / n) / (1 - α / n) ^ 2)
            = α * (2 - α / n) / (1 - α / n) ^ 2 := by
          field_simp [hn0]
        exact this

/-- `α/n → 0`. -/
theorem tendsto_alpha_div_nat {α : ℝ} :
    Tendsto (fun n : ℕ => α / (n:ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have : Tendsto (fun n : ℕ => α * (n:ℝ)⁻¹) atTop (𝓝 (α * 0)) :=
    Tendsto.const_mul α h
  simpa [div_eq_mul_inv, mul_zero] using this

/-- Paper S4.p12: `n((1-α/n)^{-2} - 1) → 2α`. -/
theorem scaleLimit {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n : ℕ =>
      ((n:ℝ) * (((1 - α / n) ^ (2 : ℝ))⁻¹ - 1))) atTop (𝓝 (2 * α)) := by
  have hform : (fun n : ℕ => ((n:ℝ) * (((1 - α / n) ^ (2 : ℝ))⁻¹ - 1)))
      =ᶠ[atTop] (fun n : ℕ => α * (2 - α / n) / (1 - α / n) ^ 2) := by
    filter_upwards [eventually_gt_atTop ⌈α⌉₊] with n hn
    have hαn : α < n := lt_of_le_of_lt (Nat.le_ceil α)
      (Nat.cast_lt.mpr hn)
    have hn0 : (0:ℝ) < n := lt_of_le_of_lt (le_of_lt hα) hαn
    exact scale_closed_form hα hn0 hαn
  have hnum : Tendsto (fun n : ℕ => α * (2 - α / (n:ℝ))) atTop (𝓝 (α * 2)) := by
    have h2 : Tendsto (fun n : ℕ => 2 - α / (n:ℝ)) atTop (𝓝 (2 - 0)) :=
      Tendsto.const_sub 2 tendsto_alpha_div_nat
    have h3 : Tendsto (fun n : ℕ => α * (2 - α / (n:ℝ))) atTop (𝓝 (α * (2 - 0))) :=
      Tendsto.const_mul α h2
    simpa using h3
  have hbase : Tendsto (fun n : ℕ => 1 - α / (n:ℝ)) atTop (𝓝 1) := by
    simpa using (Tendsto.const_sub 1 tendsto_alpha_div_nat)
  have hden : Tendsto (fun n : ℕ => (1 - α / (n:ℝ)) ^ (2:ℕ)) atTop (𝓝 1) := by
    simpa [one_pow] using hbase.pow 2
  have hquot : Tendsto (fun n : ℕ =>
      α * (2 - α / (n:ℝ)) / (1 - α / (n:ℝ)) ^ 2) atTop (𝓝 (α * 2 / 1)) := by
    refine Tendsto.div hnum hden ?_
    norm_num
  apply (tendsto_congr' hform).mpr
  simpa [mul_comm] using hquot

/-- `ρ_n = (1-α/n)^2 → 1`. -/
theorem scale_rho_tendsto_one {α : ℝ} (_hα : 0 < α) :
    Tendsto (fun n : ℕ => (1 - α / (n:ℝ)) ^ 2) atTop (𝓝 1) := by
  have hbase : Tendsto (fun n : ℕ => 1 - α / (n:ℝ)) atTop (𝓝 1) := by
    simpa using (Tendsto.const_sub 1 tendsto_alpha_div_nat)
  simpa [one_pow] using hbase.pow 2

/-- Theorem 4 hypothesis (ii): `n(ρ_n^{-1}-1)` is eventually bounded,
because it converges to `2α`. -/
theorem scale_moment_bound {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (n:ℝ) * (((1 - α / (n:ℝ)) ^ (2 : ℝ))⁻¹ - 1) ≤ C := by
  have hconv := scaleLimit hα
  have hev : ∀ᶠ n : ℕ in atTop,
      dist ((n:ℝ) * (((1 - α / (n:ℝ)) ^ (2 : ℝ))⁻¹ - 1)) (2 * α) < 1 :=
    hconv (Metric.ball_mem_nhds _ (by norm_num : (0:ℝ) < 1))
  refine ⟨2 * α + 1, ?_⟩
  filter_upwards [hev] with n hn
  have habs : |((n:ℝ) * (((1 - α / (n:ℝ)) ^ (2 : ℝ))⁻¹ - 1) - 2 * α)| < 1 := by
    simpa [Real.dist_eq] using hn
  have hle : ((n:ℝ) * (((1 - α / (n:ℝ)) ^ (2 : ℝ))⁻¹ - 1)) - 2 * α ≤ 1 :=
    le_of_lt (lt_of_le_of_lt (le_abs_self _) habs)
  linarith

end Paper14
