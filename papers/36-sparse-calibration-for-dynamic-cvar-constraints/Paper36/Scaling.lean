import Paper36.Target
import Mathlib.Analysis.Asymptotics.Defs

/-! An explicit fixed-instance logarithmic square-root envelope for the actual
target. This establishes the near-square-root growth claimed in Theorem 4.2,
in addition to the already proved target/n limit. -/
namespace Paper36.Scaling
open Filter Asymptotics
noncomputable section

/-- A concrete coefficient for the target's soft-square-root growth. -/
def coefficient (c A ν M : ℝ) : ℝ := c * (Target.G₀ A M + Target.gamma₀ A ν M)

lemma target_log_sqrt_bound {c A ν M : ℝ} (hc : 0 ≤ c) (hA : 0 < A)
    (hM : 0 < M) (hν : 0 ≤ ν) {n : ℕ} (hn : 1 ≤ n) :
    Target.target c A ν M n ≤ coefficient c A ν M * Real.sqrt (n : ℝ) *
      (1 + Real.log (n : ℝ)) := by
  have hn0 : n ≠ 0 := by omega
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_nonneg hnr
  have hg : 0 ≤ Target.G₀ A M := Real.sqrt_nonneg _
  have hγ : 0 ≤ Target.gamma₀ A ν M := by unfold Target.gamma₀ Target.G₀; positivity
  have ht := Target.G_tangent hA hM hν hlog
  have hprod : (n : ℝ) * (A + ν * Real.log (n : ℝ)) * (M + Real.log (n : ℝ)) =
      (n : ℝ) * ((A + ν * Real.log (n : ℝ)) * (M + Real.log (n : ℝ))) := by ring
  rw [Target.target, if_neg hn0, hprod, Real.sqrt_mul (Nat.cast_nonneg n)]
  calc
    _ ≤ c * (Real.sqrt (n : ℝ) * (Target.G₀ A M + Target.gamma₀ A ν M * Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _)) hc
    _ ≤ coefficient c A ν M * Real.sqrt (n : ℝ) * (1 + Real.log (n : ℝ)) := by
      unfold coefficient
      have hb : Target.G₀ A M + Target.gamma₀ A ν M * Real.log (n : ℝ) ≤
          (Target.G₀ A M + Target.gamma₀ A ν M) * (1 + Real.log (n : ℝ)) := by
        nlinarith [mul_nonneg hg hlog]
      have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg hc (Real.sqrt_nonneg (n : ℝ)))
      nlinarith

/-- Fixed parameters give T_K = O(sqrt K (1+log K)), with an explicit coefficient above. -/
theorem target_isBigO {c A ν M : ℝ} (hc : 0 ≤ c) (hA : 0 < A)
    (hM : 0 < M) (hν : 0 ≤ ν) :
    (fun n : ℕ => Target.target c A ν M n) =O[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ) * (1 + Real.log (n : ℝ))) := by
  apply Asymptotics.IsBigO.of_bound (coefficient c A ν M)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hg : 0 ≤ Real.sqrt (n : ℝ) * (1 + Real.log (n : ℝ)) := by
    have hl := Real.log_nonneg hnr
    positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Target.target_nonneg hc n), abs_of_nonneg hg,
    mul_assoc] using target_log_sqrt_bound hc hA hM hν hn

end
end Paper36.Scaling
