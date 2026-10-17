import Paper26.MultiscaleRefinement
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The algorithm's least dyadic power is exactly the ceiling of the real
base-two logarithm in Theorem 1.3. This identifies the actual integer stage
count with the source L0, without an asymptotic replacement. -/
noncomputable section
namespace Paper26.DyadicSchedule
open MultiscaleRefinement

def sourceStages (d : ℕ) (ε : ℝ) : ℕ :=
  ⌈Real.log (16*(d : ℝ)/ε)/Real.log 2⌉₊

theorem dyadicStages_eq_logCeil (d : ℕ) {e : ℝ} (he : 0 < e) (hd : 0 < d) :
    dyadicStages d e = ⌈Real.log ((d : ℝ)/e)/Real.log 2⌉₊ := by
  have hp : 0 < (d : ℝ)/e := div_pos (Nat.cast_pos.mpr hd) he
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply Nat.le_antisymm
  · have hc : Real.log ((d : ℝ)/e)/Real.log 2 ≤
        (⌈Real.log ((d : ℝ)/e)/Real.log 2⌉₊ : ℝ) := Nat.le_ceil _
    have hpow : (d : ℝ)/e ≤ (2 : ℝ)^⌈Real.log ((d : ℝ)/e)/Real.log 2⌉₊ :=
      (Real.le_pow_iff_log_le hp (by norm_num)).mpr ((div_le_iff₀ hlog).mp hc)
    unfold dyadicStages
    exact Nat.find_min' _ hpow
  · apply Nat.ceil_le.mpr
    exact (div_le_iff₀ hlog).mpr
      ((Real.le_pow_iff_log_le hp (by norm_num)).mp (dyadicStages_spec d e))

theorem sourceStages_eq (d : ℕ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) :
    dyadicStages d (ε/16) = sourceStages d ε := by
  rw [dyadicStages_eq_logCeil d (by positivity) hd]
  have he : (d : ℝ)/(ε/16) = 16*(d : ℝ)/ε := by ring
  rw [he]
  rfl

theorem sourceStages_pos (d : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hd : 0 < d) :
    0 < sourceStages d ε := by
  rw [← sourceStages_eq d hε hd]
  apply dyadicStages_pos d (by positivity)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

theorem terminal_scale (d : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hd : 0 < d) :
    (d : ℝ)*((2 : ℝ)^sourceStages d ε)⁻¹ ≤ ε/16 ∧
      ε/(32*(d : ℝ)) < ((2 : ℝ)^sourceStages d ε)⁻¹ := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h := dyadicStages_window d (show 0<ε/16 by positivity) (show ε/16<d by linarith)
  rw [sourceStages_eq d hε hd] at h
  have heq : ε/(32*(d : ℝ)) = (ε/16)/(2*(d : ℝ)) := by field_simp; ring
  exact ⟨h.1, by rw [heq]; exact h.2⟩

end Paper26.DyadicSchedule
