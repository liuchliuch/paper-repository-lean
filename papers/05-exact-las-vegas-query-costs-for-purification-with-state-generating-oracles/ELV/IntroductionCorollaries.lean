import ELV.UnrestrictedOptimum
import ELV.AdmissibleOptimum

/-! Direct operational consequences in introduction S1.p6. The remainder
bound is uniform on the entire positive-gap interval and therefore gives
C_adm = 1/(2 delta^2) - 1/2 + O(delta^2) as delta tends to zero from above. -/
noncomputable section
namespace ELV.Costs

/-- The concrete positive gap used in the introductory example. -/
def quarterGap : Gap := ⟨1/4,by norm_num,by norm_num⟩

lemma quarterGap_mu : quarterGap.mu = Real.sqrt 3/2 := by
  apply (sq_eq_sq₀ quarterGap.mu_nonneg (by positivity)).mp
  rw [quarterGap.mu_sq,div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)]
  norm_num [quarterGap]

/-- The two actual minimax values in S1.p6, for every nonzero workspace. -/
theorem costs_at_quarter (n : ℕ) [NeZero n] :
    C_sg quarterGap n = ENNReal.ofReal 2 ∧
    C_adm quarterGap n = ENNReal.ofReal (4+2*Real.sqrt 3) := by
  constructor
  · rw [unrestricted_optimum]
    norm_num [quarterGap]
  · rw [(admissible_optimum_forms quarterGap).2,quarterGap_mu]
    congr 1
    norm_num [quarterGap] <;> ring

/-- The admissible operational optimum is finite, so its real value is
exactly the already proved closed form. -/
lemma admissible_optimum_toReal (gap : Gap) (n : ℕ) [NeZero n] :
    (C_adm gap n).toReal = (1+gap.mu)/(4*gap.δ^2) := by
  rw [(admissible_optimum_forms gap).2,ENNReal.toReal_ofReal]
  exact div_nonneg (by linarith [gap.mu_nonneg]) (by positivity)

/-- Rationalized exact decomposition, without invoking a Taylor theorem. -/
lemma admissible_exact_decomposition (gap : Gap) (n : ℕ) [NeZero n] :
    (C_adm gap n).toReal = 1/(2*gap.δ^2)-1/(1+gap.mu) := by
  rw [admissible_optimum_toReal]
  have hd : gap.δ ≠ 0 := gap.δ_pos.ne'
  have hm : 1+gap.mu ≠ 0 := by linarith [gap.mu_nonneg]
  field_simp [hd,hm]
  nlinarith [gap.mu_sq]

/-- Exact remainder in the small-gap expansion of the actual optimum. -/
theorem admissible_remainder_identity (gap : Gap) (n : ℕ) [NeZero n] :
    (C_adm gap n).toReal - (1/(2*gap.δ^2)-1/2) =
      -(2*gap.δ^2)/(1+gap.mu)^2 := by
  calc
    _ = 1/2-1/(1+gap.mu) := by rw [admissible_exact_decomposition]; ring
    _ = _ := by
      have hm : 1+gap.mu ≠ 0 := by linarith [gap.mu_nonneg]
      field_simp [hm]
      nlinarith [gap.mu_sq]

/-- Explicit O(delta^2) bound for S1.Ex1. Constant 2 works for every
0 < delta < 1/2, uniformly in the nonzero finite workspace dimension. -/
theorem admissible_asymptotic_remainder_bound (gap : Gap) (n : ℕ) [NeZero n] :
    |(C_adm gap n).toReal - (1/(2*gap.δ^2)-1/2)| ≤ 2*gap.δ^2 := by
  have hmu : 0≤gap.mu := gap.mu_nonneg
  rw [admissible_remainder_identity,abs_div,abs_neg,
    abs_of_nonneg (by positivity : 0≤2*gap.δ^2),abs_of_pos (by positivity : 0<(1+gap.mu)^2)]
  apply (div_le_iff₀ (by positivity : 0<(1+gap.mu)^2)).2
  have hm : 1 ≤ (1+gap.mu)^2 := by nlinarith [gap.mu_nonneg,sq_nonneg gap.mu]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hm (by positivity : 0≤2*gap.δ^2)

/-- The introductory dimension-independence statement for actual costs. -/
theorem costs_dimension_independent (gap : Gap) (n m : ℕ) [NeZero n] [NeZero m] :
    C_sg gap n=C_sg gap m ∧ C_adm gap n=C_adm gap m := by
  constructor
  · rw [unrestricted_optimum,unrestricted_optimum]
  · rw [admissible_optimum,admissible_optimum]

end ELV.Costs
