import Paper36.Main
import Paper36.Scaling

/-! Explicit logarithmic square-root envelopes for the actual performance
right-hand side. These are one-sided upper envelopes; no absolute-value or
two-sided regret statement is asserted. -/
namespace Paper36.SourceScaling
open Paper36 Asymptotics Filter
noncomputable section

lemma rewardLog_eq {s a h : ℝ} (hs : 0 < s) (ha : 0 < a) (hh : 0 < h)
    {K : ℕ} (hK : 1 ≤ K) :
    Bounds.rewardLog s a h K = Bounds.rewardLog s a h 1 + 2 * Real.log (K : ℝ) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hb : 0 < Bounds.budget s a h 1 := by unfold Bounds.budget; positivity
  have he : Bounds.budget s a h K = Bounds.budget s a h 1 * (K : ℝ)^2 := by
    unfold Bounds.budget
    norm_num
  unfold Bounds.rewardLog
  rw [he, Real.log_mul hb.ne' (pow_pos hK0 2).ne', Real.log_pow]
  ring

lemma rewardLog_log_envelope {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h)
    {K : ℕ} (hK : 1 ≤ K) :
    Bounds.rewardLog s a h K ≤ (Bounds.rewardLog s a h 1 + 2) * (1 + Real.log (K : ℝ)) := by
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ K by exact_mod_cast hK)
  have hL := Bounds.rewardLog_one_le hs ha hh (show 1 ≤ (1 : ℕ) by rfl)
  rw [rewardLog_eq (by linarith) (by linarith) (by linarith) hK]
  nlinarith

/-- The actual target (4.5) has its explicit fixed-instance logarithmic envelope. -/
theorem target_log_envelope {s a h w : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a)
    (hh : 1 ≤ h) (hw : 0 ≤ w) {K : ℕ} (hK : 1 ≤ K) :
    BankTarget.paperTarget s a h w K ≤
      Scaling.coefficient (Target.scale w s a) (Target.A0 s a h) (Target.nu s) (Target.M0 h) *
        Real.sqrt (K : ℝ) * (1 + Real.log (K : ℝ)) := by
  have hp := Target.parameter_bounds hs ha hh
  exact Scaling.target_log_sqrt_bound (Target.scale_nonneg hw) (by linarith [hp.1, hp.2.1])
    (by linarith [hp.2.2]) hp.1.le hK

/-- A concrete coefficient multiplying sqrt(K)(1+log K). -/
def rewardCoefficient (s a h : ℝ) : ℝ :=
  8 * h * Real.sqrt h * Real.sqrt (s*a) * Real.sqrt (Bounds.rewardLog s a h 1 + 2) + h/2

lemma reward_log_envelope {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h)
    {K : ℕ} (hK : 1 ≤ K) :
    8 * h * Real.sqrt h * Real.sqrt (s*a*(K:ℝ)*Bounds.rewardLog s a h K) + h/2 ≤
      rewardCoefficient s a h * Real.sqrt (K : ℝ) * (1 + Real.log (K : ℝ)) := by
  let x := 1 + Real.log (K : ℝ)
  let L := Bounds.rewardLog s a h 1 + 2
  have hx : 1 ≤ x := by dsimp [x]; have := Real.log_nonneg (show (1:ℝ)≤K by exact_mod_cast hK); linarith
  have hL : 0 ≤ L := by dsimp [L]; have := Bounds.rewardLog_one_le hs ha hh (K:=1) le_rfl; linarith
  have hsa : 0 ≤ s*a := by positivity
  have hk : 0 ≤ (K:ℝ) := Nat.cast_nonneg K
  have hk1 : 1 ≤ Real.sqrt (K:ℝ) := (Real.le_sqrt (by norm_num) hk).2 (by simpa using (show (1:ℝ)≤K by exact_mod_cast hK))
  have hlog := rewardLog_log_envelope hs ha hh hK
  have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog (mul_nonneg hsa hk))
  have hprod : Real.sqrt (s*a*(K:ℝ)*(L*x)) = Real.sqrt (s*a) * Real.sqrt (K:ℝ) * Real.sqrt L * Real.sqrt x := by
    rw [show s*a*(K:ℝ)*(L*x)=(s*a*(K:ℝ)*L)*x by ring,
      Real.sqrt_mul (mul_nonneg (mul_nonneg hsa hk) hL),
      Real.sqrt_mul (mul_nonneg hsa hk), Real.sqrt_mul hsa]
  have hsqrtx : Real.sqrt x ≤ x := by
    apply (Real.sqrt_le_left (by linarith)).2
    nlinarith
  have hroot' : Real.sqrt (s*a*(K:ℝ)*Bounds.rewardLog s a h K) ≤
      Real.sqrt (s*a) * Real.sqrt (K:ℝ) * Real.sqrt L * x := by
    exact hroot.trans (by rw [hprod]; exact mul_le_mul_of_nonneg_left hsqrtx (by positivity))
  have he := mul_le_mul_of_nonneg_left hroot' (show 0 ≤ 8*h*Real.sqrt h by positivity)
  have hxk : 1 ≤ Real.sqrt (K:ℝ)*x := one_le_mul_of_one_le_of_one_le hk1 hx
  have hc : h/2 ≤ (h/2)*(Real.sqrt (K:ℝ)*x) := by nlinarith
  unfold rewardCoefficient
  dsimp [L] at he
  dsimp [x] at he hxk hc
  nlinarith

/-- The literal reward RHS in Theorem 4.2, not the signed regret itself,
is O(sqrt K (1+log K)) for every fixed feasible instance. -/
theorem performance_upper_envelope_isBigO {s a h w Δ τ : ℝ}
    (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) (hw : 0 ≤ w) (hΔ : 0 < Δ) (hτ : 0 ≤ τ) :
    (fun K : ℕ =>
      8*h*Real.sqrt h*Real.sqrt (s*a*(K:ℝ)*Bounds.rewardLog s a h K) + h/2 +
        h*((BankTarget.paperTarget s a h w K+τ)/Δ)) =O[atTop]
      (fun K : ℕ => Real.sqrt (K:ℝ)*(1+Real.log (K:ℝ))) := by
  let C := Scaling.coefficient (Target.scale w s a) (Target.A0 s a h) (Target.nu s) (Target.M0 h)
  have hp := Target.parameter_bounds hs ha hh
  have hA : 0 ≤ Target.A0 s a h := by linarith [hp.1, hp.2.1]
  have hM : 0 ≤ Target.M0 h := by linarith [hp.2.2]
  have hν : 0 ≤ Target.nu s := hp.1.le
  have hscale := Target.scale_nonneg (s := s) (a := a) hw
  have hC : 0 ≤ C := by unfold C Scaling.coefficient Target.gamma₀ Target.G₀; positivity
  apply Asymptotics.IsBigO.of_bound (rewardCoefficient s a h + h/Δ*C + h*τ/Δ)
  filter_upwards [Filter.eventually_ge_atTop 1] with K hK
  let x := Real.sqrt (K:ℝ)*(1+Real.log (K:ℝ))
  have hlog := Real.log_nonneg (show (1:ℝ)≤K by exact_mod_cast hK)
  have hk : 1 ≤ Real.sqrt (K:ℝ) := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg K)).2 (by simpa using (show (1:ℝ)≤K by exact_mod_cast hK))
  have hx : 1 ≤ x := one_le_mul_of_one_le_of_one_le hk (by linarith)
  have ht := target_log_envelope hs ha hh hw hK
  have hr := reward_log_envelope hs ha hh hK
  have hmul := mul_le_mul_of_nonneg_left ht (show 0 ≤ h/Δ by positivity)
  have hconst : h*τ/Δ ≤ h*τ/Δ*x := by nlinarith [div_nonneg (mul_nonneg (by linarith : 0≤h) hτ) hΔ.le]
  have hnonneg : 0 ≤ 8*h*Real.sqrt h*Real.sqrt (s*a*(K:ℝ)*Bounds.rewardLog s a h K) + h/2 +
      h*((BankTarget.paperTarget s a h w K+τ)/Δ) := by
    have ht0 := Target.target_nonneg (Target.scale_nonneg (s:=s) (a:=a) hw) (A:=Target.A0 s a h) (ν:=Target.nu s) (M:=Target.M0 h) K
    change 0 ≤ BankTarget.paperTarget s a h w K at ht0
    positivity
  have hx0 : 0 ≤ Real.sqrt (K:ℝ)*(1+Real.log (K:ℝ)) := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hx0]
  dsimp [C] at hmul ⊢
  change _ ≤ (rewardCoefficient s a h + h/Δ*C + h*τ/Δ)*x
  dsimp [x, C] at hconst ⊢
  ring_nf at hr hmul hconst ⊢
  linarith

/-- After removing the displayed S^2 A W^2/Delta factor, the exact residual
has only this explicit logarithmic coefficient. All parameters remain visible. -/
def residualLogFactor (s a h w Δ : ℝ) : ℝ :=
  (Target.G₀ (Target.A0 s a h) (Target.M0 h) +
    2 * Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h) *
      Real.log (1 + 4 * Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h) *
        Target.scale w s a / Δ)) / Real.sqrt s

lemma scale_sq {s a w : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) :
    (Target.scale w s a)^2 = 32*w^2*s*a := by
  unfold Target.scale
  have htwo := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hsa := Real.sq_sqrt (mul_nonneg hs ha)
  nlinarith [sq_nonneg (w * Real.sqrt (s*a))]

/-- The source parameter exponents of R_* are retained as an exact identity,
with its logarithmic expression explicit and independent of K. -/
theorem residual_parameter_identity {s a h w Δ : ℝ}
    (hs : 0 < s) (ha : 0 ≤ a) (hΔ : 0 < Δ) :
    BankTarget.paperResidual s a h w Δ =
      16*s^2*a*w^2/Δ * (residualLogFactor s a h w Δ)^2 := by
  unfold BankTarget.paperResidual Target.residual residualLogFactor
  rw [scale_sq hs.le ha, div_pow, Real.sq_sqrt hs.le]
  field_simp
  ring

end
end Paper36.SourceScaling
