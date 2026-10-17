import Paper29.ContractionTools
import Paper29.TransitionScores
import Paper29.LewisInput

noncomputable section
open scoped BigOperators Classical
namespace Paper29.WeightConstruction

variable {n d : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : A.rank = d) (hrows : ∀ i, A i ≠ 0)

/-- Exact p=1 auxiliary-weight update, using only the known matrix. -/
def oneUpdate (w : PositiveWeights n) : PositiveWeights n :=
  ⟨fun i => (Leverage.radius A w i)⁻¹, by
    intro i
    exact inv_pos.mpr (Real.sqrt_pos.2 (Leverage.radiusSq_pos A w
      (Leverage.mulVec_injective_of_rank_eq A hA) w.property i (hrows i)))⟩

theorem log_oneUpdate (w : PositiveWeights n) (i : Fin n) :
    Real.log (oneUpdate A hA hrows w i) = -(Real.log (Leverage.radiusSq A w i) / 2) := by
  change Real.log (Real.sqrt (Leverage.radiusSq A w i))⁻¹ = _
  rw [Real.log_inv, Real.log_sqrt (Leverage.radiusSq_nonneg A w
    (Leverage.mulVec_injective_of_rank_eq A hA) w.property i)]

theorem oneUpdate_contracts (external : RadiusLogNonexpansive) (u w : PositiveWeights n) :
    logDist (oneUpdate A hA hrows u) (oneUpdate A hA hrows w) ≤ (1/2)*logDist u w := by
  apply logDist_le
  intro i
  rw [log_oneUpdate, log_oneUpdate]
  have he (x y : ℝ) : -(x/2) - -(y/2) = -(1/2)*(x-y) := by ring
  rw [he, abs_mul]
  norm_num
  exact external n d A hA hrows u w i

/-- Least finite stopping index for the l1 endpoint. -/
def oneStop (external : RadiusLogNonexpansive) : ℕ :=
  Nat.find (contraction_stopping (oneUpdate A hA hrows)
    (oneUpdate_contracts A hA hrows external) ⟨fun _ => 1, fun _ => by norm_num⟩
    (Real.log_pos (by norm_num : (1:ℝ)<2)))

def finiteOneWeight (external : RadiusLogNonexpansive) : PositiveWeights n :=
  (oneUpdate A hA hrows)^[oneStop A hA hrows external] ⟨fun _ => 1, fun _ => by norm_num⟩

theorem finiteOneWeight_residual (external : RadiusLogNonexpansive) :
    logDist (oneUpdate A hA hrows (finiteOneWeight A hA hrows external))
      (finiteOneWeight A hA hrows external) ≤ Real.log 2 :=
  Nat.find_spec (contraction_stopping (oneUpdate A hA hrows)
    (oneUpdate_contracts A hA hrows external) ⟨fun _ => 1, fun _ => by norm_num⟩
    (Real.log_pos (by norm_num : (1:ℝ)<2)))

theorem oneUpdate_fixed (v : PositiveWeights n)
    (hv : ∀ i, Leverage.radius A v i / Leverage.leverage A v i = 1) :
    oneUpdate A hA hrows v = v := by
  apply Subtype.ext
  funext i
  have hrs := Leverage.radiusSq_pos A v (Leverage.mulVec_injective_of_rank_eq A hA)
    v.property i (hrows i)
  have hr := Real.sqrt_pos.2 hrs
  have he := (div_eq_one_iff_eq (ne_of_gt (Chaining.leverage_pos A hA hrows v i))).1 (hv i)
  have hs := Leverage.radius_sq A v (Leverage.mulVec_injective_of_rank_eq A hA) v.property i
  change (Leverage.radius A v i)⁻¹ = v i
  have he' : Leverage.radius A v i = v i * Leverage.radiusSq A v i := he
  have heq : (v i * Leverage.radius A v i - 1) * Leverage.radius A v i = 0 := by
    calc
      _ = v i * Leverage.radius A v i ^ 2 - Leverage.radius A v i := by ring
      _ = 0 := by rw [hs, ← he']; ring
  have heq' : v i * Leverage.radius A v i = 1 := by
    have hh := (mul_eq_zero.mp heq).resolve_right (ne_of_gt hr)
    linarith
  exact inv_eq_of_mul_eq_one_left heq'

/-- The computed weight is within a universal log factor of the exact endpoint. -/
theorem finiteOneWeight_distance (external : RadiusLogNonexpansive) (v : PositiveWeights n)
    (hv : ∀ i, Leverage.radius A v i / Leverage.leverage A v i = 1) :
    logDist (finiteOneWeight A hA hrows external) v ≤ 2*Real.log 2 := by
  have h := contraction_fixedpoint_error (oneUpdate A hA hrows)
    (oneUpdate_contracts A hA hrows external) (finiteOneWeight A hA hrows external) v
    (oneUpdate_fixed A hA hrows v hv)
  have hr := finiteOneWeight_residual A hA hrows external
  linarith

/-- Safe score inflation is proved from actual leverage identities and the
known log-radius stability, not assumed as an endpoint score certificate. -/
theorem finite_endpoint_dominates (external : RadiusLogNonexpansive) (v : PositiveWeights n)
    (hv : ∀ i, Leverage.radius A v i / Leverage.leverage A v i = 1) (i : Fin n) :
    Leverage.leverage A v i ≤ 16 * Leverage.leverage A (finiteOneWeight A hA hrows external) i := by
  let u := finiteOneWeight A hA hrows external
  have hd := finiteOneWeight_distance A hA hrows external v hv
  have hlog : |Real.log (Leverage.leverage A v i) - Real.log (Leverage.leverage A u i)| ≤
      2 * logDist u v := by
    have hvrs := Leverage.radiusSq_pos A v (Leverage.mulVec_injective_of_rank_eq A hA)
      v.property i (hrows i)
    have hurs := Leverage.radiusSq_pos A u (Leverage.mulVec_injective_of_rank_eq A hA)
      u.property i (hrows i)
    rw [Leverage.leverage, Leverage.leverage,
      Real.log_mul (ne_of_gt (v.property i)) (ne_of_gt hvrs),
      Real.log_mul (ne_of_gt (u.property i)) (ne_of_gt hurs)]
    have he (a b c d : ℝ) : a+b-(c+d) = (a-c)+(b-d) := by ring
    rw [he]
    have hw := coordinate_le_logDist v u i
    have hr := external n d A hA hrows v u i
    rw [logDist_symm v u] at hw hr
    exact (abs_add_le _ _).trans (by linarith)
  have h16 : Real.log (16:ℝ) = 4*Real.log 2 := by
    rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]
    norm_num
  have hbound : Real.log (Leverage.leverage A v i) - Real.log (Leverage.leverage A u i) ≤
      Real.log 16 := by
    have hh := (abs_le.mp hlog).2
    rw [h16]
    linarith
  apply (Real.log_le_log_iff (Chaining.leverage_pos A hA hrows v i)
    (mul_pos (by norm_num) (Chaining.leverage_pos A hA hrows u i))).mp
  rw [Real.log_mul (by norm_num : (16:ℝ)≠0)
    (ne_of_gt (Chaining.leverage_pos A hA hrows u i))]
  linarith

end Paper29.WeightConstruction
