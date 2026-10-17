import PUT.OperatorBridge
import PUT.NormBound

/-! # Actual full query norm from the proved preparation/erasure estimates

This is the last step of Lemma 1. Its two local block estimates are supplied
by the Fourier/principal/radial construction, not by an external theorem.
-/
noncomputable section
namespace PUT.FullNorm

def plusEnvelope (a A d M : ℝ) : ℝ :=
  Real.sqrt (1 + 8 * A / d) + A ^ (3 / 2 : ℝ) / (a * Real.sqrt d) +
    etaM A M + A / Real.sqrt (a * d)

def minusEnvelope (a A d M : ℝ) : ℝ :=
  Real.sqrt (1 + 8 * A / d) + A ^ (3 / 2 : ℝ) / (a * Real.sqrt d) +
    etaM A M + A / Real.sqrt M

/-- The exact two-block expression, with both radial contributions, is
bounded by the printed right-hand side (8). -/
theorem envelopes_le_printed (a A d M : ℝ) (ha : 0 < a) (hA : 1 ≤ A)
    (hd : 0 < d) (hM : 16 * A ^ 2 * LA A ≤ M) :
    2 * (plusEnvelope a A d M + minusEnvelope a A d M) ≤ lemma1RHS A a d := by
  have hAd : 0 ≤ A / d := by positivity
  have hg := sqrt_one_add_8x_le (A / d) hAd
  have hg' : Real.sqrt (1 + 8 * A / d) ≤ 3 * Real.sqrt (1 + A / d) := by
    simpa only [mul_div_assoc] using hg
  have hS := sqrt_one_add_nonneg (A / d) hAd
  have hh : 0 ≤ A ^ (3 / 2 : ℝ) / (a * Real.sqrt d) := by positivity
  have hr : 0 ≤ A / Real.sqrt (a * d) := by positivity
  have htwo := two_block_envelope a A d M ha hA hd hM
  dsimp only [plusEnvelope, minusEnvelope] at *
  unfold lemma1RHS
  linarith

section Operators
variable {E₀ E₁ F₀ F₁ : Type*}
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
open PUT.OperatorBridge

/-- Full reflection query difference on arbitrary inputs, including all
radial-complement inputs. -/
theorem query_norm_le (Γ : E₁ →L[ℂ] E₀) (ΓH : F₁ →L[ℂ] F₀)
    (V₀ : E₀ →ₗᵢ[ℂ] F₀) (V₁ : E₁ →ₗᵢ[ℂ] F₁)
    (a A d M : ℝ) (ha : 0 < a) (hA : 1 ≤ A) (hd : 0 < d)
    (hM : 16 * A ^ 2 * LA A ≤ M)
    (hplus : ‖dplus Γ ΓH V₀.toContinuousLinearMap V₁.toContinuousLinearMap‖ ≤ plusEnvelope a A d M)
    (hminus : ‖dminus Γ ΓH V₀.toContinuousLinearMap V₁.toContinuousLinearMap‖ ≤ minusEnvelope a A d M) :
    ‖liftedAdversary Γ ΓH ∘L reflectionBlock V₁.toContinuousLinearMap -
      reflectionBlock V₀.toContinuousLinearMap ∘L liftedAdversary Γ ΓH‖ ≤ lemma1RHS A a d := by
  exact (full_query_norm_le Γ ΓH V₀ V₁).trans
    ((mul_le_mul_of_nonneg_left (add_le_add hplus hminus) (by norm_num)).trans
      (envelopes_le_printed a A d M ha hA hd hM))
end Operators
end PUT.FullNorm
