import Paper26.TailVolume
import Paper26.ScalarTailBall
import Paper26.TailLossConstraints

/-! The Bures numerator-volume argument of Theorem 2.4, with the internally
proved symmetrization discharged rather than supplied as a new premise. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.BuresTailVolume

variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]

local instance matrixMeasurableSpace (m : Type*) (n : Type*) :
    MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

theorem trace_pos [Nonempty σ] (A : Matrix σ σ ℂ) (hA : A.PosDef) :
    0 < (Matrix.trace A).re := by
  obtain ⟨U, a, hU₁, _, ha, heq⟩ :=
    Normalization.exists_positive_spectral_representation A hA
  rw [heq, Normalization.trace_conjugate_diagonal U a hU₁]
  exact Normalization.spectrum_trace_pos a ha

/-- The loss-specific numerator in (19) is bounded by a real Euclidean ball.
The only external inputs are the generic Lyapunov/BM/rotation theorems and the
ordinary even-dimensional Euclidean-ball volume formula. -/
theorem body_volume_le_formula [AddCommGroup σ] [Nonempty σ] [Nonempty κ]
    (L : TailConvexity.LyapunovPositivityInput σ)
    (BM : TailVolume.BrunnMinkowskiInput σ κ)
    (UL : TailVolume.UnitaryLebesgueInput σ κ)
    (BV : ScalarTailBall.EuclideanBallVolumeInput σ κ)
    (A : Matrix σ σ ℂ) (hA : A.PosDef) {ε : ℝ}
    (hε : 0 < ε) (htrace : (Matrix.trace A).re ≤ ε) :
    TailGeometry.matrixLebesgue {Z : Matrix σ κ ℂ |
      TailConvexity.H A Z ≤ 9 * (Fintype.card κ : ℝ) ^ 2 * ε} ≤
      ENNReal.ofReal (ScalarTailBall.euclideanBallVolume (σ := σ) (κ := κ)
        (ScalarTailBall.buresSquaredRadius (σ := σ) (κ := κ) ε)) := by
  apply ScalarTailBall.body_volume_le_formula_of_scalar_comparison BV A
    (trace_pos A hA) htrace
  exact TailVolume.uniform_tail_maximizes_volume L BM UL A hA _ (by positivity)

/-- Any set satisfying the actual pointwise tail constraint inherits the
numerator bound; its eventual Haar normalization is a separate step. -/
theorem subset_volume_le_formula [AddCommGroup σ] [Nonempty σ] [Nonempty κ]
    (L : TailConvexity.LyapunovPositivityInput σ)
    (BM : TailVolume.BrunnMinkowskiInput σ κ)
    (UL : TailVolume.UnitaryLebesgueInput σ κ)
    (BV : ScalarTailBall.EuclideanBallVolumeInput σ κ)
    (A : Matrix σ σ ℂ) (hA : A.PosDef) {ε : ℝ}
    (hε : 0 < ε) (htrace : (Matrix.trace A).re ≤ ε)
    (S : Set (Matrix σ κ ℂ))
    (hS : ∀ Z ∈ S, TailConvexity.H A Z ≤ 9 * (Fintype.card κ : ℝ) ^ 2 * ε) :
    TailGeometry.matrixLebesgue S ≤
      ENNReal.ofReal (ScalarTailBall.euclideanBallVolume (σ := σ) (κ := κ)
        (ScalarTailBall.buresSquaredRadius (σ := σ) (κ := κ) ε)) := by
  exact (measure_mono hS).trans (body_volume_le_formula L BM UL BV A hA hε htrace)

end Paper26.BuresTailVolume
