import Paper26.FrameTailConstraints
import Paper26.BuresTailVolume
import Paper26.RightTailVolume
import Paper26.HaarTruncation
import Mathlib.Algebra.Group.Fin.Basic

/-! Theorem 2.4 in a positive leading-eigenvalue basis. The pointwise
constraints, the numerator bounds, Haar normalization and the final constants
are connected here. Only separately named generic external facts are inputs. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.DiagonalHaarLossBalls
open QuantumModel HaarFrames HaarTruncation Normalization

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

theorem bures_diagonal (r s : ℕ) [NeZero r] (hr : 0 < r) (hrs : r ≤ s)
    (T : TruncatedHaarInput)
    (F : TailMass.BuresMetricInput (Fin r ⊕ Fin s))
    (C : TailMassBridges.RawCompressionInput (Fin r ⊕ Fin s) (Fintype.card (Fin r)))
    (L : TailConvexity.LyapunovPositivityInput (Fin s))
    (BM : TailVolume.BrunnMinkowskiInput (Fin s) (Fin r))
    (UL : TailVolume.UnitaryLebesgueInput (Fin s) (Fin r))
    (BV : ScalarTailBall.EuclideanBallVolumeInput (Fin s) (Fin r))
    (μ : Measure (FrameSpace r s)) (hμ : IsHaarFrameDistribution μ)
    (τ : Density (Fin r ⊕ Fin s)) (b : Fin r → ℝ) (a : Fin s → ℝ)
    (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i)
    (hτ : τ.matrix = diagonalMatrix (Sum.elim b a)) (horder : ∀ i j, a j ≤ b i)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    μ {U | chiB U.density τ ≤ ENNReal.ofReal ε} ≤
      ENNReal.ofReal ((6 * Real.exp 1 * ε * Real.sqrt ((r : ℝ) / (s : ℝ))) ^ (r * s)) := by
  have hs : 0 < s := hr.trans_le hrs
  letI : NeZero r := ⟨hr.ne'⟩
  letI : NeZero s := ⟨hs.ne'⟩
  haveI : IsProbabilityMeasure μ := hμ.probability
  let E : Set (FrameSpace r s) := {U | chiB U.density τ ≤ ENNReal.ofReal ε}
  by_cases hmass : ∑ i, a i ≤ ε
  · let S : Set (TailMatrix r s) :=
      {Z | TailConvexity.H (diagonalMatrix a) Z ≤ 9 * (r : ℝ) ^ 2 * ε}
    have hES : E ⊆ (bottomMap r s) ⁻¹' S := by
      intro U hU
      have h := FrameTailConstraints.bures_success_H F C τ b a hb ha hτ horder U hε hε1 hU
      simpa only [S, Set.mem_setOf_eq, Set.mem_preimage, Fintype.card_fin] using h.2
    have hA : (diagonalMatrix a).PosDef :=
      Matrix.PosDef.diagonal (fun i => Complex.zero_lt_real.2 (ha i))
    have htrace : (Matrix.trace (diagonalMatrix a)).re ≤ ε := by
      simpa [diagonalMatrix, Matrix.trace_diagonal, Complex.re_sum] using hmass
    have hnum := BuresTailVolume.body_volume_le_formula L BM UL BV
      (diagonalMatrix a) hA hε htrace
    simp only [Fintype.card_fin] at hnum
    change matrixLebesgue r s S ≤ _ at hnum
    have hfinite : matrixLebesgue r s S ≠ ∞ :=
      ne_of_lt ((lt_of_le_of_lt hnum ENNReal.ofReal_lt_top))
    have hnumreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnum
    have hformula : (matrixLebesgue r s S).toReal ≤ Real.pi ^ (r * s) *
        (3 * (r : ℝ) * Real.sqrt (r : ℝ) * ε / Real.sqrt (s : ℝ)) ^ (r * s) /
          ((r * s).factorial : ℝ) := by
      simp only [ScalarTailBall.euclideanBallVolume, ScalarTailBall.buresSquaredRadius,
        ScalarTailBall.complexDimension, Fintype.card_fin, Nat.mul_comm] at hnumreal
      rw [ENNReal.toReal_ofReal (by positivity)] at hnumreal
      exact hnumreal
    have hreal := bures_numerator_probability_rate T r s hr hrs μ hμ E S hES hfinite ε hε hformula
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ E)]
    exact ENNReal.ofReal_le_ofReal hreal
  · have hzero : E = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro U hU
      exact hmass (FrameTailConstraints.bures_success_tail F C τ b a hτ horder U hε hε1 hU).1
    change μ E ≤ _
    simp only [hzero, measure_empty, zero_le]

theorem right_diagonal (r s : ℕ) [NeZero r] (hr : 0 < r) (hrs : r ≤ s)
    (T : TruncatedHaarInput)
    (F : TailMass.BuresMetricInput (Fin r ⊕ Fin s))
    (C : TailMassBridges.RawCompressionInput (Fin r ⊕ Fin s) (Fintype.card (Fin r)))
    (J : RightTailVolume.PositiveRowScalingInput (Fin s) (Fin r))
    (BV : ScalarTailBall.EuclideanBallVolumeInput (Fin s) (Fin r))
    (μ : Measure (FrameSpace r s)) (hμ : IsHaarFrameDistribution μ)
    (τ : Density (Fin r ⊕ Fin s)) (b : Fin r → ℝ) (a : Fin s → ℝ)
    (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i)
    (hτ : τ.matrix = diagonalMatrix (Sum.elim b a)) (horder : ∀ i j, a j ≤ b i)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    μ {U | chiR U.density τ ≤ ENNReal.ofReal ε} ≤
      ENNReal.ofReal ((18 * Real.exp 1 * (r : ℝ) * ε ^ 2 / (s : ℝ)) ^ (r * s)) := by
  have hs : 0 < s := hr.trans_le hrs
  letI : NeZero r := ⟨hr.ne'⟩
  letI : NeZero s := ⟨hs.ne'⟩
  haveI : IsProbabilityMeasure μ := hμ.probability
  let E : Set (FrameSpace r s) := {U | chiR U.density τ ≤ ENNReal.ofReal ε}
  by_cases hmass : ∑ i, a i ≤ ε
  · let S : Set (TailMatrix r s) :=
      {Z | TailLossConstraints.ellipsoidEnergy a Z ≤ 9 * (r : ℝ) ^ 2 * ε}
    have hES : E ⊆ (bottomMap r s) ⁻¹' S := by
      intro U hU
      have h := FrameTailConstraints.right_success_ellipsoid F C τ b a hb ha hτ horder U hε hε1 hU
      simpa only [S, Set.mem_setOf_eq, Set.mem_preimage, Fintype.card_fin] using h.2
    have hnum := RightTailVolume.ellipsoid_volume_epsilon J BV a ha hε.le hmass
    simp only [Fintype.card_fin] at hnum
    change matrixLebesgue r s S ≤ _ at hnum
    have hfinite : matrixLebesgue r s S ≠ ∞ :=
      ne_of_lt ((lt_of_le_of_lt hnum ENNReal.ofReal_lt_top))
    have hnumreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnum
    have hformula : (matrixLebesgue r s S).toReal ≤ Real.pi ^ (r * s) *
        (9 * (r : ℝ) ^ 2 * ε ^ 2 / (s : ℝ)) ^ (r * s) /
          ((r * s).factorial : ℝ) := by
      simp only [ScalarTailBall.euclideanBallVolume, RightTailVolume.rightSquaredRadius,
        ScalarTailBall.complexDimension, Fintype.card_fin, Nat.mul_comm] at hnumreal
      rw [ENNReal.toReal_ofReal (by positivity)] at hnumreal
      exact hnumreal
    have hreal := right_numerator_probability_rate T r s hr hrs μ hμ E S hES hfinite ε hε hformula
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ E)]
    exact ENNReal.ofReal_le_ofReal hreal
  · have hzero : E = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro U hU
      exact hmass (FrameTailConstraints.right_success_ellipsoid F C τ b a hb ha hτ horder U hε hε1 hU).1
    change μ E ≤ _
    simp only [hzero, measure_empty, zero_le]

end Paper26.DiagonalHaarLossBalls
