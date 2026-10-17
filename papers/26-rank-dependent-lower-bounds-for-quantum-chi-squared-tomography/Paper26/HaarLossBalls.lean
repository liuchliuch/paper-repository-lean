import Paper26.DiagonalHaarLossBalls
import Paper26.PositiveOutputDecomposition
import Paper26.SingularHaarLoss

/-! The full two loss-ball statements of Theorem 2.4, for every actual
density output, including singular outputs and all `0 < r ≤ s`.

The standard external inputs are individually visible: fidelity/metric and
compression theory, Lyapunov positivity, Brunn--Minkowski, Lebesgue coordinate
changes and ball volume, and Haar truncation/subspace nullity. None of them
states a loss-ball bound. All P26-specific steps are derived in the imported
modules and connected by the proofs below. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.HaarLossBalls
open QuantumModel HaarFrames HaarTruncation PositiveLossBridge PositiveOutputDecomposition

private theorem density_ext {ι : Type*} [Fintype ι] {ρ η : Density ι}
    (h : ρ.matrix = η.matrix) : ρ = η := by
  cases ρ
  cases η
  cases h
  rfl

/-- The frame's actual rotated flat density is the conjugated density. -/
theorem rotate_density_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (V : Matrix.unitaryGroup ι ℂ) (U : Frame ι κ) :
    (U.rotate V).density = conjugateDensity V U.density := by
  apply density_ext
  exact U.rotate_density V

/-- Haar row invariance transfers the successful event to ordered spectral
coordinates. The argument uses the outer-measure inequality for maps, so no
unproved measurability of the singular spectral loss is required. -/
theorem event_probability_to_diagonal {κ σ : Type*}
    [Fintype κ] [DecidableEq κ] [Nonempty κ] [Fintype σ] [DecidableEq σ]
    (loss : Density (κ ⊕ σ) → Density (κ ⊕ σ) → ℝ≥0∞)
    (hinvariant : ∀ (V : Matrix.unitaryGroup (κ ⊕ σ) ℂ) (ρ τ : Density (κ ⊕ σ)),
      τ.matrix.PosDef → loss (conjugateDensity V ρ) (conjugateDensity V τ) = loss ρ τ)
    (μ : Measure (Frame (κ ⊕ σ) κ)) (hμ : IsHaarFrameDistribution μ)
    (τ : Density (κ ⊕ σ)) (hτ : τ.matrix.PosDef) (D : OrderedDecomposition τ)
    (ε : ℝ) :
    μ {U | loss U.density τ ≤ ENNReal.ofReal ε} ≤
      μ {U | loss U.density D.diagonalDensity ≤ ENNReal.ofReal ε} := by
  let R : Frame (κ ⊕ σ) κ → Frame (κ ⊕ σ) κ := fun U => U.rotate (star D.unitary)
  let E : Set (Frame (κ ⊕ σ) κ) :=
    {U | loss U.density D.diagonalDensity ≤ ENNReal.ofReal ε}
  have hsub : {U | loss U.density τ ≤ ENNReal.ofReal ε} ⊆ R ⁻¹' E := by
    intro U hU
    have h := hinvariant (star D.unitary) U.density τ hτ
    rw [D.conjugateDensity_eq_diagonalDensity, ← rotate_density_eq] at h
    change loss (U.rotate (star D.unitary)).density D.diagonalDensity ≤ ENNReal.ofReal ε
    rw [h]
    exact hU
  calc
    _ ≤ μ (R ⁻¹' E) := measure_mono hsub
    _ ≤ (Measure.map R μ) E := Measure.le_map_apply (Frame.measurable_rotate _).aemeasurable E
    _ = μ E := by rw [hμ.row_invariant (star D.unitary)]

/-- Theorem 2.4, Equation (19), with the actual support/infinity convention. -/
theorem theorem_2_4_bures (r s : ℕ) [NeZero r] (hr : 0 < r) (hrs : r ≤ s)
    (T : TruncatedHaarInput)
    (N : ProperSubspaceNullInput (Fin r ⊕ Fin s) (Fin r))
    (F : TailMass.BuresMetricInput (Fin r ⊕ Fin s))
    (C : TailMassBridges.RawCompressionInput (Fin r ⊕ Fin s) (Fintype.card (Fin r)))
    (L : TailConvexity.LyapunovPositivityInput (Fin s))
    (BM : TailVolume.BrunnMinkowskiInput (Fin s) (Fin r))
    (UL : TailVolume.UnitaryLebesgueInput (Fin s) (Fin r))
    (BV : ScalarTailBall.EuclideanBallVolumeInput (Fin s) (Fin r))
    (μ : Measure (FrameSpace r s)) (hμ : IsHaarFrameDistribution μ)
    (τ : Density (Fin r ⊕ Fin s)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    μ {U | chiB U.density τ ≤ ENNReal.ofReal ε} ≤
      ENNReal.ofReal ((6 * Real.exp 1 * ε * Real.sqrt ((r : ℝ) / (s : ℝ))) ^ (r * s)) := by
  by_cases hτ : τ.matrix.PosDef
  · let D := orderedDecomposition τ hτ
    exact (event_probability_to_diagonal chiB chiB_unitary μ hμ τ hτ D ε).trans
      (DiagonalHaarLossBalls.bures_diagonal r s hr hrs T F C L BM UL BV μ hμ
        D.diagonalDensity D.head D.tail D.head_pos D.tail_pos rfl D.tail_le_head hε hε1)
  · rw [SingularHaarLoss.chiB_success_null N μ hμ τ hτ ε]
    exact zero_le _

/-- Theorem 2.4, Equation (20), for the same unrestricted density outputs. -/
theorem theorem_2_4_right (r s : ℕ) [NeZero r] (hr : 0 < r) (hrs : r ≤ s)
    (T : TruncatedHaarInput)
    (N : ProperSubspaceNullInput (Fin r ⊕ Fin s) (Fin r))
    (F : TailMass.BuresMetricInput (Fin r ⊕ Fin s))
    (C : TailMassBridges.RawCompressionInput (Fin r ⊕ Fin s) (Fintype.card (Fin r)))
    (J : RightTailVolume.PositiveRowScalingInput (Fin s) (Fin r))
    (BV : ScalarTailBall.EuclideanBallVolumeInput (Fin s) (Fin r))
    (μ : Measure (FrameSpace r s)) (hμ : IsHaarFrameDistribution μ)
    (τ : Density (Fin r ⊕ Fin s)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    μ {U | chiR U.density τ ≤ ENNReal.ofReal ε} ≤
      ENNReal.ofReal ((18 * Real.exp 1 * (r : ℝ) * ε ^ 2 / (s : ℝ)) ^ (r * s)) := by
  by_cases hτ : τ.matrix.PosDef
  · let D := orderedDecomposition τ hτ
    exact (event_probability_to_diagonal chiR chiR_unitary μ hμ τ hτ D ε).trans
      (DiagonalHaarLossBalls.right_diagonal r s hr hrs T F C J BV μ hμ
        D.diagonalDensity D.head D.tail D.head_pos D.tail_pos rfl D.tail_le_head hε hε1)
  · rw [SingularHaarLoss.chiR_success_null N μ hμ τ hτ ε]
    exact zero_le _

end Paper26.HaarLossBalls
