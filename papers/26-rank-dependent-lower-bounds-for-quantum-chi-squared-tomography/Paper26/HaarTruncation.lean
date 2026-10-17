import Paper26.HaarFrames
import Paper26.TailGeometry
import Paper26.VolumeRates
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Exact Haar-frame truncation input and probability/volume bridges

The sole matrix-ball distribution field is an explicitly supplied known
theorem, not a claimed Lean proof and not part of the definition of Haar
frames. Its primary source is Fyodorov--Khoruzhenko (2006),
arXiv:math-ph/0610045v2, Section 3, equations (35)--(38), PDF p. 9;
the Selberg normalizations are (87)--(88), PDF p. 22. At dimensions
`N=r+s`, `m=r`, `n=s`, the determinant exponent `N-m-n` is zero.
The exact factorial constant is `VolumeRates.graphNormalizer s r`, also
matching the normalized Grassmann chart constant in Douçot--Kovrizhin--
Moessner (2018), arXiv:1808.06783v1, equations (35), (38), (39), PDF p. 8.
These are registry entries `FK2006`, `DKM2018`, and
`P26-EXT-HAAR-TRUNCATION` in `external-inputs.json`.

The input below is stated directly for the actual invariant frame measure,
including its standard identification with the first columns of a Haar
unitary and the unitary row permutation to the bottom corner. It contains
no loss, success event, numerator-volume estimate, or rate. All subsequent
probability inequalities and arithmetic rate conversions are proved here.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.HaarTruncation

open HaarFrames

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

abbrev FrameSpace (r s : ℕ) := Frame (Fin r ⊕ Fin s) (Fin r)
abbrev TailMatrix (r s : ℕ) := Matrix (Fin s) (Fin r) ℂ

/-- The actual open operator-norm matrix ball `Z†Z < I`. -/
def matrixBall (r s : ℕ) : Set (TailMatrix r s) :=
  {Z | (1 - Zᴴ * Z).PosDef}

/-- Standard product Lebesgue measure in all complex matrix entries, with
one real and one imaginary coordinate per entry. -/
abbrev matrixLebesgue (r s : ℕ) : Measure (TailMatrix r s) :=
  TailGeometry.matrixLebesgue

/-- The actual last-row map already verified on orthonormal frame objects. -/
abbrev bottomMap (r s : ℕ) : FrameSpace r s → TailMatrix r s := Frame.bottom

theorem measurable_bottomMap (r s : ℕ) : Measurable (bottomMap r s) :=
  Frame.measurable_bottom

/-- Exact external rectangular Haar-truncation theorem, specialized only in
dimensions (`N=r+s`, so the determinant exponent is zero). The law is a
measure equality, not an all-set preimage equality. -/
structure TruncatedHaarInput : Prop where
  bottom_law : ∀ (r s : ℕ), 0 < r → r ≤ s →
    ∀ (μ : Measure (FrameSpace r s)), IsHaarFrameDistribution μ →
      Measure.map (bottomMap r s) μ =
        (ENNReal.ofReal (VolumeRates.graphNormalizer s r))⁻¹ •
          (matrixLebesgue r s).restrict (matrixBall r s)

/-- The exact factorial product is strictly positive, independently of any
unformalized probability theorem. -/
theorem graphNormalizer_pos (s r : ℕ) : 0 < VolumeRates.graphNormalizer s r := by
  unfold VolumeRates.graphNormalizer
  apply mul_pos (pow_pos Real.pi_pos _)
  apply Finset.prod_pos
  intro j _
  exact div_pos (Nat.cast_pos.2 (Nat.factorial_pos j))
    (Nat.cast_pos.2 (Nat.factorial_pos (s + j)))

/-- Exact probability formula on measurable matrix sets. No measurability
assumption about the preimage is silently replaced by an all-set equality. -/
theorem bottom_probability (T : TruncatedHaarInput) (r s : ℕ)
    (hr : 0 < r) (hrs : r ≤ s) (μ : Measure (FrameSpace r s))
    (hμ : IsHaarFrameDistribution μ) (S : Set (TailMatrix r s))
    (hS : MeasurableSet S) :
    μ ((bottomMap r s) ⁻¹' S) =
      matrixLebesgue r s (S ∩ matrixBall r s) /
        ENNReal.ofReal (VolumeRates.graphNormalizer s r) := by
  rw [← Measure.map_apply (measurable_bottomMap r s) hS,
    T.bottom_law r s hr hrs μ hμ, Measure.smul_apply,
    Measure.restrict_apply hS, smul_eq_mul]
  rw [div_eq_mul_inv, mul_comm]

/-- Probability normalization recovers the actual matrix-ball volume from
the supplied law, with precisely the factorial-product normalizer. -/
theorem matrixBall_volume (T : TruncatedHaarInput) (r s : ℕ)
    (hr : 0 < r) (hrs : r ≤ s) (μ : Measure (FrameSpace r s))
    (hμ : IsHaarFrameDistribution μ) :
    matrixLebesgue r s (matrixBall r s) =
      ENNReal.ofReal (VolumeRates.graphNormalizer s r) := by
  haveI : IsProbabilityMeasure μ := hμ.probability
  have h := bottom_probability T r s hr hrs μ hμ Set.univ MeasurableSet.univ
  simp only [Set.preimage_univ, Set.univ_inter, measure_univ] at h
  exact (ENNReal.div_eq_one_iff
    (ENNReal.ofReal_ne_zero_iff.2 (graphNormalizer_pos s r)) ENNReal.ofReal_ne_top).1 h.symm

theorem matrixBall_volume_ne_top (T : TruncatedHaarInput) (r s : ℕ)
    (hr : 0 < r) (hrs : r ≤ s) (μ : Measure (FrameSpace r s))
    (hμ : IsHaarFrameDistribution μ) :
    matrixLebesgue r s (matrixBall r s) ≠ ∞ := by
  rw [matrixBall_volume T r s hr hrs μ hμ]
  exact ENNReal.ofReal_ne_top

theorem matrixBall_volume_toReal (T : TruncatedHaarInput) (r s : ℕ)
    (hr : 0 < r) (hrs : r ≤ s) (μ : Measure (FrameSpace r s))
    (hμ : IsHaarFrameDistribution μ) :
    (matrixLebesgue r s (matrixBall r s)).toReal = VolumeRates.graphNormalizer s r := by
  rw [matrixBall_volume T r s hr hrs μ hμ,
    ENNReal.toReal_ofReal (graphNormalizer_pos s r).le]

/-- For arbitrary matrix sets, the correct statement is an outer-measure
upper bound. It follows from the measurable bottom map and the measure law,
without requiring a measurable success set. -/
theorem bottom_probability_le (T : TruncatedHaarInput) (r s : ℕ)
    (hr : 0 < r) (hrs : r ≤ s) (μ : Measure (FrameSpace r s))
    (hμ : IsHaarFrameDistribution μ) (S : Set (TailMatrix r s)) :
    μ ((bottomMap r s) ⁻¹' S) ≤
      matrixLebesgue r s S / ENNReal.ofReal (VolumeRates.graphNormalizer s r) := by
  calc
    _ ≤ (Measure.map (bottomMap r s) μ) S :=
      Measure.le_map_apply (measurable_bottomMap r s).aemeasurable S
    _ = (ENNReal.ofReal (VolumeRates.graphNormalizer s r))⁻¹ *
        ((matrixLebesgue r s).restrict (matrixBall r s)) S := by
      rw [T.bottom_law r s hr hrs μ hμ, Measure.smul_apply, smul_eq_mul]
    _ ≤ (ENNReal.ofReal (VolumeRates.graphNormalizer s r))⁻¹ * matrixLebesgue r s S :=
      mul_le_mul_left' (Measure.restrict_apply_le _ _) _
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

/-- Any actual frame event whose bottom matrices lie in `S` inherits the
volume-ratio bound. Both sets may be nonmeasurable: only outer measures are
used in this inequality. -/
theorem event_probability_le (T : TruncatedHaarInput) (r s : ℕ)
    (hr : 0 < r) (hrs : r ≤ s) (μ : Measure (FrameSpace r s))
    (hμ : IsHaarFrameDistribution μ) (E : Set (FrameSpace r s))
    (S : Set (TailMatrix r s)) (hES : E ⊆ (bottomMap r s) ⁻¹' S) :
    μ E ≤ matrixLebesgue r s S / ENNReal.ofReal (VolumeRates.graphNormalizer s r) :=
  (measure_mono hES).trans (bottom_probability_le T r s hr hrs μ hμ S)

/-- The finite-numerator bridge from extended-real outer measures to the
ordinary real volume ratio used in Theorem 2.4. -/
theorem event_probability_toReal_le (T : TruncatedHaarInput) (r s : ℕ)
    (hr : 0 < r) (hrs : r ≤ s) (μ : Measure (FrameSpace r s))
    (hμ : IsHaarFrameDistribution μ) (E : Set (FrameSpace r s))
    (S : Set (TailMatrix r s)) (hES : E ⊆ (bottomMap r s) ⁻¹' S)
    (hfinite : matrixLebesgue r s S ≠ ∞) :
    (μ E).toReal ≤ (matrixLebesgue r s S).toReal / VolumeRates.graphNormalizer s r := by
  have hV := graphNormalizer_pos s r
  have hden : ENNReal.ofReal (VolumeRates.graphNormalizer s r) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 hV
  have h := ENNReal.toReal_mono (ENNReal.div_ne_top hfinite hden)
    (event_probability_le T r s hr hrs μ hμ E S hES)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofReal hV.le] using h

/-- A real volume-ratio bound can be lifted back to the extended-real
probability statement. Finiteness of the event measure follows from the
actual Haar probability assumption, even for a nonmeasurable event. -/
theorem event_probability_ofReal_le (T : TruncatedHaarInput) (r s : ℕ)
    (hr : 0 < r) (hrs : r ≤ s) (μ : Measure (FrameSpace r s))
    (hμ : IsHaarFrameDistribution μ) (E : Set (FrameSpace r s))
    (S : Set (TailMatrix r s)) (hES : E ⊆ (bottomMap r s) ⁻¹' S)
    (hfinite : matrixLebesgue r s S ≠ ∞) {R : ℝ}
    (hR : (matrixLebesgue r s S).toReal / VolumeRates.graphNormalizer s r ≤ R) :
    μ E ≤ ENNReal.ofReal R := by
  haveI : IsProbabilityMeasure μ := hμ.probability
  have h := (event_probability_toReal_le T r s hr hrs μ hμ E S hES hfinite).trans hR
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ E)]
  exact ENNReal.ofReal_le_ofReal h

/-- Substituting a proved Bures numerator bound gives the `6e` probability
rate. The set `E` is arbitrary; no loss-specific claim is built into the
external distribution input. -/
theorem bures_numerator_probability_rate (T : TruncatedHaarInput) (r s : ℕ)
    (hr : 0 < r) (hrs : r ≤ s) (μ : Measure (FrameSpace r s))
    (hμ : IsHaarFrameDistribution μ) (E : Set (FrameSpace r s))
    (S : Set (TailMatrix r s)) (hES : E ⊆ (bottomMap r s) ⁻¹' S)
    (hfinite : matrixLebesgue r s S ≠ ∞) (ε : ℝ) (hε : 0 < ε)
    (hnum : (matrixLebesgue r s S).toReal ≤ Real.pi ^ (r * s) *
      (3 * (r : ℝ) * Real.sqrt (r : ℝ) * ε / Real.sqrt (s : ℝ)) ^ (r * s) /
        ((r * s).factorial : ℝ)) :
    (μ E).toReal ≤ (6 * Real.exp 1 * ε * Real.sqrt ((r : ℝ) / (s : ℝ))) ^ (r * s) := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  exact (event_probability_toReal_le T r s hr hrs μ hμ E S hES hfinite).trans
    (VolumeRates.bures_graphNormalizer_rate r s hr hs hrs ε hε ENNReal.toReal_nonneg hnum)

/-- The corresponding `18e` conversion from an actual ellipsoid numerator
bound. No final probability-rate bound is an input. -/
theorem right_numerator_probability_rate (T : TruncatedHaarInput) (r s : ℕ)
    (hr : 0 < r) (hrs : r ≤ s) (μ : Measure (FrameSpace r s))
    (hμ : IsHaarFrameDistribution μ) (E : Set (FrameSpace r s))
    (S : Set (TailMatrix r s)) (hES : E ⊆ (bottomMap r s) ⁻¹' S)
    (hfinite : matrixLebesgue r s S ≠ ∞) (ε : ℝ) (hε : 0 < ε)
    (hnum : (matrixLebesgue r s S).toReal ≤ Real.pi ^ (r * s) *
      (9 * (r : ℝ) ^ 2 * ε ^ 2 / (s : ℝ)) ^ (r * s) /
        ((r * s).factorial : ℝ)) :
    (μ E).toReal ≤ (18 * Real.exp 1 * (r : ℝ) * ε ^ 2 / (s : ℝ)) ^ (r * s) := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  exact (event_probability_toReal_le T r s hr hrs μ hμ E S hES hfinite).trans
    (VolumeRates.rightInverse_graphNormalizer_rate r s hr hs hrs ε hε ENNReal.toReal_nonneg hnum)

/-- A separate ordinary Haar-nullity input for a fixed proper complex
subspace. It is stated on actual frame column ranges, with no singular loss
or successful event in its hypotheses or conclusion. This is the standard
first-Haar-column subspace-nullity consequence, kept separate from the
rectangular matrix-ball law. -/
structure ProperSubspaceNullInput (ι κ : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] : Prop where
  null_containment : ∀ (μ : Measure (Frame ι κ)), IsHaarFrameDistribution μ →
    ∀ (W : Submodule ℂ (ι → ℂ)), W ≠ ⊤ →
      μ {U | ∀ v : κ → ℂ, U.matrix *ᵥ v ∈ W} = 0

/-- Any event forcing all frame columns into a fixed proper subspace is
null. This generic consequence does not mention a tomography loss. -/
theorem event_null_of_column_containment {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (N : ProperSubspaceNullInput ι κ) (μ : Measure (Frame ι κ))
    (hμ : IsHaarFrameDistribution μ) (W : Submodule ℂ (ι → ℂ)) (hW : W ≠ ⊤)
    (E : Set (Frame ι κ))
    (hE : E ⊆ {U | ∀ v : κ → ℂ, U.matrix *ᵥ v ∈ W}) : μ E = 0 := by
  have h : μ E ≤ μ {U | ∀ v : κ → ℂ, U.matrix *ᵥ v ∈ W} := measure_mono hE
  rw [N.null_containment μ hμ W hW] at h
  exact le_antisymm h (zero_le _)

end Paper26.HaarTruncation
