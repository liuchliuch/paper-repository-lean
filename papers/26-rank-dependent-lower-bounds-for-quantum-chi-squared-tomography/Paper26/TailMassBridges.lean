import Paper26.TailMass
import Paper26.Normalization

/-!
# Local spectral-calculus bridges for Lemma 2.2

This module retains only a raw Hermitian-compression spectral/min-max input.
It supplies a rectangular orthonormal eigenbasis `U` for the actual range of
`P`, with `Uᴴ U = I`, `U Uᴴ = P`, and `Uᴴ sigma U = diagonal lambda`.
The only comparison field is the standard pointwise compression interlacing
against a leading-r projector (Bhatia, Matrix Analysis, Chapter III).

All trace and square-root trace formulas are proved below using these actual
matrix identities and Mathlib's positive square-root uniqueness.  No fidelity
formula and no functional-calculus specialization is an external input.
The principal-angle input is also eliminated: applying scalar Cauchy--Schwarz
to the compression of `Q/r` proves `t <= BuresDistance(P/r,Q/r)^2` directly.
The earlier `TailMass` proofs are preserved; the final theorems here use none
of `CompressionInput` or `PrincipalAngleInput` from that earlier interface.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder ENNReal

namespace Paper26.TailMassBridges

open QuantumModel TailMass Normalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Raw spectral theorem for Hermitian compressions, with the usual min-max
interlacing.  Every field is an actual matrix identity or an eigenvalue fact. -/
structure RawCompressionInput (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℕ) where
  values : Density ι → RankProjector ι r → Fin r → ℝ
  basis : Density ι → RankProjector ι r → Matrix ι (Fin r) ℂ
  nonneg : ∀ σ P i, 0 ≤ values σ P i
  decreasing : ∀ σ P, Antitone (values σ P)
  isometry : ∀ σ P, (basis σ P)ᴴ * basis σ P = 1
  range_projection : ∀ σ P, basis σ P * (basis σ P)ᴴ = P.matrix
  compressed_diagonal : ∀ σ P,
    (basis σ P)ᴴ * σ.matrix * basis σ P = diagonalMatrix (values σ P)
  leading_interlacing : ∀ σ P Q, Leading σ Q → ∀ i, values σ P i ≤ values σ Q i

lemma sqrt_projector {r : ℕ} (P : RankProjector ι r) :
    CFC.sqrt P.matrix = P.matrix :=
  CFC.sqrt_unique P.projector.idempotent P.projector.positive.nonneg

lemma sqrt_real_smul (X : Matrix ι ι ℂ) (hX : X.PosSemidef)
    (c : ℝ) (hc : 0 ≤ c) : CFC.sqrt (c • X) = Real.sqrt c • CFC.sqrt X := by
  apply CFC.sqrt_unique
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [CFC.sqrt_mul_sqrt_self X hX.nonneg, Real.mul_self_sqrt hc]
  · exact ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg X)).smul (Real.sqrt_nonneg c)).nonneg

lemma flat_matrix {r : ℕ} (P : RankProjector ι r) (hr : 0 < r) :
    (P.flat hr).matrix = (r : ℝ)⁻¹ • P.matrix := by
  simp only [RankProjector.flat, OrthogonalProjector.flat, P.rank_eq]

lemma sqrt_flat {r : ℕ} (P : RankProjector ι r) (hr : 0 < r) :
    CFC.sqrt (P.flat hr).matrix = Real.sqrt ((r : ℝ)⁻¹) • P.matrix := by
  rw [flat_matrix, sqrt_real_smul P.matrix P.projector.positive _
    (inv_nonneg.mpr (Nat.cast_nonneg _)), sqrt_projector]

/-- The positive square root of an actual rectangular spectral decomposition. -/
lemma sqrt_rect_spectral {r : ℕ} (U : Matrix ι (Fin r) ℂ) (a : Fin r → ℝ)
    (hU : Uᴴ * U = 1) (ha : ∀ i, 0 ≤ a i) :
    CFC.sqrt (U * diagonalMatrix a * Uᴴ) =
      U * diagonalMatrix (fun i => Real.sqrt (a i)) * Uᴴ := by
  let D := diagonalMatrix (fun i => Real.sqrt (a i))
  have hDD : D * D = diagonalMatrix a := by
    dsimp [D, diagonalMatrix]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (ha i)]
  apply CFC.sqrt_unique
  · change (U * D * Uᴴ) * (U * D * Uᴴ) = _
    calc
      _ = U * D * (Uᴴ * U) * D * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * diagonalMatrix a * Uᴴ := by
        rw [hU, Matrix.mul_one, Matrix.mul_assoc U D D, hDD]
  · have hD : D.PosSemidef := Matrix.PosSemidef.diagonal fun i =>
      RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg (a i))
    exact (hD.mul_mul_conjTranspose_same U).nonneg

lemma trace_rect_spectral {r : ℕ} (U : Matrix ι (Fin r) ℂ) (a : Fin r → ℝ)
    (hU : Uᴴ * U = 1) :
    (Matrix.trace (U * diagonalMatrix a * Uᴴ)).re = ∑ i, a i := by
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  simp [diagonalMatrix, Matrix.trace_diagonal, Complex.re_sum]

lemma compression_decomposition {r : ℕ} (C : RawCompressionInput ι r)
    (σ : Density ι) (P : RankProjector ι r) :
    P.matrix * σ.matrix * P.matrix =
      C.basis σ P * diagonalMatrix (C.values σ P) * (C.basis σ P)ᴴ := by
  rw [← C.compressed_diagonal σ P, ← C.range_projection σ P]
  simp only [Matrix.mul_assoc]

/-- Ordinary trace compression is a local consequence of the raw spectral basis. -/
theorem compression_trace {r : ℕ} (C : RawCompressionInput ι r)
    (σ : Density ι) (P : RankProjector ι r) :
    (Matrix.trace (P.matrix * σ.matrix)).re = ∑ i, C.values σ P i := by
  have he : Matrix.trace (P.matrix * σ.matrix * P.matrix) =
      Matrix.trace (P.matrix * σ.matrix) := by
    rw [Matrix.trace_mul_cycle, P.projector.idempotent]
  rw [← he, compression_decomposition C σ P,
    trace_rect_spectral _ _ (C.isometry σ P)]

/-- Square-root trace is proved using CFC square-root uniqueness, with no new
external functional-calculus or fidelity identity. -/
theorem compression_sqrt_trace {r : ℕ} (C : RawCompressionInput ι r)
    (σ : Density ι) (P : RankProjector ι r) :
    (Matrix.trace (CFC.sqrt (P.matrix * σ.matrix * P.matrix))).re =
      ∑ i, Real.sqrt (C.values σ P i) := by
  rw [compression_decomposition C σ P,
    sqrt_rect_spectral _ _ (C.isometry σ P) (C.nonneg σ P),
    trace_rect_spectral _ _ (C.isometry σ P)]

/-- The flat-state fidelity formula is derived from the actual matrix square roots. -/
theorem flat_fidelity_formula {r : ℕ} (C : RawCompressionInput ι r)
    (σ : Density ι) (P : RankProjector ι r) (hr : 0 < r) :
    rootFidelity (P.flat hr) σ =
      (∑ i, Real.sqrt (C.values σ P i)) / Real.sqrt (r : ℝ) := by
  have hc : 0 ≤ (r : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcomp : (P.matrix * σ.matrix * P.matrix).PosSemidef := by
    simpa only [P.projector.hermitian.eq] using
      σ.positive.conjTranspose_mul_mul_same P.matrix
  unfold rootFidelity
  rw [sqrt_flat P hr]
  have hi : (Real.sqrt ((r : ℝ)⁻¹) • P.matrix) * σ.matrix *
      (Real.sqrt ((r : ℝ)⁻¹) • P.matrix) =
        (r : ℝ)⁻¹ • (P.matrix * σ.matrix * P.matrix) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [Real.mul_self_sqrt hc]
  rw [hi, sqrt_real_smul _ hcomp _ hc, Matrix.trace_smul]
  simp only [Complex.smul_re, smul_eq_mul]
  change Real.sqrt ((r : ℝ)⁻¹) *
    (Matrix.trace (CFC.sqrt (P.matrix * σ.matrix * P.matrix))).re = _
  rw [compression_sqrt_trace C σ P, Real.sqrt_inv]
  ring

/-- The Cauchy step, now using the derived (rather than externally supplied) fidelity formula. -/
theorem flat_fidelity_sq_le_trace {r : ℕ} (C : RawCompressionInput ι r)
    (σ : Density ι) (P : RankProjector ι r) (hr : 0 < r) :
    rootFidelity (P.flat hr) σ ^ 2 ≤ (Matrix.trace (P.matrix * σ.matrix)).re := by
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin r => Real.sqrt (C.values σ P i)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  simp_rw [Real.sq_sqrt (C.nonneg σ P _)] at hcs
  rw [flat_fidelity_formula C σ P hr, div_pow, Real.sq_sqrt hrR.le, compression_trace C σ P]
  exact (div_le_iff₀ hrR).mpr (by simpa [mul_comm] using hcs)

lemma subspaceTail_eq_flat_trace {r : ℕ} (P Q : RankProjector ι r) (hr : 0 < r) :
    subspaceTail P Q = 1 - (Matrix.trace (P.matrix * (Q.flat hr).matrix)).re := by
  have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  have ht : (Matrix.trace P.matrix).re = (r : ℝ) := by
    rw [P.projector.trace_eq_rank, P.rank_eq]
    simp
  rw [flat_matrix, Matrix.mul_smul, Matrix.trace_smul]
  simp only [Complex.smul_re, smul_eq_mul]
  unfold subspaceTail
  change (Matrix.trace (P.matrix * (1 - Q.matrix))).re / (r : ℝ) =
    1 - (r : ℝ)⁻¹ * (Matrix.trace (P.matrix * Q.matrix)).re
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re, ht]
  field_simp [hrR]
  <;> ring

/-- The projector residual comparison needs no CS/principal-angle input:
compression Cauchy and `(f-1)^2 >= 0` already suffice. -/
theorem subspaceTail_le_bures_sq {r : ℕ} (F : BuresMetricInput ι)
    (C : RawCompressionInput ι r) (P Q : RankProjector ι r) (hr : 0 < r) :
    subspaceTail P Q ≤ buresDistance (P.flat hr) (Q.flat hr) ^ 2 := by
  have h := flat_fidelity_sq_le_trace C (Q.flat hr) P hr
  rw [subspaceTail_eq_flat_trace P Q hr, buresDistance_sq F]
  nlinarith [sq_nonneg (rootFidelity (P.flat hr) (Q.flat hr) - 1)]

end Paper26.TailMassBridges

namespace Paper26.TailMassBridges

open QuantumModel TailMass
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma leading_trace_maximal {r : ℕ} (C : RawCompressionInput ι r)
    (σ : Density ι) (P Q : RankProjector ι r) (hQ : Leading σ Q) :
    (Matrix.trace (P.matrix * σ.matrix)).re ≤ (Matrix.trace (Q.matrix * σ.matrix)).re := by
  rw [compression_trace C σ P, compression_trace C σ Q]
  exact Finset.sum_le_sum fun i _ => C.leading_interlacing σ P Q hQ i

lemma leading_fidelity_maximal {r : ℕ} (C : RawCompressionInput ι r)
    (σ : Density ι) (P Q : RankProjector ι r) (hr : 0 < r) (hQ : Leading σ Q) :
    rootFidelity (P.flat hr) σ ≤ rootFidelity (Q.flat hr) σ := by
  rw [flat_fidelity_formula C σ P hr, flat_fidelity_formula C σ Q hr]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact Finset.sum_le_sum fun i _ => Real.sqrt_le_sqrt (C.leading_interlacing σ P Q hQ i)

lemma leading_bures_minimal {r : ℕ} (C : RawCompressionInput ι r)
    (σ : Density ι) (P Q : RankProjector ι r) (hr : 0 < r) (hQ : Leading σ Q) :
    buresDistance (Q.flat hr) σ ≤ buresDistance (P.flat hr) σ := by
  unfold buresDistance
  apply Real.sqrt_le_sqrt
  linarith [leading_fidelity_maximal C σ P Q hr hQ]

/-- Complete tail-mass deduction with only the raw compression spectral input. -/
theorem tailMass_le_epsilon {r : ℕ} (F : BuresMetricInput ι)
    (C : RawCompressionInput ι r) (σ : Density ι) (P Q : RankProjector ι r)
    (hr : 0 < r) (hQ : Leading σ Q) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hχ : chiB (P.flat hr) σ ≤ ENNReal.ofReal ε) : tailMass σ Q ≤ ε := by
  have hb := bures_sq_le_of_chiB F (P.flat hr) σ hε.le hχ
  rw [buresDistance_sq F] at hb
  have hf : 1 - ε / 2 ≤ rootFidelity (P.flat hr) σ := by linarith
  have hp := flat_fidelity_sq_le_trace C σ P hr
  have hm := leading_trace_maximal C σ P Q hQ
  have hprod : 0 ≤ (rootFidelity (P.flat hr) σ - (1 - ε / 2)) *
      (rootFidelity (P.flat hr) σ + (1 - ε / 2)) :=
    mul_nonneg (sub_nonneg.mpr hf) (by linarith [(F.fidelity_range (P.flat hr) σ).1])
  rw [tailMass_eq_one_sub]
  nlinarith [sq_nonneg (ε / 2)]

/-- Complete subspace deduction with no principal-angle or specialized fidelity input. -/
theorem subspaceTail_le_four_epsilon {r : ℕ} (F : BuresMetricInput ι)
    (C : RawCompressionInput ι r) (σ : Density ι) (P Q : RankProjector ι r)
    (hr : 0 < r) (hQ : Leading σ Q) {ε : ℝ} (hε : 0 ≤ ε)
    (hχ : chiB (P.flat hr) σ ≤ ENNReal.ofReal ε) : subspaceTail P Q ≤ 4 * ε := by
  have hb := bures_sq_le_of_chiB F (P.flat hr) σ hε hχ
  have hbest := leading_bures_minimal C σ P Q hr hQ
  have htriangle := F.distance_triangle (P.flat hr) σ (Q.flat hr)
  rw [F.distance_symm σ (Q.flat hr)] at htriangle
  have htwo : buresDistance (P.flat hr) (Q.flat hr) ≤ 2 * buresDistance (P.flat hr) σ :=
    by linarith
  have hpq := buresDistance_nonneg (P.flat hr) (Q.flat hr)
  have hps := buresDistance_nonneg (P.flat hr) σ
  have hsquare : 0 ≤ (2 * buresDistance (P.flat hr) σ -
      buresDistance (P.flat hr) (Q.flat hr)) *
      (2 * buresDistance (P.flat hr) σ + buresDistance (P.flat hr) (Q.flat hr)) :=
    mul_nonneg (sub_nonneg.mpr htwo) (by positivity)
  have ht := subspaceTail_le_bures_sq F C P Q hr
  nlinarith

/-- Lemma 2.2 with only generic metric and raw compression/min-max external inputs.
All specialized trace and fidelity formulas are internally proved above. -/
theorem lemma_2_2_bures {r : ℕ} (F : BuresMetricInput ι)
    (C : RawCompressionInput ι r) (σ : Density ι) (P Q : RankProjector ι r)
    (hr : 0 < r) (hQ : Leading σ Q) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hχ : chiB (P.flat hr) σ ≤ ENNReal.ofReal ε) :
    tailMass σ Q ≤ ε ∧ subspaceTail P Q ≤ 4 * ε :=
  ⟨tailMass_le_epsilon F C σ P Q hr hQ hε hε1 hχ,
    subspaceTail_le_four_epsilon F C σ P Q hr hQ hε.le hχ⟩

/-- Right-inverse chi-squared gives the same actual tail bounds by the proved
loss comparison; no external right-inverse reduction is assumed. -/
theorem lemma_2_2_right {r : ℕ} (F : BuresMetricInput ι)
    (C : RawCompressionInput ι r) (σ : Density ι) (P Q : RankProjector ι r)
    (hr : 0 < r) (hQ : Leading σ Q) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hχ : chiR (P.flat hr) σ ≤ ENNReal.ofReal ε) :
    tailMass σ Q ≤ ε ∧ subspaceTail P Q ≤ 4 * ε := by
  apply lemma_2_2_bures F C σ P Q hr hQ hε hε1
  exact ((loss_comparison (P.flat hr) σ).1.trans (loss_comparison (P.flat hr) σ).2).trans hχ

end Paper26.TailMassBridges
