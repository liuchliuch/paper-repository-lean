import Paper26.HaarFrames
import Paper26.TailMassBridges
import Paper26.PositiveLossBridge

/-! Connecting the actual Haar-frame input and the tail estimates of Lemma
2.2 to the pointwise constraints used in Theorem 2.4. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal

namespace Paper26.FrameTailConstraints

open QuantumModel HaarFrames TailMass Normalization

variable {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [Fintype σ] [DecidableEq σ]

def topMask : κ ⊕ σ → ℝ := Sum.elim (fun _ => 1) (fun _ => 0)

def topProjector : OrthogonalProjector (κ ⊕ σ) where
  matrix := diagonalMatrix topMask
  hermitian := diagonalMatrix_conjTranspose _
  idempotent := by
    rw [diagonalMatrix, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    cases i <;> simp [topMask]

omit [Nonempty κ] in
theorem topProjector_trace :
    Matrix.trace (topProjector (κ := κ) (σ := σ)).matrix = (Fintype.card κ : ℂ) := by
  simp [topProjector, diagonalMatrix, topMask, Matrix.trace_diagonal,
    Fintype.sum_sum_type]

omit [Nonempty κ] in
theorem topProjector_rank :
    (topProjector (κ := κ) (σ := σ)).matrix.rank = Fintype.card κ := by
  have h := (topProjector (κ := κ) (σ := σ)).trace_eq_rank.symm.trans topProjector_trace
  exact_mod_cast h

def topRankProjector : RankProjector (κ ⊕ σ) (Fintype.card κ) :=
  ⟨topProjector, topProjector_rank⟩

def frameRankProjector (U : Frame (κ ⊕ σ) κ) :
    RankProjector (κ ⊕ σ) (Fintype.card κ) := ⟨U.projector, U.projector_rank⟩

theorem frame_flat (U : Frame (κ ⊕ σ) κ) :
    (frameRankProjector U).flat Fintype.card_pos = U.density := rfl

theorem top_leading (τ : Density (κ ⊕ σ)) (b : κ → ℝ) (a : σ → ℝ)
    (hτ : τ.matrix = diagonalMatrix (Sum.elim b a))
    (horder : ∀ i j, a j ≤ b i) : Leading τ (topRankProjector (κ := κ) (σ := σ)) := by
  refine ⟨1, Sum.elim b a, Finset.univ.image Sum.inl, by simp, by simp, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ]
  · simpa only [Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one] using hτ
  · simp only [topRankProjector, RankProjector.matrix, topProjector,
      Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    unfold diagonalMatrix
    congr 1
    funext i
    cases i <;> simp [topMask]
  · intro i hi j hj
    cases i with
    | inl i =>
      cases j with
      | inl j => simp at hj
      | inr j => exact horder i j
    | inr i => simp at hi

theorem tailMass_eq_sum (τ : Density (κ ⊕ σ)) (b : κ → ℝ) (a : σ → ℝ)
    (hτ : τ.matrix = diagonalMatrix (Sum.elim b a)) :
    TailMass.tailMass τ (topRankProjector (κ := κ) (σ := σ)) = ∑ i, a i := by
  simp [TailMass.tailMass, topRankProjector, RankProjector.matrix, topProjector,
    hτ, diagonalMatrix, Matrix.sub_mul, Matrix.diagonal_mul_diagonal, topMask,
    Matrix.trace_diagonal, Fintype.sum_sum_type, Complex.re_sum]

theorem subspaceTail_eq_bottom (U : Frame (κ ⊕ σ) κ) :
    TailMass.subspaceTail (frameRankProjector U) topRankProjector =
      TailLossConstraints.tailMass (Fintype.card κ : ℝ) U.bottom := by
  have ht : Matrix.trace (U.projector.matrix * (1 - topProjector.matrix)) =
      Matrix.trace (TailLossConstraints.bottomBlock U.projector.matrix) := by
    simp [topProjector, diagonalMatrix, Matrix.mul_sub, Matrix.trace,
      Fintype.sum_sum_type, topMask, TailLossConstraints.bottomBlock]
  change (Matrix.trace (U.projector.matrix * (1 - topProjector.matrix))).re /
      (Fintype.card κ : ℝ) = _
  rw [ht, U.bottom_projector]
  rfl

theorem bures_success_tail (F : BuresMetricInput (κ ⊕ σ))
    (C : TailMassBridges.RawCompressionInput (κ ⊕ σ) (Fintype.card κ))
    (τ : Density (κ ⊕ σ)) (b : κ → ℝ) (a : σ → ℝ)
    (hτ : τ.matrix = diagonalMatrix (Sum.elim b a)) (horder : ∀ i j, a j ≤ b i)
    (U : Frame (κ ⊕ σ) κ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hχ : chiB U.density τ ≤ ENNReal.ofReal ε) :
    (∑ i, a i) ≤ ε ∧ TailLossConstraints.tailMass (Fintype.card κ : ℝ) U.bottom ≤ 4 * ε := by
  have h := TailMassBridges.lemma_2_2_bures F C τ (frameRankProjector U)
    topRankProjector Fintype.card_pos (top_leading τ b a hτ horder) hε hε1
    (by simpa only [frame_flat] using hχ)
  simpa only [tailMass_eq_sum τ b a hτ, subspaceTail_eq_bottom] using h

theorem bures_success_H (F : BuresMetricInput (κ ⊕ σ))
    (C : TailMassBridges.RawCompressionInput (κ ⊕ σ) (Fintype.card κ))
    (τ : Density (κ ⊕ σ)) (b : κ → ℝ) (a : σ → ℝ)
    (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i)
    (hτ : τ.matrix = diagonalMatrix (Sum.elim b a)) (horder : ∀ i j, a j ≤ b i)
    (U : Frame (κ ⊕ σ) κ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hχ : chiB U.density τ ≤ ENNReal.ofReal ε) :
    (∑ i, a i) ≤ ε ∧ TailConvexity.H (diagonalMatrix a) U.bottom ≤
      9 * (Fintype.card κ : ℝ) ^ 2 * ε := by
  have htail := bures_success_tail F C τ b a hτ horder U hε hε1 hχ
  refine ⟨htail.1, ?_⟩
  have hs : ∀ i, 0 < Sum.elim b a i := by intro i; cases i <;> simp [hb, ha]
  have hpd : τ.matrix.PosDef := hτ ▸ Matrix.PosDef.diagonal
    (fun i => Complex.zero_lt_real.2 (hs i))
  have henergy := (ENNReal.ofReal_le_ofReal_iff hε.le).1
    (by simpa only [PositiveLossBridge.chiB_eq_standardBuresEnergy _ _ hpd] using hχ)
  apply TailLossConstraints.bures_success_H_bound_trace U.density.matrix U.density.hermitian
    b a hb ha (Nat.cast_pos.2 Fintype.card_pos) U.bottom U.bottom_density
    (by simpa only [← hτ] using henergy) htail.2

theorem right_success_ellipsoid (F : BuresMetricInput (κ ⊕ σ))
    (C : TailMassBridges.RawCompressionInput (κ ⊕ σ) (Fintype.card κ))
    (τ : Density (κ ⊕ σ)) (b : κ → ℝ) (a : σ → ℝ)
    (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i)
    (hτ : τ.matrix = diagonalMatrix (Sum.elim b a)) (horder : ∀ i j, a j ≤ b i)
    (U : Frame (κ ⊕ σ) κ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hχ : chiR U.density τ ≤ ENNReal.ofReal ε) :
    (∑ i, a i) ≤ ε ∧ TailLossConstraints.ellipsoidEnergy a U.bottom ≤
      9 * (Fintype.card κ : ℝ) ^ 2 * ε := by
  have hB : chiB U.density τ ≤ ENNReal.ofReal ε :=
    ((loss_comparison U.density τ).1.trans (loss_comparison U.density τ).2).trans hχ
  have htail := bures_success_tail F C τ b a hτ horder U hε hε1 hB
  refine ⟨htail.1, ?_⟩
  have hs : ∀ i, 0 < Sum.elim b a i := by intro i; cases i <;> simp [hb, ha]
  have hpd : τ.matrix.PosDef := hτ ▸ Matrix.PosDef.diagonal
    (fun i => Complex.zero_lt_real.2 (hs i))
  have henergy := (ENNReal.ofReal_le_ofReal_iff hε.le).1
    (by simpa only [PositiveLossBridge.chiR_eq_standardRightEnergy _ _ hpd] using hχ)
  have heq : standardRightEnergy U.density.matrix τ.matrix =
      rightEnergy U.density.matrix (Sum.elim b a) := by
    have ht := PositiveLossBridge.standardRightEnergy_spectral
      (1 : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) U.density.matrix (Sum.elim b a)
      (by simp) (by simp) U.density.hermitian hs
    rw [hτ, PositiveLossBridge.rightEnergy_eq_spectral]
    simpa only [conjugate, coordinates, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one] using ht
  rw [heq] at henergy
  have hsum : ∑ i, Sum.elim b a i = 1 := by
    have ht := congrArg Complex.re τ.trace_one
    simpa only [hτ, diagonalMatrix, Matrix.trace_diagonal, Complex.re_sum,
      Complex.ofReal_re, Complex.one_re] using ht
  have hflat : TailLossConstraints.flatInput (Fintype.card κ : ℝ) U.projector.matrix =
      U.density.matrix := by
    ext i j
    simp only [TailLossConstraints.flatInput, Frame.density_matrix,
      Frame.projector_matrix, Matrix.smul_apply, one_div, Complex.real_smul,
      smul_eq_mul]
  exact TailLossConstraints.right_success_ellipsoid_bound_proved U.projector.matrix
    U.projector.hermitian U.projector.idempotent b a hb ha hsum
    (Nat.cast_pos.2 Fintype.card_pos) U.projector_trace U.bottom U.bottom_projector
    (by simpa only [hflat] using henergy) htail.2

end Paper26.FrameTailConstraints
