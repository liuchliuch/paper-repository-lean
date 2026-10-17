import Paper26.SupportCompression
import Paper26.HaarFrames
import Paper26.PureState

/-!
# Actual pure densities and matrix risk ingredients for Appendix A

The initial classification identifies every actual rank-one density with the
one-column frame model used by the covariant experiment. Loss statements below
use the actual `QuantumModel.chiB/chiR` and their support convention.

The final section proves the affine posterior candidate's positive floor,
original-basis CFC square-root trace bound, and the sharp deterministic matrix
minimum when τ is pure. The Haar posterior identity for an arbitrary collective
POVM, singular-output conditional risk, covariant expected-risk achievability,
and minimax/Bayes reduction are not asserted by this module.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal MatrixOrder
namespace Paper26.PureMinimax
open QuantumModel HaarFrames

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A selected column of an actual unitary is a genuine one-column frame. -/
def columnFrame (U : Matrix.unitaryGroup ι ℂ) (j : ι) : Frame ι (Fin 1) where
  matrix := fun i _ => (U : Matrix ι ι ℂ) i j
  orthonormal := by
    ext a b
    fin_cases a
    fin_cases b
    have h := congrArg (fun X : Matrix ι ι ℂ => X j j) (PositiveLossBridge.unitary_left U)
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] using h

lemma columnFrame_density (U : Matrix.unitaryGroup ι ℂ) (j : ι) :
    (columnFrame U j).density.matrix =
      Matrix.vecMulVec (fun i => (U : Matrix ι ι ℂ) i j)
        (star (fun i => (U : Matrix ι ι ℂ) i j)) := by
  ext i k
  simp [Frame.density_matrix, columnFrame, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.vecMulVec_apply]

lemma conjugate_single_diagonal (U : Matrix.unitaryGroup ι ℂ) (j : ι) :
    Normalization.conjugate (U : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix (Pi.single j 1)) =
        (columnFrame U j).density.matrix := by
  rw [columnFrame_density]
  ext i k
  simp only [Normalization.conjugate, Normalization.diagonalMatrix]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply,
    Pi.single_apply, Pi.star_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · simp


/-- A rank-one density has exactly one nonzero eigenvalue, which equals one;
all claims refer to the actual spectral theorem selected by `Density`. -/
lemma pure_spectrum (ρ : Density ι) (hr : ρ.matrix.rank = 1) :
    ∃ j : ι, ρ.spectrum = Pi.single j 1 := by
  classical
  have hc : Fintype.card {i // ρ.spectrum i ≠ 0} = 1 := by
    rw [← hr]
    exact ρ.hermitian.rank_eq_card_non_zero_eigs.symm
  letI : Subsingleton {i // ρ.spectrum i ≠ 0} :=
    Fintype.card_le_one_iff_subsingleton.mp hc.le
  have hn : Nonempty {i // ρ.spectrum i ≠ 0} := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨⟨j, hj⟩⟩ := hn
  have hz : ∀ k, k ≠ j → ρ.spectrum k = 0 := by
    intro k hkj
    by_contra hk
    have he : (⟨k, hk⟩ : {i // ρ.spectrum i ≠ 0}) = ⟨j, hj⟩ := Subsingleton.elim _ _
    exact hkj (congrArg Subtype.val he)
  have hsum : ∑ i, ρ.spectrum i = ρ.spectrum j := by
    apply Finset.sum_eq_single j
    · intro k _ hk
      exact hz k hk
    · simp
  have hj1 : ρ.spectrum j = 1 := hsum.symm.trans ρ.spectrum_sum
  refine ⟨j, ?_⟩
  funext k
  by_cases hk : k = j
  · subst k
    simp [hj1]
  · simp [hk, hz k hk]

/-- Every actual rank-one density is represented by a genuine one-column
orthonormal frame, with no external pure-state representation hypothesis. -/
theorem pure_density_iff_frame (ρ : Density ι) :
    ρ.matrix.rank = 1 ↔ ∃ U : Frame ι (Fin 1), ρ = U.density := by
  constructor
  · intro hr
    obtain ⟨j, hj⟩ := pure_spectrum ρ hr
    refine ⟨columnFrame ρ.eigenbasis j, CommonCenter.density_eq_of_matrix ?_⟩
    rw [PositiveLossBridge.density_spectral_reconstruction ρ, hj,
      conjugate_single_diagonal]
  · rintro ⟨U, rfl⟩
    simpa using U.density_rank


lemma density_rank_pos (ρ : Density ι) : 0 < ρ.matrix.rank := by
  classical
  have hn : ∃ i, ρ.spectrum i ≠ 0 := by
    by_contra h
    push_neg at h
    have hs := ρ.spectrum_sum
    simp [h] at hs
  obtain ⟨i, hi⟩ := hn
  rw [ρ.hermitian.rank_eq_card_non_zero_eigs]
  exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩

/-- The entire rank-at-most-one density family, rather than a chosen subset,
is exactly the one-column frame family used by the pure experiment. -/
theorem rankAtMost_one_iff_frame (ρ : Density ι) :
    ρ ∈ Density.RankAtMost 1 ↔ ∃ U : Frame ι (Fin 1), ρ = U.density := by
  rw [← pure_density_iff_frame]
  change ρ.matrix.rank ≤ 1 ↔ ρ.matrix.rank = 1
  have hp := density_rank_pos ρ
  omega

lemma pure_idempotent (ρ : Density ι) (hr : ρ.matrix.rank = 1) :
    ρ.matrix * ρ.matrix = ρ.matrix := by
  obtain ⟨U, rfl⟩ := (pure_density_iff_frame ρ).mp hr
  simpa only [Frame.density_matrix, Fintype.card_fin, Nat.cast_one, inv_one, one_smul]
    using U.projector.idempotent


/-- Rank-one density matrices are precisely trace-one rank-one orthogonal
projector matrices. -/
theorem pure_density_iff_projector (ρ : Density ι) :
    ρ.matrix.rank = 1 ↔ ∃ P : OrthogonalProjector ι,
      P.matrix.rank = 1 ∧ ρ.matrix = P.matrix := by
  constructor
  · intro hr
    exact ⟨⟨ρ.matrix, ρ.hermitian, pure_idempotent ρ hr⟩, hr, rfl⟩
  · rintro ⟨P, hP, he⟩
    rwa [he]

/-- A genuine pure input's finite right loss is linear in its matrix,
including the correct Moore–Penrose inverse for singular supported outputs. -/
theorem pure_chiR (ρ σ : Density ι) (hr : ρ.matrix.rank = 1)
    (h : SupportContained ρ σ) :
    chiR ρ σ = ENNReal.ofReal
      ((Matrix.trace (ρ.matrix * SupportCompression.pinv σ)).re - 1) := by
  rw [SupportCompression.chiR_eq_pinv_trace ρ σ h,
    SupportCompression.rightEnergy_expansion ρ σ h, pure_idempotent ρ hr]
  rfl

/-- The positive-output specialization uses the actual nonsingular inverse. -/
theorem pure_chiR_positive (ρ σ : Density ι) (hr : ρ.matrix.rank = 1)
    (hσ : σ.matrix.PosDef) :
    chiR ρ σ = ENNReal.ofReal ((Matrix.trace (ρ.matrix * σ.matrix⁻¹)).re - 1) := by
  rw [PositiveLossBridge.chiR_eq_standardRightEnergy ρ σ hσ,
    CommonCenter.standardRightEnergy_expansion ρ σ hσ, pure_idempotent ρ hr]
  rfl


/-- Complementary actual orthogonal projector. -/
def complement (P : OrthogonalProjector ι) : OrthogonalProjector ι where
  matrix := 1 - P.matrix
  hermitian := by simp [Matrix.IsHermitian, Matrix.conjTranspose_sub, P.hermitian.eq]
  idempotent := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, P.idempotent]
    abel

lemma projector_complement_mul (P : OrthogonalProjector ι) :
    P.matrix * (complement P).matrix = 0 := by
  change P.matrix * (1 - P.matrix) = 0
  rw [Matrix.mul_sub, Matrix.mul_one, P.idempotent, sub_self]

lemma complement_projector_mul (P : OrthogonalProjector ι) :
    (complement P).matrix * P.matrix = 0 := by
  change (1 - P.matrix) * P.matrix = 0
  rw [Matrix.sub_mul, Matrix.one_mul, P.idempotent, sub_self]

def outputMatrix (P : OrthogonalProjector ι) (a : ℝ) (m : ℕ) : Matrix ι ι ℂ :=
  ((1 - a : ℝ) : ℂ) • P.matrix + ((a / m : ℝ) : ℂ) • (complement P).matrix

lemma outputMatrix_inverse_product (P : OrthogonalProjector ι) (a : ℝ) (m : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hm : 0 < m) :
    outputMatrix P a m *
      ((((1 - a)⁻¹ : ℝ) : ℂ) • P.matrix + (((m / a : ℝ) : ℂ)) • (complement P).matrix) = 1 := by
  have hau : ((1 - a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (sub_pos.mpr ha1)
  have hav : ((a / m : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (div_pos ha (Nat.cast_pos.mpr hm))
  unfold outputMatrix
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, P.idempotent, (complement P).idempotent, projector_complement_mul,
    complement_projector_mul, smul_zero, add_zero, zero_add]
  have hu : ((1 - a : ℝ) : ℂ) * (((1 - a)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr ha1)), Complex.ofReal_one]
  have hv : ((a / m : ℝ) : ℂ) * (((m / a : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
    have he : (a / m : ℝ) * (m / a) = 1 := by field_simp
    rw [he, Complex.ofReal_one]
  rw [mul_comm] at hu hv
  rw [hu, hv, one_smul, one_smul]
  simp [complement]

lemma outputMatrix_posSemidef (P : OrthogonalProjector ι) (a : ℝ) (m : ℕ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) : (outputMatrix P a m).PosSemidef :=
  (P.positive.smul (RCLike.ofReal_nonneg.mpr (sub_nonneg.mpr ha1))).add
    ((complement P).positive.smul (RCLike.ofReal_nonneg.mpr
      (div_nonneg ha (Nat.cast_nonneg m))))

lemma outputMatrix_posDef (P : OrthogonalProjector ι) (a : ℝ) (m : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hm : 0 < m) : (outputMatrix P a m).PosDef := by
  apply CommonCenter.posDef_of_posSemidef_isUnit _ (outputMatrix_posSemidef P a m ha.le ha1.le)
  exact Matrix.isUnit_of_right_inverse (outputMatrix_inverse_product P a m ha ha1 hm)

/-- The source's regularized measured direction, as an actual density in any
basis. Its direction projector has true rank one. -/
def projectorOutput (P : OrthogonalProjector ι) (hP : P.matrix.rank = 1)
    (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) : Density ι where
  matrix := outputMatrix P a m
  positive := outputMatrix_posSemidef P a m ha ha1
  trace_one := by
    unfold outputMatrix
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
    simp only [complement, Matrix.trace_sub, P.trace_eq_rank, hP, Nat.cast_one,
      Matrix.trace_one, hd, Nat.cast_add, smul_eq_mul]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
    push_cast
    field_simp
    ring

lemma projectorOutput_posDef (P : OrthogonalProjector ι) (hP : P.matrix.rank = 1)
    (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    (projectorOutput P hP m hm hd a ha.le ha1.le).matrix.PosDef :=
  outputMatrix_posDef P a m ha ha1 hm

lemma projectorOutput_inverse (P : OrthogonalProjector ι) (hP : P.matrix.rank = 1)
    (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    (projectorOutput P hP m hm hd a ha.le ha1.le).matrix⁻¹ =
      (((1 - a)⁻¹ : ℝ) : ℂ) • P.matrix + (((m / a : ℝ) : ℂ)) • (complement P).matrix :=
  Matrix.inv_eq_right_inv (outputMatrix_inverse_product P a m ha ha1 hm)

/-- Equation (39) for any actual pure density and any actual measured rank-one
projector, without assuming a common eigenbasis or a two-component input. -/
theorem equation_39 (ρ : Density ι) (hr : ρ.matrix.rank = 1)
    (P : OrthogonalProjector ι) (hP : P.matrix.rank = 1)
    (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    let t := 1 - (Matrix.trace (ρ.matrix * P.matrix)).re
    chiR ρ (projectorOutput P hP m hm hd a ha.le ha1.le) =
      ENNReal.ofReal ((1 - t) / (1 - a) + (m : ℝ) * t / a - 1) := by
  dsimp only
  rw [pure_chiR_positive _ _ hr (projectorOutput_posDef P hP m hm hd a ha ha1),
    projectorOutput_inverse P hP m hm hd a ha ha1]
  congr 1
  have hc : Matrix.trace (ρ.matrix * (complement P).matrix) =
      1 - Matrix.trace (ρ.matrix * P.matrix) := by
    simp [complement, Matrix.mul_sub, ρ.trace_one]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hc, Complex.sub_re, Complex.one_re]
  ring


lemma conjugate_pure (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι)
    (hr : ρ.matrix.rank = 1) :
    (PositiveLossBridge.conjugateDensity U ρ).matrix.rank = 1 := by
  obtain ⟨V, rfl⟩ := (pure_density_iff_frame ρ).mp hr
  have he : PositiveLossBridge.conjugateDensity U V.density = (V.rotate U).density := by
    apply CommonCenter.density_eq_of_matrix
    exact (V.rotate_density U).symm
  rw [he]
  simpa using (V.rotate U).density_rank

lemma pure_normSq (ρ : Density ι) (hr : ρ.matrix.rank = 1) (i j : ι) :
    Complex.normSq (ρ.matrix i j) = (ρ.matrix i i).re * (ρ.matrix j j).re := by
  obtain ⟨U, rfl⟩ := (pure_density_iff_frame ρ).mp hr
  simp only [Frame.density_matrix, Fintype.card_fin, Nat.cast_one, inv_one, one_smul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_one]
  simp [Complex.normSq_mul, Complex.normSq_conj, Complex.mul_conj]

def twoSpectrum (j : ι) (u v : ℝ) (i : ι) : ℝ := if i = j then u else v

omit [Fintype ι] in
lemma twoSpectrum_matrix (j : ι) (u v : ℝ) :
    Normalization.diagonalMatrix (twoSpectrum j u v) =
      (u : ℂ) • Normalization.diagonalMatrix (Pi.single j 1) +
        (v : ℂ) • (1 - Normalization.diagonalMatrix (Pi.single j 1)) := by
  ext i k
  by_cases hik : i = k
  · subst k
    by_cases hij : i = j <;>
      simp [Normalization.diagonalMatrix, twoSpectrum, Pi.single_apply, hij]
  · simp [Normalization.diagonalMatrix, hik]

/-- Every measured rank-one projector admits the actual two-eigenvalue output
representation. This follows from the spectral theorem, without ordering it. -/
lemma projectorOutput_spectral (P : OrthogonalProjector ι) (hP : P.matrix.rank = 1)
    (m : ℕ) (a : ℝ) :
    ∃ (U : Matrix.unitaryGroup ι ℂ) (j : ι),
      P.matrix = Normalization.conjugate (U : Matrix ι ι ℂ)
        (Normalization.diagonalMatrix (Pi.single j 1)) ∧
      outputMatrix P a m = Normalization.conjugate (U : Matrix ι ι ℂ)
        (Normalization.diagonalMatrix (twoSpectrum j (1 - a) (a / m))) := by
  let ρ := P.flat (by omega : 0 < P.matrix.rank)
  have hρ : ρ.matrix = P.matrix := by simp [ρ, OrthogonalProjector.flat, hP]
  have hrρ : ρ.matrix.rank = 1 := by rw [hρ, hP]
  obtain ⟨j, hj⟩ := pure_spectrum ρ hrρ
  have hrec := PositiveLossBridge.density_spectral_reconstruction ρ
  rw [hρ, hj] at hrec
  refine ⟨ρ.eigenbasis, j, hrec, ?_⟩
  rw [twoSpectrum_matrix, Normalization.conjugate_add,
    Normalization.conjugate_smul, Normalization.conjugate_smul,
    Normalization.conjugate_sub, ← hrec]
  have hi : Normalization.conjugate (ρ.eigenbasis : Matrix ι ι ℂ) 1 = 1 := by
    simpa only [Normalization.conjugate, Matrix.mul_one] using
      PositiveLossBridge.unitary_right ρ.eigenbasis
  rw [hi]
  rfl

lemma sum_twoSpectrum (j : ι) (u v : ℝ) (p : ι → ℝ) (hs : ∑ i, p i = 1)
    (f : ℝ → ℝ) :
    (∑ i, f (twoSpectrum j u v i) * p i) = f u * p j + f v * (1 - p j) := by
  calc
    _ = ∑ i, ((if i = j then (f u - f v) * p j else 0) + f v * p i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hij : i = j
      · subst i
        simp [twoSpectrum]
        ring
      · simp [twoSpectrum, hij]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs]
      simp
      ring

lemma weighted_twoSpectrum (j : ι) (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (p : ι → ℝ) (hs : ∑ i, p i = 1) :
    (∑ i, ∑ k, (2 / (twoSpectrum j u v i + twoSpectrum j u v k)) * p i * p k) =
      p j ^ 2 / u + (1 - p j) ^ 2 / v + 4 * p j * (1 - p j) / (u + v) := by
  calc
    _ = ∑ i, (∑ k, (2 / (twoSpectrum j u v i + twoSpectrum j u v k)) * p k) * p i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [sum_twoSpectrum j u v p hs
          (fun x => ∑ k, 2 / (x + twoSpectrum j u v k) * p k),
        sum_twoSpectrum j u v p hs (fun x => 2 / (u + x)),
        sum_twoSpectrum j u v p hs (fun x => 2 / (v + x))]
      field_simp [ne_of_gt hu, ne_of_gt hv, ne_of_gt (add_pos hu hv)]
      ring

lemma coordinatesDensity (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) :
    (PositiveLossBridge.conjugateDensity (star U) ρ).matrix =
      Normalization.coordinates (U : Matrix ι ι ℂ) ρ.matrix := by
  simp only [PositiveLossBridge.conjugateDensity_matrix, unitary.coe_star,
    Matrix.star_eq_conjTranspose, Normalization.conjugate, Normalization.coordinates,
    Matrix.conjTranspose_conjTranspose]

lemma overlap_coordinates (U : Matrix.unitaryGroup ι ℂ) (j : ι) (ρ : Density ι)
    (P : OrthogonalProjector ι)
    (hP : P.matrix = Normalization.conjugate (U : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix (Pi.single j 1))) :
    (Matrix.trace (ρ.matrix * P.matrix)).re =
      (Normalization.coordinates (U : Matrix ι ι ℂ) ρ.matrix j j).re := by
  have hr : ρ.matrix = Normalization.conjugate (U : Matrix ι ι ℂ)
      (Normalization.coordinates (U : Matrix ι ι ℂ) ρ.matrix) :=
    (Normalization.conjugate_coordinates _ _ (PositiveLossBridge.unitary_right U)).symm
  rw [hP, hr, ← Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U),
    Normalization.trace_conjugate _ _ (PositiveLossBridge.unitary_left U),
    Normalization.coordinates_conjugate _ _ (PositiveLossBridge.unitary_left U)]
  congr 1
  simp only [Normalization.diagonalMatrix, Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · simp


/-- Equation (38) for an arbitrary actual pure input and measured rank-one
projector. The actual spectral theorem supplies the basis, and the double sum
is grouped only by the two output eigenvalues. -/
theorem equation_38 (ρ : Density ι) (hr : ρ.matrix.rank = 1)
    (P : OrthogonalProjector ι) (hP : P.matrix.rank = 1)
    (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    let t := 1 - (Matrix.trace (ρ.matrix * P.matrix)).re
    chiB ρ (projectorOutput P hP m hm hd a ha.le ha1.le) =
      ENNReal.ofReal ((a - t) ^ 2 / (1 - a) + (m : ℝ) * t ^ 2 / a - 2 * t + a +
        4 * t * (1 - t) / (1 - a + a / (m : ℝ))) := by
  let σ := projectorOutput P hP m hm hd a ha.le ha1.le
  obtain ⟨U, j, hPmat, hσmat⟩ := projectorOutput_spectral P hP m a
  let R := PositiveLossBridge.conjugateDensity (star U) ρ
  let q := twoSpectrum j (1 - a) (a / m)
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hu : 0 < 1 - a := sub_pos.mpr ha1
  have hv : 0 < a / (m : ℝ) := div_pos ha hmR
  have hq : ∀ i, 0 < q i := by
    intro i
    dsimp [q, twoSpectrum]
    split_ifs <;> assumption
  have hspec : σ.matrix = Normalization.conjugate (U : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix q) := hσmat
  have hqsum : ∑ i, q i = 1 := by
    have ht : Matrix.trace (Normalization.diagonalMatrix q) = 1 := by
      rw [← Normalization.trace_conjugate _ _ (PositiveLossBridge.unitary_left U),
        ← hspec, σ.trace_one]
    simpa only [Normalization.diagonalMatrix, Matrix.trace_diagonal,
      Complex.re_sum, Complex.ofReal_re, Complex.one_re] using congrArg Complex.re ht
  have hpsum : ∑ i, (R.matrix i i).re = 1 := by
    simpa only [Matrix.trace, Matrix.diag, Complex.re_sum, Complex.one_re] using
      congrArg Complex.re R.trace_one
  have hRpure : R.matrix.rank = 1 := conjugate_pure (star U) ρ hr
  have hb : Normalization.standardBuresEnergy ρ.matrix σ.matrix =
      Normalization.buresEnergy R.matrix q := by
    rw [hspec, PositiveLossBridge.standardBuresEnergy_spectral _ _ _
      (PositiveLossBridge.unitary_left U) (PositiveLossBridge.unitary_right U) ρ.hermitian hq,
      ← coordinatesDensity U ρ]
    exact (PositiveLossBridge.buresEnergy_eq_spectral R.matrix q).symm
  have hw : ∀ i, 2 / (q i + q i) = 1 / q i := by
    intro i
    field_simp [ne_of_gt (hq i)]
    ring
  have he : Normalization.buresEnergy R.matrix q =
      (R.matrix j j).re ^ 2 / (1 - a) + (1 - (R.matrix j j).re) ^ 2 / (a / m) +
        4 * (R.matrix j j).re * (1 - (R.matrix j j).re) / (1 - a + a / m) - 1 := by
    unfold Normalization.buresEnergy
    rw [Normalization.spectralEnergy_expansion _ _ _ (fun i => ne_of_gt (hq i)) hw,
      hpsum, hqsum]
    simp_rw [pure_normSq R hRpure, ← mul_assoc]
    rw [weighted_twoSpectrum j (1 - a) (a / m) hu hv
      (fun i => (R.matrix i i).re) hpsum]
    ring
  have hc : (Matrix.trace (ρ.matrix * P.matrix)).re = (R.matrix j j).re := by
    rw [overlap_coordinates U j ρ P hPmat]
    exact congrArg (fun X : Matrix ι ι ℂ => (X j j).re) (coordinatesDensity U ρ).symm
  dsimp only
  change chiB ρ σ = _
  rw [PositiveLossBridge.chiB_eq_standardBuresEnergy _ _
    (projectorOutput_posDef P hP m hm hd a ha ha1), hb, he, hc]
  congr 1
  field_simp [ne_of_gt hu, ne_of_gt ha, ne_of_gt hmR, ne_of_gt (add_pos hu hv)]
  ring


/-- Actual infidelity to the measured pure direction. -/
def tailMass (ρ : Density ι) (P : OrthogonalProjector ι) : ℝ :=
  1 - (Matrix.trace (ρ.matrix * P.matrix)).re

lemma tailMass_mem_unit (ρ : Density ι) (P : OrthogonalProjector ι) :
    0 ≤ tailMass ρ P ∧ tailMass ρ P ≤ 1 := by
  have hc := TailConvexity.pairing_nonneg_psd ρ.matrix P.matrix ρ.positive P.positive
  have ht := TailConvexity.pairing_nonneg_psd ρ.matrix (complement P).matrix
    ρ.positive (complement P).positive
  change 0 ≤ (Matrix.trace (ρ.matrix * P.matrix)).re at hc
  change 0 ≤ (Matrix.trace (ρ.matrix * (1 - P.matrix))).re at ht
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, ρ.trace_one,
    Complex.sub_re, Complex.one_re] at ht
  exact ⟨ht, by unfold tailMass; linarith⟩

/-- The source Bures success event now implies strict success for every actual
pure input and measured pure direction, rather than a single canonical vector. -/
theorem bures_epsilon (ρ : Density ι) (hr : ρ.matrix.rank = 1)
    (P : OrthogonalProjector ι) (hP : P.matrix.rank = 1)
    (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ht : tailMass ρ P ≤ (ε / 16) / Real.sqrt (m : ℝ)) :
    chiB ρ (projectorOutput P hP m hm hd (ε / 16) (by positivity) (by linarith)) <
      ENNReal.ofReal ε := by
  let k : Fin m := ⟨0, hm⟩
  obtain ⟨ht0, ht1⟩ := tailMass_mem_unit ρ P
  have ha : 0 < ε / 16 := by positivity
  have ha1 : ε / 16 < 1 := by linarith
  have hs := PureState.bures_epsilon k hε hε1 ht0 ht
  rw [PureState.bures_formula k ht0 ht1 ha ha1] at hs
  rw [equation_38 ρ hr P hP m hm hd (ε / 16) ha ha1]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hs

/-- The source right-inverse success event for arbitrary actual pure inputs. -/
theorem right_epsilon (ρ : Density ι) (hr : ρ.matrix.rank = 1)
    (P : OrthogonalProjector ι) (hP : P.matrix.rank = 1)
    (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ht : tailMass ρ P ≤ ε ^ 2 / (8 * (m : ℝ))) :
    chiR ρ (projectorOutput P hP m hm hd (ε / 4) (by positivity) (by linarith)) ≤
      ENNReal.ofReal ε := by
  let k : Fin m := ⟨0, hm⟩
  obtain ⟨ht0, ht1⟩ := tailMass_mem_unit ρ P
  have ha : 0 < ε / 4 := by positivity
  have ha1 : ε / 4 < 1 := by linarith
  have hs := PureState.rightInverse_epsilon k hε hε1 ht0 ht
  rw [PureState.rightInverse_formula k ht0 ht1 ha ha1] at hs
  rw [equation_39 ρ hr P hP m hm hd (ε / 4) ha ha1]
  exact ENNReal.ofReal_le_ofReal hs


section PosteriorMatrix
variable [Nonempty ι]

def posteriorSpectrum (τ : Density ι) (n : ℝ) (i : ι) : ℝ :=
  (1 + n * τ.spectrum i) / (n + Fintype.card ι)

omit [DecidableEq ι] in
lemma posterior_den_pos (n : ℝ) (hn : 0 ≤ n) : 0 < n + Fintype.card ι := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  linarith

lemma posteriorSpectrum_pos (τ : Density ι) (n : ℝ) (hn : 0 ≤ n) (i : ι) :
    0 < posteriorSpectrum τ n i :=
  div_pos (by nlinarith [mul_nonneg hn (τ.spectrum_nonneg i)]) (posterior_den_pos n hn)

lemma posteriorSpectrum_sum (τ : Density ι) (n : ℝ) (hn : 0 ≤ n) :
    ∑ i, posteriorSpectrum τ n i = 1 := by
  unfold posteriorSpectrum
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, τ.spectrum_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [add_comm, div_self (ne_of_gt (posterior_den_pos n hn))]

/-- The actual affine posterior candidate from Equation (51), constructed
as a density from τ's genuine spectral representation. No measurement moment
or posterior-mean identity is assumed by this definition. -/
def posteriorMean (τ : Density ι) (n : ℝ) (hn : 0 ≤ n) : Density ι where
  matrix := Normalization.conjugate (τ.eigenbasis : Matrix ι ι ℂ)
    (Normalization.diagonalMatrix (posteriorSpectrum τ n))
  positive := (Matrix.PosSemidef.diagonal (fun i =>
    RCLike.ofReal_nonneg.mpr (posteriorSpectrum_pos τ n hn i).le)).mul_mul_conjTranspose_same
      (τ.eigenbasis : Matrix ι ι ℂ)
  trace_one := by
    rw [Normalization.trace_conjugate _ _ (PositiveLossBridge.unitary_left τ.eigenbasis)]
    simp [Normalization.diagonalMatrix, Matrix.trace_diagonal, ← Complex.ofReal_sum,
      posteriorSpectrum_sum τ n hn]

lemma posteriorMean_posDef (τ : Density ι) (n : ℝ) (hn : 0 ≤ n) :
    (posteriorMean τ n hn).matrix.PosDef := by
  apply TailConvexity.conjugate_posDef _ _ (PositiveLossBridge.unitary_right τ.eigenbasis)
  exact Matrix.PosDef.diagonal (fun i => RCLike.ofReal_pos.mpr (posteriorSpectrum_pos τ n hn i))

lemma posteriorMean_affine (τ : Density ι) (n : ℝ) (hn : 0 ≤ n) :
    (posteriorMean τ n hn).matrix =
      (((1 / (n + Fintype.card ι) : ℝ) : ℂ)) • (1 + (n : ℂ) • τ.matrix) := by
  have hd : Normalization.diagonalMatrix (posteriorSpectrum τ n) =
      (((1 / (n + Fintype.card ι) : ℝ) : ℂ)) •
        (1 + (n : ℂ) • Normalization.diagonalMatrix τ.spectrum) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Normalization.diagonalMatrix, posteriorSpectrum, div_eq_mul_inv]
      ring
    · simp [Normalization.diagonalMatrix, hij]
  change Normalization.conjugate _ _ = _
  rw [hd, Normalization.conjugate_smul, Normalization.conjugate_add,
    Normalization.conjugate_smul, ← PositiveLossBridge.density_spectral_reconstruction τ]
  have hi : Normalization.conjugate (τ.eigenbasis : Matrix ι ι ℂ) 1 = 1 := by
    simpa only [Normalization.conjugate, Matrix.mul_one] using
      PositiveLossBridge.unitary_right τ.eigenbasis
  rw [hi]

/-- The actual posterior candidate has the required uniform positive floor. -/
lemma posteriorMean_floor (τ : Density ι) (n : ℝ) (hn : 0 ≤ n) :
    ((posteriorMean τ n hn).matrix -
      (((1 / (n + Fintype.card ι) : ℝ) : ℂ)) • (1 : Matrix ι ι ℂ)).PosSemidef := by
  rw [posteriorMean_affine, smul_add, add_sub_cancel_left, smul_smul]
  apply τ.positive.smul
  rw [← Complex.ofReal_mul]
  exact RCLike.ofReal_nonneg.mpr (mul_nonneg (one_div_nonneg.mpr (posterior_den_pos n hn).le) hn)

lemma posterior_sqrt_trace (τ : Density ι) (n : ℝ) (hn : 0 ≤ n) :
    (Matrix.trace (CFC.sqrt (posteriorMean τ n hn).matrix)).re =
      (∑ i, Real.sqrt (1 + n * τ.spectrum i)) / Real.sqrt (n + Fintype.card ι) := by
  have hd : CFC.sqrt (Normalization.diagonalMatrix (posteriorSpectrum τ n)) =
      Normalization.diagonalMatrix (fun i => Real.sqrt (posteriorSpectrum τ n i)) := by
    apply CFC.sqrt_unique
    · unfold Normalization.diagonalMatrix
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact_mod_cast Real.mul_self_sqrt (posteriorSpectrum_pos τ n hn i).le
    · exact (Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr
        (Real.sqrt_nonneg (posteriorSpectrum τ n i)))).nonneg
  change (Matrix.trace (CFC.sqrt (Normalization.conjugate _ _))).re = _
  have hp : (Normalization.diagonalMatrix (posteriorSpectrum τ n)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr
      (posteriorSpectrum_pos τ n hn i).le)
  rw [CommonCenter.cfc_sqrt_conjugate τ.eigenbasis
      (Normalization.diagonalMatrix (posteriorSpectrum τ n)) hp, hd,
    Normalization.trace_conjugate _ _ (PositiveLossBridge.unitary_left τ.eigenbasis)]
  simp only [Normalization.diagonalMatrix, Matrix.trace_diagonal, Complex.re_sum,
    Complex.ofReal_re, posteriorSpectrum]
  simp_rw [Real.sqrt_div' _ (posterior_den_pos (ι := ι) n hn).le]
  rw [← Finset.sum_div]

/-- Appendix A's spectral chord now controls the square-root trace of the
actual affine density matrix in its original basis. -/
theorem posterior_sqrt_trace_lower (τ : Density ι) (n : ℝ) (hn : 0 ≤ n) :
    (Real.sqrt (n + 1) + Fintype.card ι - 1) / Real.sqrt (n + Fintype.card ι) ≤
      (Matrix.trace (CFC.sqrt (posteriorMean τ n hn).matrix)).re := by
  rw [posterior_sqrt_trace]
  exact div_le_div_of_nonneg_right
    (Variational.posterior_sqrtTrace_lower n hn τ.spectrum τ.spectrum_nonneg τ.spectrum_sum)
    (Real.sqrt_nonneg _)

def appendixARisk (n : ℝ) : ℝ :=
  (Real.sqrt (n + 1) + Fintype.card ι - 1) ^ 2 / (n + Fintype.card ι) - 1

/-- The actual noncommuting matrix risk lower bound used after Equation (51).
The statistical identification of `posteriorMean` is a separate obligation. -/
theorem posterior_matrix_risk_lower (τ σ : Density ι) (n : ℝ) (hn : 0 ≤ n)
    (hσ : σ.matrix.PosDef) :
    appendixARisk (ι := ι) n ≤
      (Matrix.trace ((posteriorMean τ n hn).matrix * σ.matrix⁻¹)).re - 1 := by
  let M := posteriorMean τ n hn
  let S := CFC.sqrt M.matrix
  have hS : S.PosDef := (posteriorMean_posDef τ n hn).posDef_sqrt
  have hc := CommonCenter.inverseRisk_lower S σ.matrix hS.1 hσ σ.trace_one
  have hSq : S * S = M.matrix := CFC.sqrt_mul_sqrt_self M.matrix M.positive.nonneg
  rw [hSq] at hc
  have hl := posterior_sqrt_trace_lower τ n hn
  have hd := posterior_den_pos (ι := ι) n hn
  have hdim : 1 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hb0 : 0 ≤ Real.sqrt (n + 1) + Fintype.card ι - 1 := by
    linarith [Real.sqrt_nonneg (n + 1)]
  have ht0 : 0 ≤ (Matrix.trace S).re := (hS.posSemidef.trace_nonneg).1
  have hbsq := (sq_le_sq₀ (div_nonneg hb0 (Real.sqrt_nonneg _)) ht0).mpr hl
  rw [div_pow, Real.sq_sqrt hd.le] at hbsq
  unfold appendixARisk
  change _ ≤ (Matrix.trace (M.matrix * σ.matrix⁻¹)).re - 1
  change (Matrix.trace S).re ^ 2 ≤ (Matrix.trace (M.matrix * σ.matrix⁻¹)).re at hc
  linarith

/-- The conditional matrix objective has its actual square-root minimizer;
this is an attained minimum over all positive density outputs. -/
theorem posterior_matrix_minimizer (τ : Density ι) (n : ℝ) (hn : 0 ≤ n) :
    ∃ σ : Density ι, σ.matrix.PosDef ∧
      (Matrix.trace ((posteriorMean τ n hn).matrix * σ.matrix⁻¹)).re =
        (Matrix.trace (CFC.sqrt (posteriorMean τ n hn).matrix)).re ^ 2 ∧
      ∀ A : Density ι, A.matrix.PosDef →
        (Matrix.trace ((posteriorMean τ n hn).matrix * σ.matrix⁻¹)).re ≤
          (Matrix.trace ((posteriorMean τ n hn).matrix * A.matrix⁻¹)).re := by
  let M := posteriorMean τ n hn
  let S := CFC.sqrt M.matrix
  have hS : S.PosDef := (posteriorMean_posDef τ n hn).posDef_sqrt
  have hSq : S * S = M.matrix := CFC.sqrt_mul_sqrt_self M.matrix M.positive.nonneg
  refine ⟨CommonCenter.squareRootCenter S hS, CommonCenter.squareRootCenter_posDef S hS, ?_, ?_⟩
  · have he := CommonCenter.inverseRisk_center S hS
    rwa [hSq] at he
  · intro A hA
    have hl := CommonCenter.inverseRisk_lower S A.matrix hS.1 hA A.trace_one
    have he := CommonCenter.inverseRisk_center S hS
    rw [hSq] at hl he
    exact he.le.trans hl


/-- Pure τ attains the chord value, using its actual rank-one spectrum. -/
lemma posterior_sqrt_trace_pure (τ : Density ι) (hr : τ.matrix.rank = 1)
    (n : ℝ) (hn : 0 ≤ n) :
    (Matrix.trace (CFC.sqrt (posteriorMean τ n hn).matrix)).re =
      (Real.sqrt (n + 1) + Fintype.card ι - 1) / Real.sqrt (n + Fintype.card ι) := by
  rw [posterior_sqrt_trace]
  obtain ⟨j, hj⟩ := pure_spectrum τ hr
  congr 1
  calc
    _ = ∑ i : ι, (1 + if i = j then Real.sqrt (n + 1) - 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hj]
      by_cases hij : i = j
      · subst i
        simp [add_comm]
      · simp [hij]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp
      ring

/-- The deterministic matrix optimization in Appendix A is sharp when the
posterior parameter τ is pure. This is not a statement of a Haar posterior law
or of minimax risk over collective learners. -/
theorem posterior_matrix_minimizer_pure (τ : Density ι) (hr : τ.matrix.rank = 1)
    (n : ℝ) (hn : 0 ≤ n) :
    ∃ σ : Density ι, σ.matrix.PosDef ∧
      (Matrix.trace ((posteriorMean τ n hn).matrix * σ.matrix⁻¹)).re - 1 =
        appendixARisk (ι := ι) n ∧
      ∀ A : Density ι, A.matrix.PosDef →
        appendixARisk (ι := ι) n ≤
          (Matrix.trace ((posteriorMean τ n hn).matrix * A.matrix⁻¹)).re - 1 := by
  obtain ⟨σ, hσ, he, _⟩ := posterior_matrix_minimizer τ n hn
  refine ⟨σ, hσ, ?_, fun A hA => posterior_matrix_risk_lower τ A n hn hA⟩
  rw [posterior_sqrt_trace_pure τ hr n hn, div_pow,
    Real.sq_sqrt (posterior_den_pos (ι := ι) n hn).le] at he
  unfold appendixARisk
  linarith

end PosteriorMatrix

end Paper26.PureMinimax
