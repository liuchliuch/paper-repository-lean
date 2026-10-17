import Paper26.ShellAccounting
import Paper26.Regularization
import Paper26.ComparisonInequalities
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Deterministic multiscale refinement on actual matrices

The stage data below record actual unitary eigenbases and nonnegative
diagonal estimates, threshold cuts, and the structural rule that later
basis changes act only on coordinates not yet frozen. Accuracy is supplied
only for the actual active-block Frobenius error. Shell, floor, tail and
normalization conclusions are not stage-data fields.

This deterministic interface does not choose a measurable eigenbasis or
construct the history-dependent measurement experiment.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal MatrixOrder

namespace Paper26.MultiscaleRefinement
open QuantumModel Normalization ShellAccounting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def projection (S : ι → Prop) [DecidablePred S] : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => if S i then 1 else 0)

def mask (S : ι → Prop) [DecidablePred S] (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i k => if S i ∧ S k then X i k else 0

theorem mask_eq_projection (S : ι → Prop) [DecidablePred S] (X : Matrix ι ι ℂ) :
    mask S X = projection S * X * projection S := by
  ext i k
  by_cases hi : S i <;> by_cases hk : S k <;>
    simp [mask, projection, Matrix.diagonal_mul, Matrix.mul_diagonal, hi, hk]

omit [DecidableEq ι] in
theorem frobeniusSq_mask_le (S : ι → Prop) [DecidablePred S] (X : Matrix ι ι ℂ) :
    frobeniusSq (mask S X) ≤ frobeniusSq X := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro k _
  by_cases h : S i ∧ S k <;> simp [mask, h]

theorem frobeniusSq_coordinates (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    frobeniusSq (coordinates (U : Matrix ι ι ℂ) X) = frobeniusSq X := by
  unfold coordinates
  rw [frobeniusSq_mul_unitary _ _ (PositiveLossBridge.unitary_right U),
    frobeniusSq_unitary_mul _ _ (by
      simpa only [Matrix.conjTranspose_conjTranspose] using PositiveLossBridge.unitary_right U)]

theorem projection_commute (S : ι → Prop) [DecidablePred S]
    (V : Matrix ι ι ℂ) (hV : ∀ i k, S i ≠ S k → V i k = 0) :
    projection S * V = V * projection S := by
  ext i k
  by_cases h : S i = S k
  · simp only [projection, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hk : S k <;> simp [h, hk]
  · simp [projection, Matrix.diagonal_mul, Matrix.mul_diagonal, hV i k h]

theorem coordinates_mask (S : ι → Prop) [DecidablePred S]
    (V : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ)
    (hV : ∀ i k, S i ≠ S k → (V : Matrix ι ι ℂ) i k = 0) :
    coordinates (V : Matrix ι ι ℂ) (mask S X) =
      mask S (coordinates (V : Matrix ι ι ℂ) X) := by
  have hp : coordinates (V : Matrix ι ι ℂ) (projection S) = projection S := by
    unfold coordinates
    rw [Matrix.mul_assoc, projection_commute S _ hV, ← Matrix.mul_assoc,
      PositiveLossBridge.unitary_left V, Matrix.one_mul]
  rw [mask_eq_projection, coordinates_mul _ _ _ (PositiveLossBridge.unitary_right V),
    coordinates_mul _ _ _ (PositiveLossBridge.unitary_right V), hp, mask_eq_projection]

theorem trace_coordinates (V : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    Matrix.trace (coordinates (V : Matrix ι ι ℂ) X) = Matrix.trace X := by
  unfold coordinates
  rw [Matrix.trace_mul_cycle, PositiveLossBridge.unitary_right V, Matrix.one_mul]

theorem coordinates_diagonal_fixed (V : Matrix ι ι ℂ) (a : ι → ℝ) (i k : ι)
    (hc : ∀ q, V q i = (1 : Matrix ι ι ℂ) q i)
    (hr : ∀ q, V i q = (1 : Matrix ι ι ℂ) i q) :
    coordinates V (diagonalMatrix a) i k = diagonalMatrix a i k := by
  unfold coordinates
  rw [Matrix.mul_apply]
  simp only [diagonalMatrix, Matrix.mul_diagonal, Matrix.conjTranspose_apply, hc]
  rw [Finset.sum_eq_single i]
  · by_cases hik : i = k
    · subst k; simp [hr]
    · simp [hr, hik]
  · intro q _ hqi
    simp [hqi]
  · simp

omit [DecidableEq ι] in
theorem sum_entryError_le_frobeniusSq (s : Finset (ι × ι)) (X : Matrix ι ι ℂ) :
    (∑ p ∈ s, entryError X p) ≤ frobeniusSq X := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun p _ _ => entryError_nonneg X p)
  simpa only [entryError, frobeniusSq, Fintype.sum_prod_type] using h

omit [Fintype ι] [DecidableEq ι] in
theorem mask_sub (S : ι → Prop) [DecidablePred S] (X Y : Matrix ι ι ℂ) :
    mask S (X - Y) = mask S X - mask S Y := by
  ext i k
  by_cases h : S i ∧ S k <;> simp [mask, h]

omit [DecidableEq ι] in
theorem frobeniusSq_mask_mono (S T : ι → Prop) [DecidablePred S] [DecidablePred T]
    (hST : ∀ i, S i → T i) (X : Matrix ι ι ℂ) :
    frobeniusSq (mask S X) ≤ frobeniusSq (mask T X) := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro k _
  by_cases h : S i ∧ S k
  · simp [mask, h, hST i h.1, hST k h.2]
  · simp only [mask, if_neg h, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _

theorem frobeniusSq_mask_diagonal (S : ι → Prop) [DecidablePred S] (a : ι → ℝ) :
    frobeniusSq (mask S (diagonalMatrix a)) = ∑ i, if S i then a i ^ 2 else 0 := by
  unfold frobeniusSq
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · by_cases hi : S i <;> simp [mask, diagonalMatrix, hi]
  · intro k _ hki
    by_cases h : S i ∧ S k <;> simp [mask, diagonalMatrix, h, Ne.symm hki]
  · simp

omit [DecidableEq ι] in
theorem frobeniusSq_three (X Y Z : Matrix ι ι ℂ) :
    frobeniusSq (X - Z) ≤ 2 * frobeniusSq (X - Y) + 2 * frobeniusSq (Y - Z) := by
  simp only [frobeniusSq, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro k _
  have h : ‖X i k - Z i k‖ ≤ ‖X i k - Y i k‖ + ‖Y i k - Z i k‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (X i k - Y i k) (Y i k - Z i k)
  change ‖X i k - Z i k‖ ^ 2 ≤ 2 * ‖X i k - Y i k‖ ^ 2 + 2 * ‖Y i k - Z i k‖ ^ 2
  nlinarith [norm_nonneg (X i k - Z i k), norm_nonneg (X i k - Y i k),
    norm_nonneg (Y i k - Z i k), sq_nonneg (‖X i k - Y i k‖ - ‖Y i k - Z i k‖)]

omit [DecidableEq ι] in
theorem frobeniusSq_mask_eq_sum (S : ι → Prop) [DecidablePred S] (X : Matrix ι ι ℂ) :
    frobeniusSq (mask S X) =
      ∑ p ∈ Finset.univ.filter (fun p : ι × ι => S p.1 ∧ S p.2), entryError X p := by
  simp only [frobeniusSq, mask, entryError, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : S i ∧ S k <;> simp [h]

omit [Fintype ι] in
theorem projection_hermitian (S : ι → Prop) [DecidablePred S] : (projection S).IsHermitian := by
  ext i k
  by_cases hik : i = k
  · subst k; by_cases hi : S i <;> simp [projection, Matrix.conjTranspose_apply, hi]
  · simp [projection, Matrix.conjTranspose_apply, hik, Ne.symm hik]

theorem mask_posSemidef (S : ι → Prop) [DecidablePred S] {X : Matrix ι ι ℂ} (hX : X.PosSemidef) :
    (mask S X).PosSemidef := by
  rw [mask_eq_projection]
  simpa only [(projection_hermitian S).eq] using hX.mul_mul_conjTranspose_same (projection S)

theorem mask_rank_le (S : ι → Prop) [DecidablePred S] (X : Matrix ι ι ℂ) :
    (mask S X).rank ≤ X.rank := by
  rw [mask_eq_projection]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem mask_trace_le (S : ι → Prop) [DecidablePred S] {X : Matrix ι ι ℂ} (hX : X.PosSemidef) :
    (Matrix.trace (mask S X)).re ≤ (Matrix.trace X).re := by
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi : 0 ≤ (X i i).re := by
    simpa [← Pi.single_star, star_one] using hX.re_dotProduct_nonneg (Pi.single i 1)
  by_cases hs : S i <;> simp [mask, hs, hi]

/-- Every actual Hermitian matrix has a support projector of no larger rank.
The projector is constructed spectrally, not supplied by an external field. -/
theorem exists_support_projector (R : Matrix ι ι ℂ) (hR : R.IsHermitian) :
    ∃ S : OrthogonalProjector ι, S.matrix * R = R ∧ S.matrix.rank ≤ R.rank := by
  let U := hR.eigenvectorUnitary
  let a := hR.eigenvalues
  let b : ι → ℝ := fun i => if a i = 0 then 0 else 1
  have hspec : R = conjugate (U : Matrix ι ι ℂ) (diagonalMatrix a) := by
    simpa only [U, a, conjugate, diagonalMatrix, Function.comp_def, Matrix.star_eq_conjTranspose] using hR.spectral_theorem
  have hb (i : ι) : b i * b i = b i := by dsimp [b]; split_ifs <;> norm_num
  have hdiag : diagonalMatrix b * diagonalMatrix b = diagonalMatrix b := by
    simp only [diagonalMatrix, Matrix.diagonal_mul_diagonal, ← Complex.ofReal_mul, hb]
  let S : OrthogonalProjector ι :=
    { matrix := conjugate (U : Matrix ι ι ℂ) (diagonalMatrix b)
      hermitian := Matrix.isHermitian_mul_mul_conjTranspose _ (diagonalMatrix_conjTranspose b)
      idempotent := by
        rw [← conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U), hdiag] }
  refine ⟨S, ?_, ?_⟩
  · change conjugate (U : Matrix ι ι ℂ) (diagonalMatrix b) * R = R
    rw [hspec, ← conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U)]
    congr 1
    simp only [diagonalMatrix, Matrix.diagonal_mul_diagonal, ← Complex.ofReal_mul]
    congr 1
    funext i
    by_cases hi : a i = 0 <;> simp [b, hi]
  · calc
      S.matrix.rank ≤ (diagonalMatrix b).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
      _ = Fintype.card {i // (b i : ℂ) ≠ 0} := Matrix.rank_diagonal _
      _ = Fintype.card {i // a i ≠ 0} := Fintype.card_congr
        (Equiv.subtypeEquivRight (fun i => by by_cases hi : a i = 0 <;> simp [b, hi]))
      _ = R.rank := hR.rank_eq_card_non_zero_eigs.symm

/-- The source's low-rank trace/Frobenius mass estimate on actual matrices. -/
theorem mass_bound (R C : Matrix ι ι ℂ) (hR : R.PosSemidef) (hC : C.PosSemidef)
    {r : ℕ} {lam η : ℝ} (hlam : 0 ≤ lam) (hr : R.rank ≤ r)
    (hupper : (lam • (1 : Matrix ι ι ℂ) - C).PosSemidef)
    (haccuracy : frobeniusSq (R - C) ≤ η) :
    (Matrix.trace R).re ≤ (r : ℝ) * lam + Real.sqrt ((r : ℝ) * η) := by
  obtain ⟨S, hSR, hSr⟩ := exists_support_projector R hR.isHermitian
  have hE : (R - C).IsHermitian := hR.isHermitian.sub hC.isHermitian
  have hcs := ComparisonInequalities.weighted_bilinear_cs (1 : Matrix ι ι ℂ)
    (R - C) S.matrix Matrix.PosSemidef.one hE S.hermitian
  have hf : TailConvexity.pairing (1 : Matrix ι ι ℂ) ((R - C) * (R - C)) = frobeniusSq (R - C) := by
    rw [frobeniusSq_eq_trace]
    simp only [TailConvexity.pairing, Matrix.one_mul, hE.eq]
  have hp : TailConvexity.pairing (1 : Matrix ι ι ℂ) (S.matrix * S.matrix) = (S.matrix.rank : ℝ) := by
    simp only [TailConvexity.pairing, Matrix.one_mul, S.idempotent, S.trace_eq_rank, Complex.natCast_re]
  have hcros : TailConvexity.pairing (1 : Matrix ι ι ℂ) (S.matrix * (R - C)) =
      TailConvexity.pairing S.matrix (R - C) := by simp [TailConvexity.pairing]
  rw [hf, hp, hcros] at hcs
  have hη : 0 ≤ η := (frobeniusSq_nonneg _).trans haccuracy
  have hsr : (S.matrix.rank : ℝ) ≤ r := by exact_mod_cast hSr.trans hr
  have hm := mul_le_mul haccuracy hsr (Nat.cast_nonneg S.matrix.rank) hη
  have hcs' : TailConvexity.pairing S.matrix (R - C) ^ 2 ≤ (r : ℝ) * η := by nlinarith
  have hn := TailConvexity.pairing_nonneg_psd S.matrix _ S.positive hupper
  have hSI : TailConvexity.pairing S.matrix (1 : Matrix ι ι ℂ) = (S.matrix.rank : ℝ) := by
    simp only [TailConvexity.pairing, Matrix.mul_one, S.trace_eq_rank, Complex.natCast_re]
  rw [TailConvexity.pairing_sub_right, WeightedTraceCS.pairing_smul_right, hSI] at hn
  have hCtrace : TailConvexity.pairing S.matrix C ≤ (r : ℝ) * lam := by nlinarith [mul_le_mul_of_nonneg_left hsr hlam]
  have hdiff : TailConvexity.pairing S.matrix (R - C) =
      (Matrix.trace R).re - TailConvexity.pairing S.matrix C := by
    rw [TailConvexity.pairing_sub_right]
    simp only [TailConvexity.pairing, hSR]
  rw [hdiff] at hcs'
  nlinarith [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg r) hη), Real.sqrt_nonneg ((r : ℝ) * η)]

def lastStage (L : ℕ) [NeZero L] : Fin L := ⟨L - 1, by have := NeZero.pos L; omega⟩

/-- Raw deterministic execution data. `frozen_update` is the actual matrix
rule for a later basis change, not an assumed error or mass invariant. -/
structure StageData (L : ℕ) [NeZero L] (lower : Fin L → ℝ) where
  basis : Fin L → Matrix.unitaryGroup ι ℂ
  estimateSpectrum : Fin L → ι → ℝ
  estimate_nonneg : ∀ j i, 0 ≤ estimateSpectrum j i
  freezeTime : ι → ℕ
  time_bound : ∀ i, freezeTime i ≤ L
  threshold_cut : ∀ j i, j.val ≤ freezeTime i →
    (freezeTime i = j.val ↔ lower j ≤ estimateSpectrum j i)
  frozen_update : ∀ j i k, freezeTime i ≤ j.val ∨ freezeTime k ≤ j.val →
    (((basis j : Matrix ι ι ℂ)ᴴ) * (basis (lastStage L) : Matrix ι ι ℂ)) i k =
      (1 : Matrix ι ι ℂ) i k

namespace StageData
variable {L : ℕ} [NeZero L] {lower : Fin L → ℝ} (D : StageData (ι := ι) L lower)

def active (j : ℕ) (i : ι) : Prop := j ≤ D.freezeTime i
instance active_decidable (j : ℕ) : DecidablePred (D.active j) :=
  fun i => inferInstanceAs (Decidable (j ≤ D.freezeTime i))

def activeProjection (j : ℕ) : Matrix ι ι ℂ := projection (D.active j)

def trueBlock (ρ : Density ι) (j : Fin L) : Matrix ι ι ℂ :=
  mask (D.active j.val) (coordinates (D.basis j : Matrix ι ι ℂ) ρ.matrix)

def estimate (j : Fin L) : Matrix ι ι ℂ :=
  mask (D.active j.val) (diagonalMatrix (D.estimateSpectrum j))

def localError (ρ : Density ι) (j : Fin L) : Matrix ι ι ℂ :=
  mask (D.active j.val) (coordinates (D.basis j : Matrix ι ι ℂ) ρ.matrix -
    diagonalMatrix (D.estimateSpectrum j))

def finalBasis : Matrix.unitaryGroup ι ℂ := D.basis (lastStage L)
def finalCoordinates (ρ : Density ι) : Matrix ι ι ℂ :=
  coordinates (D.finalBasis : Matrix ι ι ℂ) ρ.matrix

def later (j : Fin L) : Matrix.unitaryGroup ι ℂ := star (D.basis j) * D.finalBasis

def outputSpectrum (i : ι) : ℝ :=
  if h : D.freezeTime i < L then D.estimateSpectrum ⟨D.freezeTime i, h⟩ i
  else lower (lastStage L)

def outputMatrix : Matrix ι ι ℂ :=
  conjugate (D.finalBasis : Matrix ι ι ℂ) (diagonalMatrix D.outputSpectrum)

theorem estimate_posSemidef (j : Fin L) : (D.estimate j).PosSemidef := by
  rw [estimate, mask_eq_projection]
  have hp : (projection (D.active j.val))ᴴ = projection (D.active j.val) := by
    ext i k
    by_cases hik : i = k
    · subst k; by_cases hi : D.active j.val i <;> simp [projection, Matrix.conjTranspose_apply, hi]
    · simp [projection, Matrix.conjTranspose_apply, hik, Ne.symm hik]
  simpa only [hp] using (Matrix.PosSemidef.diagonal (fun i =>
    RCLike.ofReal_nonneg.mpr (D.estimate_nonneg j i))).mul_mul_conjTranspose_same
      (projection (D.active j.val))

theorem output_at_freeze (j : Fin L) (i : ι) (hi : D.freezeTime i = j.val) :
    D.outputSpectrum i = D.estimateSpectrum j i := by
  simp only [outputSpectrum, hi, dif_pos j.isLt]

theorem output_at_tail (i : ι) (hi : D.freezeTime i = L) :
    D.outputSpectrum i = lower (lastStage L) := by simp [outputSpectrum, hi]

theorem output_threshold (j : Fin L) (i : ι) (hi : D.freezeTime i = j.val) :
    lower j ≤ D.outputSpectrum i := by
  rw [D.output_at_freeze j i hi]
  exact (D.threshold_cut j i (by omega)).mp hi

theorem output_pos (hlower : ∀ j, 0 < lower j) (i : ι) : 0 < D.outputSpectrum i := by
  by_cases hi : D.freezeTime i < L
  · let j : Fin L := ⟨D.freezeTime i, hi⟩
    exact (hlower j).trans_le (D.output_threshold j i rfl)
  · have ht : D.freezeTime i = L := by have := D.time_bound i; omega
    rw [D.output_at_tail i ht]
    exact hlower _

theorem output_floor (hmono : ∀ j, lower (lastStage L) ≤ lower j) (i : ι) :
    lower (lastStage L) ≤ D.outputSpectrum i := by
  by_cases hi : D.freezeTime i < L
  · exact (hmono ⟨_, hi⟩).trans (D.output_threshold ⟨_, hi⟩ i rfl)
  · have ht : D.freezeTime i = L := by have := D.time_bound i; omega
    rw [D.output_at_tail i ht]

theorem later_fixes (j : Fin L) (i k : ι) (h : D.freezeTime i ≤ j.val ∨ D.freezeTime k ≤ j.val) :
    (D.later j : Matrix ι ι ℂ) i k = (1 : Matrix ι ι ℂ) i k :=
  D.frozen_update j i k h

theorem later_cross_zero (j : Fin L) (i k : ι) (h : D.active j.val i ≠ D.active j.val k) :
    (D.later j : Matrix ι ι ℂ) i k = 0 := by
  have hne : i ≠ k := by intro he; subst k; exact h rfl
  have ht : D.freezeTime i ≤ j.val ∨ D.freezeTime k ≤ j.val := by
    unfold active at h
    by_cases hi : j.val ≤ D.freezeTime i <;> by_cases hk : j.val ≤ D.freezeTime k <;> simp_all <;> omega
  rw [D.later_fixes j i k ht, Matrix.one_apply_ne hne]

theorem finalCoordinates_eq (ρ : Density ι) (j : Fin L) :
    coordinates (D.later j : Matrix ι ι ℂ)
      (coordinates (D.basis j : Matrix ι ι ℂ) ρ.matrix) = D.finalCoordinates ρ := by
  have he : D.basis j * D.later j = D.finalBasis := by simp [later, ← mul_assoc]
  have hm := congrArg (fun U : Matrix.unitaryGroup ι ℂ => (U : Matrix ι ι ℂ)) he
  have hc : coordinates (D.later j : Matrix ι ι ℂ)
      (coordinates (D.basis j : Matrix ι ι ℂ) ρ.matrix) =
      coordinates ((D.basis j : Matrix ι ι ℂ) * (D.later j : Matrix ι ι ℂ)) ρ.matrix := by
    simp only [coordinates, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  change (D.basis j : Matrix ι ι ℂ) * (D.later j : Matrix ι ι ℂ) =
    (D.finalBasis : Matrix ι ι ℂ) at hm
  rw [hc, hm]
  rfl

theorem shell_diagonal (j : Fin L) (i k : ι)
    (hp : (i, k) ∈ shellEntries D.freezeTime j.val) :
    coordinates (D.later j : Matrix ι ι ℂ) (diagonalMatrix (D.estimateSpectrum j)) i k =
      diagonalMatrix D.outputSpectrum i k := by
  obtain ⟨_, _, hf⟩ := mem_shellEntries_iff.mp hp
  have hdiag : (diagonalMatrix (D.estimateSpectrum j)).IsHermitian :=
    diagonalMatrix_conjTranspose _
  have hc : (coordinates (D.later j : Matrix ι ι ℂ)
      (diagonalMatrix (D.estimateSpectrum j))).IsHermitian := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      Matrix.isHermitian_mul_mul_conjTranspose (D.later j : Matrix ι ι ℂ)ᴴ hdiag
  have he : coordinates (D.later j : Matrix ι ι ℂ)
      (diagonalMatrix (D.estimateSpectrum j)) i k = diagonalMatrix (D.estimateSpectrum j) i k := by
    rcases hf with hi | hk
    · exact coordinates_diagonal_fixed _ _ i k
        (fun q => D.later_fixes j q i (Or.inr hi.le))
        (fun q => D.later_fixes j i q (Or.inl hi.le))
    · have hh := coordinates_diagonal_fixed (D.later j : Matrix ι ι ℂ)
        (D.estimateSpectrum j) k i
        (fun q => D.later_fixes j q k (Or.inr hk.le))
        (fun q => D.later_fixes j k q (Or.inl hk.le))
      rw [← hc.apply i k, hh, hdiag.apply i k]
  rw [he]
  by_cases hik : i = k
  · subst k
    have hi : D.freezeTime i = j.val := by simpa using hf
    simp [diagonalMatrix, D.output_at_freeze j i hi]
  · simp [diagonalMatrix, hik]

theorem shell_error_entry (ρ : Density ι) (j : Fin L) (i k : ι)
    (hp : (i, k) ∈ shellEntries D.freezeTime j.val) :
    (D.finalCoordinates ρ - diagonalMatrix D.outputSpectrum) i k =
      coordinates (D.later j : Matrix ι ι ℂ) (D.localError ρ j) i k := by
  have hc := coordinates_mask (D.active j.val) (D.later j)
    (coordinates (D.basis j : Matrix ι ι ℂ) ρ.matrix - diagonalMatrix (D.estimateSpectrum j))
    (D.later_cross_zero j)
  rw [coordinates_sub, D.finalCoordinates_eq ρ j] at hc
  change _ = (coordinates (D.later j : Matrix ι ι ℂ)
    (mask (D.active j.val) _)) i k
  rw [hc]
  obtain ⟨hi, hk, _⟩ := mem_shellEntries_iff.mp hp
  simp only [mask, active, hi, hk, and_self, if_true, Matrix.sub_apply]
  rw [D.shell_diagonal j i k hp]

theorem shell_error_le (ρ : Density ι) (j : Fin L) (η : ℝ)
    (haccuracy : frobeniusSq (D.localError ρ j) ≤ η) :
    (∑ p ∈ shellEntries D.freezeTime j.val,
      entryError (D.finalCoordinates ρ - diagonalMatrix D.outputSpectrum) p) ≤ η := by
  calc
    _ = ∑ p ∈ shellEntries D.freezeTime j.val,
        entryError (coordinates (D.later j : Matrix ι ι ℂ) (D.localError ρ j)) p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [entryError, entryError, D.shell_error_entry ρ j p.1 p.2 hp]
    _ ≤ frobeniusSq (coordinates (D.later j : Matrix ι ι ℂ) (D.localError ρ j)) :=
      sum_entryError_le_frobeniusSq _ _
    _ = frobeniusSq (D.localError ρ j) := frobeniusSq_coordinates _ _
    _ ≤ η := haccuracy

/-- The full new-shell energy is derived from the actual stage error and
threshold cut, retaining both ordered cross blocks. -/
theorem shell_bures_le (ρ : Density ι) (j : Fin L) (η : ℝ)
    (hlower : ∀ j, 0 < lower j) (haccuracy : frobeniusSq (D.localError ρ j) ≤ η) :
    (∑ p ∈ shellEntries D.freezeTime j.val,
      2 * entryError (D.finalCoordinates ρ - diagonalMatrix D.outputSpectrum) p /
        (D.outputSpectrum p.1 + D.outputSpectrum p.2)) ≤ 2 * η / lower j := by
  calc
    _ ≤ ∑ p ∈ shellEntries D.freezeTime j.val,
        (2 / lower j) * entryError (D.finalCoordinates ρ - diagonalMatrix D.outputSpectrum) p := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨_, _, hf⟩ := mem_shellEntries_iff.mp hp
      exact bures_weight_bound (D.output_pos hlower _).le (D.output_pos hlower _).le (hlower j)
        (hf.imp (D.output_threshold j p.1) (D.output_threshold j p.2)) (entryError_nonneg _ _)
    _ = (2 / lower j) * ∑ p ∈ shellEntries D.freezeTime j.val,
        entryError (D.finalCoordinates ρ - diagonalMatrix D.outputSpectrum) p := by rw [Finset.mul_sum]
    _ ≤ (2 / lower j) * η := mul_le_mul_of_nonneg_left (D.shell_error_le ρ j η haccuracy)
      (div_nonneg (by norm_num) (hlower j).le)
    _ = 2 * η / lower j := by ring

/-- The retained output is updated only at the new threshold shell. -/
def partialSpectrum (t : ℕ) (i : ι) : ℝ := if D.freezeTime i < t then D.outputSpectrum i else 0

theorem partialSpectrum_succ (t : ℕ) (i : ι) :
    D.partialSpectrum (t + 1) i = D.partialSpectrum t i +
      if D.freezeTime i = t then D.outputSpectrum i else 0 := by
  unfold partialSpectrum
  by_cases hlt : D.freezeTime i < t
  · have hnext : D.freezeTime i < t + 1 := by omega
    have heq : D.freezeTime i ≠ t := by omega
    simp [hlt, hnext, heq]
  · by_cases heq : D.freezeTime i = t
    · simp [heq]
    · have hnext : ¬ D.freezeTime i < t + 1 := by omega
      simp [hlt, hnext, heq]

/-- The actual block left after a stage, before diagonalizing its next estimate. -/
def remainingBlock (ρ : Density ι) (j : Fin L) : Matrix ι ι ℂ :=
  mask (fun i => j.val < D.freezeTime i) (coordinates (D.basis j : Matrix ι ι ℂ) ρ.matrix)

theorem remaining_mass_bound (ρ : Density ι) (j : Fin L) {r : ℕ} {η : ℝ}
    (hlower : 0 < lower j) (hr : ρ.matrix.rank ≤ r)
    (haccuracy : frobeniusSq (D.localError ρ j) ≤ η) :
    (Matrix.trace (D.remainingBlock ρ j)).re ≤
      min 1 ((r : ℝ) * lower j + Real.sqrt ((r : ℝ) * η)) := by
  let S : ι → Prop := fun i => j.val < D.freezeTime i
  let X := coordinates (D.basis j : Matrix ι ι ℂ) ρ.matrix
  let b : ι → ℝ := fun i => if S i then D.estimateSpectrum j i else 0
  let C := diagonalMatrix b
  have hX : X.PosSemidef := by
    simpa only [coordinates, Matrix.conjTranspose_conjTranspose] using
      ρ.positive.mul_mul_conjTranspose_same (D.basis j : Matrix ι ι ℂ)ᴴ
  have hb (i : ι) : 0 ≤ b i ∧ b i ≤ lower j := by
    by_cases hi : S i
    · have ha : j.val ≤ D.freezeTime i := Nat.le_of_lt hi
      have hne : D.freezeTime i ≠ j.val := by omega
      have hlt : D.estimateSpectrum j i < lower j :=
        lt_of_not_ge (fun h => hne ((D.threshold_cut j i ha).mpr h))
      simpa [b, hi] using And.intro (D.estimate_nonneg j i) hlt.le
    · simp [b, hi, hlower.le]
  have hC : C.PosSemidef := Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr (hb i).1)
  have hupper : (lower j • (1 : Matrix ι ι ℂ) - C).PosSemidef := by
    have he : lower j • (1 : Matrix ι ι ℂ) - C = diagonalMatrix (fun i => lower j - b i) := by
      ext i k
      by_cases hik : i = k <;> simp [C, diagonalMatrix, hik, Complex.real_smul]
    rw [he]
    exact Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr (sub_nonneg.mpr (hb i).2))
  have hCeq : C = mask S (diagonalMatrix (D.estimateSpectrum j)) := by
    ext i k
    by_cases hik : i = k
    · subst k; by_cases hi : S i <;> simp [C, b, mask, diagonalMatrix, hi]
    · simp [C, b, mask, diagonalMatrix, hik]
  have hacc : frobeniusSq (mask S X - C) ≤ η := by
    rw [hCeq, ← mask_sub]
    exact (frobeniusSq_mask_mono S (D.active j.val) (fun i hi => Nat.le_of_lt hi) _).trans haccuracy
  have hrank : (mask S X).rank ≤ r :=
    (mask_rank_le S X).trans (((Matrix.rank_mul_le_left _ _).trans
      (Matrix.rank_mul_le_right _ _)).trans hr)
  have hm := mass_bound (mask S X) C (mask_posSemidef S hX) hC hlower.le hrank hupper hacc
  have ht : (Matrix.trace X).re = 1 := by
    unfold X coordinates
    rw [Matrix.trace_mul_cycle, PositiveLossBridge.unitary_right (D.basis j), Matrix.one_mul, ρ.trace_one]
    rfl
  apply le_min
  · exact (mask_trace_le S hX).trans_eq ht
  · exact hm

/-- The current active block and the previously retained block are the same
compression, expressed in the two actual accumulated eigenbases. -/
theorem trueBlock_mass_eq_remaining (ρ : Density ι) (j k : Fin L)
    (hjk : j.val = k.val + 1) :
    (Matrix.trace (D.trueBlock ρ j)).re = (Matrix.trace (D.remainingBlock ρ k)).re := by
  have ha : coordinates (D.later j : Matrix ι ι ℂ) (D.trueBlock ρ j) =
      mask (D.active j.val) (D.finalCoordinates ρ) := by
    unfold trueBlock
    rw [coordinates_mask _ _ _ (D.later_cross_zero j), D.finalCoordinates_eq]
  have hk : coordinates (D.later k : Matrix ι ι ℂ) (D.remainingBlock ρ k) =
      mask (fun i => k.val < D.freezeTime i) (D.finalCoordinates ρ) := by
    unfold remainingBlock
    rw [coordinates_mask, D.finalCoordinates_eq]
    intro i q h
    have hne : i ≠ q := by intro he; subst q; exact h rfl
    have hf : D.freezeTime i ≤ k.val ∨ D.freezeTime q ≤ k.val := by
      by_contra hn
      have hi : k.val < D.freezeTime i := by omega
      have hq : k.val < D.freezeTime q := by omega
      exact h (propext ⟨fun _ => hq, fun _ => hi⟩)
    rw [D.later_fixes k i q hf, Matrix.one_apply_ne hne]
  have hm : mask (D.active j.val) (D.finalCoordinates ρ) =
      mask (fun i => k.val < D.freezeTime i) (D.finalCoordinates ρ) := by
    ext i q
    have hi : D.active j.val i ↔ k.val < D.freezeTime i := by unfold active; omega
    have hq : D.active j.val q ↔ k.val < D.freezeTime q := by unfold active; omega
    simp only [mask, hi, hq]
  rw [← trace_coordinates (D.later j), ha, hm, ← hk, trace_coordinates]

/-- The source mass bound is valid for the actual block passed to the next
stage, rather than merely for an unrelated compression in an old basis. -/
theorem trueBlock_mass_bound (ρ : Density ι) (j k : Fin L) (hjk : j.val = k.val + 1)
    {r : ℕ} {η : ℝ} (hlower : 0 < lower k) (hr : ρ.matrix.rank ≤ r)
    (haccuracy : frobeniusSq (D.localError ρ k) ≤ η) :
    (Matrix.trace (D.trueBlock ρ j)).re ≤
      min 1 ((r : ℝ) * lower k + Real.sqrt ((r : ℝ) * η)) := by
  rw [D.trueBlock_mass_eq_remaining ρ j k hjk]
  exact D.remaining_mass_bound ρ k hlower hr haccuracy

/-- The accumulated frozen matrix, expressed back in the original basis. -/
def partialOutput (t : ℕ) : Matrix ι ι ℂ :=
  conjugate (D.finalBasis : Matrix ι ι ℂ) (diagonalMatrix (D.partialSpectrum t))

theorem partialOutput_zero : D.partialOutput 0 = 0 := by
  simp [partialOutput, partialSpectrum, diagonalMatrix, conjugate]

/-- Each update retains exactly the new threshold shell. -/
theorem partialOutput_succ (t : ℕ) :
    D.partialOutput (t + 1) = D.partialOutput t +
      conjugate (D.finalBasis : Matrix ι ι ℂ)
        (diagonalMatrix (fun i => if D.freezeTime i = t then D.outputSpectrum i else 0)) := by
  rw [partialOutput, partialOutput, ← conjugate_add]
  congr 1
  ext i k
  by_cases hik : i = k
  · subst k
    simpa [diagonalMatrix] using congrArg (fun x : ℝ => (x : ℂ)) (D.partialSpectrum_succ t i)
  · simp [diagonalMatrix, hik]

/-- The last update is the actual scalar floor on all unfrozen coordinates. -/
theorem outputMatrix_eq_partial_add_tail :
    D.outputMatrix = D.partialOutput L +
      conjugate (D.finalBasis : Matrix ι ι ℂ)
        (diagonalMatrix (fun i => if D.freezeTime i = L then lower (lastStage L) else 0)) := by
  rw [outputMatrix, partialOutput, ← conjugate_add]
  congr 1
  ext i k
  by_cases hik : i = k
  · subst k
    by_cases ht : D.freezeTime i = L
    · simp [diagonalMatrix, partialSpectrum, ht, D.output_at_tail i ht]
    · have hlt : D.freezeTime i < L := by have := D.time_bound i; omega
      simp [diagonalMatrix, partialSpectrum, hlt, ht]
  · simp [diagonalMatrix, hik]

def tail (i : ι) : Prop := D.freezeTime i = L
instance tail_decidable : DecidablePred D.tail := fun i => inferInstanceAs (Decidable (D.freezeTime i = L))

theorem last_remainder_lt (i : ι) (hi : D.tail i) :
    D.estimateSpectrum (lastStage L) i < lower (lastStage L) := by
  have hcut := D.threshold_cut (lastStage L) i (by
    change L - 1 ≤ D.freezeTime i
    change D.freezeTime i = L at hi
    omega)
  have hne : D.freezeTime i ≠ (lastStage L).val := by
    change D.freezeTime i = L at hi
    have := (lastStage L).isLt
    omega
  exact lt_of_not_ge (fun h => hne (hcut.mpr h))

theorem tail_error_le (ρ : Density ι) (η : ℝ)
    (haccuracy : frobeniusSq (D.localError ρ (lastStage L)) ≤ η) :
    frobeniusSq (mask D.tail (D.finalCoordinates ρ - diagonalMatrix (fun _ => lower (lastStage L)))) ≤
      2 * η + 2 * (Fintype.card ι : ℝ) * lower (lastStage L) ^ 2 := by
  let R := mask D.tail (D.finalCoordinates ρ)
  let C := mask D.tail (diagonalMatrix (D.estimateSpectrum (lastStage L)))
  let F := mask D.tail (diagonalMatrix (fun _ => lower (lastStage L)))
  have hRC : frobeniusSq (R - C) ≤ η := by
    rw [← mask_sub]
    exact (frobeniusSq_mask_mono D.tail (D.active (lastStage L).val) (fun i hi => by
      change D.freezeTime i = L at hi
      change (lastStage L).val ≤ D.freezeTime i
      have := (lastStage L).isLt
      omega) _).trans haccuracy
  have hCF : frobeniusSq (C - F) ≤ (Fintype.card ι : ℝ) * lower (lastStage L) ^ 2 := by
    change frobeniusSq (mask D.tail (diagonalMatrix (D.estimateSpectrum (lastStage L))) -
      mask D.tail (diagonalMatrix (fun _ => lower (lastStage L)))) ≤ _
    rw [← mask_sub]
    have hd : diagonalMatrix (D.estimateSpectrum (lastStage L)) - diagonalMatrix (fun _ => lower (lastStage L)) =
        diagonalMatrix (fun i => D.estimateSpectrum (lastStage L) i - lower (lastStage L)) := by
      simp [diagonalMatrix, Matrix.diagonal_sub]
    rw [hd, frobeniusSq_mask_diagonal]
    calc
      _ ≤ ∑ _i : ι, lower (lastStage L) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hi
        · have h0 := D.estimate_nonneg (lastStage L) i
          have h1 := D.last_remainder_lt i hi
          nlinarith
        · exact sq_nonneg _
      _ = _ := by simp
  rw [mask_sub]
  exact (frobeniusSq_three R C F).trans (by linarith)

theorem tail_entries : shellEntries D.freezeTime L =
    Finset.univ.filter (fun p : ι × ι => D.tail p.1 ∧ D.tail p.2) := by
  ext p
  simp only [mem_shellEntries, Finset.mem_filter, Finset.mem_univ, true_and, tail]
  have h1 := D.time_bound p.1
  have h2 := D.time_bound p.2
  omega

theorem tail_bures_le (ρ : Density ι) (η : ℝ) (hlower : 0 < lower (lastStage L))
    (haccuracy : frobeniusSq (D.localError ρ (lastStage L)) ≤ η) :
    (∑ p ∈ shellEntries D.freezeTime L,
      2 * entryError (D.finalCoordinates ρ - diagonalMatrix D.outputSpectrum) p /
        (D.outputSpectrum p.1 + D.outputSpectrum p.2)) ≤
      2 * η / lower (lastStage L) + 2 * (Fintype.card ι : ℝ) * lower (lastStage L) := by
  have heq : (∑ p ∈ shellEntries D.freezeTime L,
      2 * entryError (D.finalCoordinates ρ - diagonalMatrix D.outputSpectrum) p /
        (D.outputSpectrum p.1 + D.outputSpectrum p.2)) =
      frobeniusSq (mask D.tail (D.finalCoordinates ρ - diagonalMatrix (fun _ => lower (lastStage L)))) /
        lower (lastStage L) := by
    rw [frobeniusSq_mask_eq_sum, ← D.tail_entries, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    have ht := hp
    rw [D.tail_entries] at ht
    obtain ⟨hi, hk⟩ := (Finset.mem_filter.mp ht).2
    have hei : D.outputSpectrum p.1 = lower (lastStage L) := D.output_at_tail p.1 hi
    have hek : D.outputSpectrum p.2 = lower (lastStage L) := D.output_at_tail p.2 hk
    have hentry : entryError (D.finalCoordinates ρ - diagonalMatrix D.outputSpectrum) p =
        entryError (D.finalCoordinates ρ - diagonalMatrix (fun _ => lower (lastStage L))) p := by
      unfold entryError
      simp only [Matrix.sub_apply, diagonalMatrix, Matrix.diagonal_apply]
      by_cases h : p.1 = p.2
      · simp [h, hek]
      · simp [h]
    rw [hentry, hei, hek]
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ (2 * η + 2 * (Fintype.card ι : ℝ) * lower (lastStage L) ^ 2) / lower (lastStage L) :=
      div_le_div_of_nonneg_right (D.tail_error_le ρ η haccuracy) hlower.le
    _ = _ := by field_simp

theorem energy_split (ρ : Density ι) :
    Normalization.buresEnergy (D.finalCoordinates ρ) D.outputSpectrum =
      (∑ j : Fin L, ∑ p ∈ shellEntries D.freezeTime j.val,
        2 * entryError (D.finalCoordinates ρ - diagonalMatrix D.outputSpectrum) p /
          (D.outputSpectrum p.1 + D.outputSpectrum p.2)) +
      ∑ p ∈ shellEntries D.freezeTime L,
        2 * entryError (D.finalCoordinates ρ - diagonalMatrix D.outputSpectrum) p /
          (D.outputSpectrum p.1 + D.outputSpectrum p.2) := by
  let f : ι × ι → ℝ := fun p =>
    2 * entryError (D.finalCoordinates ρ - diagonalMatrix D.outputSpectrum) p /
      (D.outputSpectrum p.1 + D.outputSpectrum p.2)
  have huniv : frozenEntries D.freezeTime (L + 1) = Finset.univ := by
    ext p
    have hp : min (D.freezeTime p.1) (D.freezeTime p.2) < L + 1 :=
      Nat.lt_succ_of_le ((min_le_left _ _).trans (D.time_bound p.1))
    constructor
    · intro _; exact Finset.mem_univ _
    · intro _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
  have hs := sum_shells D.freezeTime (L + 1) f
  rw [Finset.sum_range_succ, huniv, ← Fin.sum_univ_eq_sum_range] at hs
  rw [hs]
  simp only [Normalization.buresEnergy, spectralEnergy, f, entryError, Fintype.sum_prod_type,
    Matrix.sub_apply, Complex.normSq_eq_norm_sq]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Complete deterministic shell-plus-tail bound derived from per-stage
active-block Frobenius accuracy, without a final-error input. -/
theorem total_bures_bound (ρ : Density ι) (η : Fin L → ℝ)
    (hlower : ∀ j, 0 < lower j)
    (haccuracy : ∀ j, frobeniusSq (D.localError ρ j) ≤ η j) :
    Normalization.buresEnergy (D.finalCoordinates ρ) D.outputSpectrum ≤
      (∑ j, 2 * η j / lower j) + 2 * η (lastStage L) / lower (lastStage L) +
        2 * (Fintype.card ι : ℝ) * lower (lastStage L) := by
  rw [D.energy_split]
  have hf := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    D.shell_bures_le ρ j (η j) hlower (haccuracy j))
  have ht := D.tail_bures_le ρ (η (lastStage L)) (hlower _) (haccuracy _)
  linarith

theorem output_posDef (hlower : ∀ j, 0 < lower j) : D.outputMatrix.PosDef := by
  apply TailConvexity.conjugate_posDef _ _ (PositiveLossBridge.unitary_right D.finalBasis)
  exact Matrix.PosDef.diagonal (fun i => RCLike.ofReal_pos.mpr (D.output_pos hlower i))

section Nonempty
variable [Nonempty ι]

theorem output_trace_pos (hlower : ∀ j, 0 < lower j) : 0 < (Matrix.trace D.outputMatrix).re := by
  rw [outputMatrix, trace_conjugate_diagonal _ _ (PositiveLossBridge.unitary_left D.finalBasis)]
  exact spectrum_trace_pos D.outputSpectrum (D.output_pos hlower)

def normalizedOutput (hlower : ∀ j, 0 < lower j) : Density ι :=
  SupportCompression.normalizePSD D.outputMatrix (D.output_posDef hlower).posSemidef (D.output_trace_pos hlower)

theorem normalizedOutput_posDef (hlower : ∀ j, 0 < lower j) : (D.normalizedOutput hlower).matrix.PosDef :=
  (D.output_posDef hlower).smul (show (0 : ℂ) < ((1 / (Matrix.trace D.outputMatrix).re : ℝ) : ℂ) from
    RCLike.ofReal_pos.mpr (one_div_pos.mpr (D.output_trace_pos hlower)))

omit [Nonempty ι] in
theorem actual_energy_eq (ρ : Density ι) (hlower : ∀ j, 0 < lower j) :
    standardBuresEnergy ρ.matrix D.outputMatrix =
      Normalization.buresEnergy (D.finalCoordinates ρ) D.outputSpectrum := by
  rw [outputMatrix, PositiveLossBridge.standardBuresEnergy_spectral _ _ _
    (PositiveLossBridge.unitary_left D.finalBasis) (PositiveLossBridge.unitary_right D.finalBasis)
    ρ.hermitian (D.output_pos hlower), ← PositiveLossBridge.buresEnergy_eq_spectral]
  rfl

/-- The actual returned state is `A/Tr A`; Lemma 5.2 is applied only after
the constructed positive output and its full noncommuting energy are linked. -/
theorem normalized_chiB_le (ρ : Density ι) (hlower : ∀ j, 0 < lower j)
    (hsmall : Normalization.buresEnergy (D.finalCoordinates ρ) D.outputSpectrum ≤ 1 / 2) :
    chiB ρ (D.normalizedOutput hlower) ≤
      ENNReal.ofReal (2 * Normalization.buresEnergy (D.finalCoordinates ρ) D.outputSpectrum) := by
  rw [PositiveLossBridge.chiB_eq_standardBuresEnergy _ _ (D.normalizedOutput_posDef hlower)]
  have hs : standardBuresEnergy ρ.matrix D.outputMatrix ≤ 1 / 2 := by
    rwa [D.actual_energy_eq ρ hlower]
  have hn := ((lemma_5_2_bures_posDef ρ.matrix D.outputMatrix ρ.hermitian.eq
    (D.output_posDef hlower) ρ.trace_one).2.2 hs).2
  rw [D.actual_energy_eq ρ hlower] at hn
  exact ENNReal.ofReal_le_ofReal hn

end Nonempty

end StageData
/-- Source stage `j+1` has threshold `2^(-(j+1))`. -/
def dyadicLower (L : ℕ) (j : Fin L) : ℝ := ((2 : ℝ) ^ (j.val + 1))⁻¹

def stageAccuracy (e : ℝ) (L : ℕ) (j : Fin L) : ℝ := e * dyadicLower L j / (8 * (L : ℝ))

theorem dyadicLower_pos (L : ℕ) (j : Fin L) : 0 < dyadicLower L j := by
  unfold dyadicLower
  positivity

theorem dyadicLower_last (L : ℕ) [NeZero L] : dyadicLower L (lastStage L) = ((2 : ℝ) ^ L)⁻¹ := by
  have he : L - 1 + 1 = L := by have := NeZero.pos L; omega
  simp only [dyadicLower, lastStage, he]

theorem dyadicLower_floor (L : ℕ) [NeZero L] (j : Fin L) :
    dyadicLower L (lastStage L) ≤ dyadicLower L j := by
  rw [dyadicLower_last]
  unfold dyadicLower
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 ^ (j.val + 1))
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show j.val + 1 ≤ L by omega))

theorem stageAccuracy_sum (e : ℝ) (L : ℕ) [NeZero L] :
    (∑ j : Fin L, 2 * stageAccuracy e L j / dyadicLower L j) = e / 4 := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have he (j : Fin L) : 2 * stageAccuracy e L j / dyadicLower L j = e / (4 * (L : ℝ)) := by
    unfold stageAccuracy
    field_simp [(dyadicLower_pos L j).ne']
    ring
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem dyadic_bures_bound {L : ℕ} [NeZero L]
    (D : StageData (ι := ι) L (dyadicLower L)) (ρ : Density ι)
    {e : ℝ} (he : 0 < e) (hterminal : (Fintype.card ι : ℝ) * dyadicLower L (lastStage L) ≤ e)
    (haccuracy : ∀ j, frobeniusSq (D.localError ρ j) ≤ stageAccuracy e L j) :
    Normalization.buresEnergy (D.finalCoordinates ρ) D.outputSpectrum ≤ (5 / 2 : ℝ) * e := by
  have h := D.total_bures_bound ρ (stageAccuracy e L) (dyadicLower_pos L) haccuracy
  rw [stageAccuracy_sum] at h
  have hlast : 2 * stageAccuracy e L (lastStage L) / dyadicLower L (lastStage L) = e / (4 * (L : ℝ)) := by
    unfold stageAccuracy
    field_simp [(dyadicLower_pos L (lastStage L)).ne']
    ring
  rw [hlast] at h
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.pos L
  have hsmall : e / (4 * (L : ℝ)) ≤ e / 4 :=
    div_le_div_of_nonneg_left he.le (by norm_num) (by linarith)
  linarith

section Nonempty
variable [Nonempty ι]

/-- Actual Section 5.3 epsilon guarantee for the constructed `A/Tr A`,
conditioned only on the actual stage Frobenius estimates. -/
theorem dyadic_chiB_epsilon {L : ℕ} [NeZero L]
    (D : StageData (ι := ι) L (dyadicLower L)) (ρ : Density ι)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hterminal : (Fintype.card ι : ℝ) * dyadicLower L (lastStage L) ≤ ε / 16)
    (haccuracy : ∀ j, frobeniusSq (D.localError ρ j) ≤ stageAccuracy (ε / 16) L j) :
    chiB ρ (D.normalizedOutput (dyadicLower_pos L)) < ENNReal.ofReal ε := by
  have hE := dyadic_bures_bound D ρ (by positivity : 0 < ε / 16) hterminal haccuracy
  have hs : Normalization.buresEnergy (D.finalCoordinates ρ) D.outputSpectrum ≤ 1 / 2 := by linarith
  apply (D.normalized_chiB_le ρ (dyadicLower_pos L) hs).trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
  linarith

end Nonempty

private theorem dyadic_power_exists (d : ℕ) (e : ℝ) : ∃ L : ℕ, (d : ℝ) / e ≤ (2 : ℝ) ^ L := by
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt ((d : ℝ) / e) (by norm_num : (1 : ℝ) < 2)
  exact ⟨L, hL.le⟩

/-- Least dyadic stage count, without rounding the radius or dimension. -/
def dyadicStages (d : ℕ) (e : ℝ) : ℕ := Nat.find (dyadic_power_exists d e)

theorem dyadicStages_spec (d : ℕ) (e : ℝ) :
    (d : ℝ) / e ≤ (2 : ℝ) ^ dyadicStages d e := Nat.find_spec (dyadic_power_exists d e)

theorem dyadicStages_pos (d : ℕ) {e : ℝ} (he : 0 < e) (hed : e < d) : 0 < dyadicStages d e := by
  have hs := dyadicStages_spec d e
  by_contra h
  have hz : dyadicStages d e = 0 := by omega
  rw [hz, pow_zero] at hs
  have hh : (1 : ℝ) < (d : ℝ) / e := (lt_div_iff₀ he).2 (by simpa using hed)
  linarith

/-- The two source terminal-scale inequalities are consequences of the
least dyadic count, not assumptions about the estimator. -/
theorem dyadicStages_window (d : ℕ) {e : ℝ} (he : 0 < e) (hed : e < d) :
    (d : ℝ) * ((2 : ℝ) ^ dyadicStages d e)⁻¹ ≤ e ∧
      e / (2 * (d : ℝ)) < ((2 : ℝ) ^ dyadicStages d e)⁻¹ := by
  let L := dyadicStages d e
  have hL : 0 < L := dyadicStages_pos d he hed
  have hd : (0 : ℝ) < d := he.trans hed
  have hpow : (0 : ℝ) < 2 ^ L := by positivity
  have hs := (div_le_iff₀ he).1 (dyadicStages_spec d e)
  have hp : (2 : ℝ) ^ (L - 1) < (d : ℝ) / e := by
    apply lt_of_not_ge
    intro h
    have hmin : L ≤ L - 1 := by
      exact Nat.find_min' (dyadic_power_exists d e) h
    omega
  have hm := (lt_div_iff₀ he).1 hp
  have hexp : (2 : ℝ) ^ L = 2 * (2 : ℝ) ^ (L - 1) := by
    have hh : L = (L - 1) + 1 := by omega
    conv_lhs => rw [hh]
    rw [pow_succ]
    ring
  constructor
  · change (d : ℝ) / (2 : ℝ) ^ L ≤ e
    exact (div_le_iff₀ hpow).2 (by nlinarith [hs])
  · have hg : e / (2 * (d : ℝ)) < 1 / (2 : ℝ) ^ L := by
      apply (div_lt_div_iff₀ (by positivity) hpow).2
      rw [hexp]
      nlinarith [hm]
    simpa only [one_div] using hg

/-- The real, nonlogarithmic cost appearing in the submatrix routine. This
is an arithmetic expression, not a hypothesis that a routine exists. -/
def stageCost (r d W η : ℝ) : ℝ := r * d * W / η + d * Real.sqrt (r / η)

private theorem sqrt_mass_div_le {r η : ℝ} (hr : 0 ≤ r) (hη : 0 < η) :
    Real.sqrt (2 * r * η) / η ≤ 2 * Real.sqrt (r / η) := by
  apply (div_le_iff₀ hη).2
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hs : (2 * Real.sqrt (r / η) * η) ^ 2 = 4 * r * η := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hr hη.le)]
      field_simp
      ring
    rw [hs]
    nlinarith [mul_nonneg hr hη.le]

/-- Exact substitution in Equation 44. The final threshold window controls
all stages; the square-root terms are proved rather than hidden in an
asymptotic-cost input. -/
theorem stageCost_le {r d L e lam η W : ℝ}
    (hr : 1 ≤ r) (hrd : r ≤ d) (hL : 1 ≤ L) (he : 0 < e)
    (hlam : e / (2 * d) ≤ lam) (hη : η = e * lam / (8 * L))
    (hW : W ≤ 2 * r * lam + Real.sqrt (2 * r * η)) :
    stageCost r d W η ≤ 32 * (r * Real.sqrt r * d * Real.sqrt d * L / e) := by
  have hr0 : 0 ≤ r := by linarith
  have hd : 0 < d := by linarith
  have hL0 : 0 < L := by linarith
  have hlam0 : 0 < lam := (div_pos he (by positivity)).trans_le hlam
  have hη0 : 0 < η := by rw [hη]; positivity
  have hbase : e ^ 2 ≤ 16 * d * L * η := by
    have hb := (div_le_iff₀ (by positivity : 0 < 2 * d)).1 hlam
    have hi : 16 * d * L * η = 2 * d * (e * lam) := by
      rw [hη]
      field_simp
      ring
    rw [hi]
    nlinarith
  have hq : Real.sqrt (r / η) ≤ 4 * Real.sqrt r * Real.sqrt d * L / e := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hs : (4 * Real.sqrt r * Real.sqrt d * L / e) ^ 2 =
        16 * r * d * L ^ 2 / e ^ 2 := by
      simp only [div_pow, mul_pow, Real.sq_sqrt hr0, Real.sq_sqrt hd.le]
      ring
    rw [hs]
    apply (div_le_div_iff₀ hη0 (sq_pos_of_pos he)).2
    have hLs : L ≤ L ^ 2 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hbase hr0
    have h2 := mul_le_mul_of_nonneg_left hLs (by positivity : 0 ≤ 16 * r * d * η)
    nlinarith
  have hsqrt : r ≤ Real.sqrt r * Real.sqrt d := by
    calc
      r = Real.sqrt r * Real.sqrt r := (Real.mul_self_sqrt hr0).symm
      _ ≤ Real.sqrt r * Real.sqrt d :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrd) (Real.sqrt_nonneg r)
  have hfirst : r * d * (2 * r * lam) / η = 16 * r ^ 2 * d * L / e := by
    rw [hη]
    field_simp
    ring
  have hfirst_le : r ^ 2 * d * L / e ≤ r * Real.sqrt r * d * Real.sqrt d * L / e := by
    calc
      _ = r * (r * d * L / e) := by ring
      _ ≤ (Real.sqrt r * Real.sqrt d) * (r * d * L / e) :=
        mul_le_mul_of_nonneg_right hsqrt (by positivity)
      _ = _ := by ring
  have hlin : 2 * r + 1 ≤ 3 * r := by linarith
  have hcost : stageCost r d W η ≤
      16 * r ^ 2 * d * L / e + (2 * r + 1) * d * Real.sqrt (r / η) := by
    calc
      _ ≤ r * d * (2 * r * lam + Real.sqrt (2 * r * η)) / η + d * Real.sqrt (r / η) := by
        unfold stageCost
        gcongr
      _ = 16 * r ^ 2 * d * L / e +
          r * d * (Real.sqrt (2 * r * η) / η) + d * Real.sqrt (r / η) := by rw [← hfirst]; ring
      _ ≤ 16 * r ^ 2 * d * L / e +
          r * d * (2 * Real.sqrt (r / η)) + d * Real.sqrt (r / η) := by
        gcongr
        exact sqrt_mass_div_le hr0 hη0
      _ = _ := by ring
  have hsecond : (2 * r + 1) * d * Real.sqrt (r / η) ≤
      12 * (r * Real.sqrt r * d * Real.sqrt d * L / e) := by
    calc
      _ ≤ (3 * r) * d * (4 * Real.sqrt r * Real.sqrt d * L / e) := by gcongr
      _ = _ := by ring
  have hB : 0 ≤ r * Real.sqrt r * d * Real.sqrt d * L / e := by positivity
  calc
    _ ≤ 16 * r ^ 2 * d * L / e + (2 * r + 1) * d * Real.sqrt (r / η) := hcost
    _ = 16 * (r ^ 2 * d * L / e) + (2 * r + 1) * d * Real.sqrt (r / η) := by ring
    _ ≤ 16 * (r * Real.sqrt r * d * Real.sqrt d * L / e) +
        12 * (r * Real.sqrt r * d * Real.sqrt d * L / e) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst_le (by norm_num)) hsecond
    _ ≤ _ := by nlinarith

/-- The previous stage index is used only after the first stage. -/
def previousStage {L : ℕ} (j : Fin L) (_hj : j.val ≠ 0) : Fin L := ⟨j.val - 1, by omega⟩

/-- Equation 46, including its first-stage convention. -/
def massAllowance (r : ℕ) (e : ℝ) (L : ℕ) (j : Fin L) : ℝ :=
  if hj : j.val = 0 then 1 else
    min 1 ((r : ℝ) * dyadicLower L (previousStage j hj) +
      Real.sqrt ((r : ℝ) * stageAccuracy e L (previousStage j hj)))

theorem massAllowance_nonneg (r : ℕ) (e : ℝ) (L : ℕ) [NeZero L] (j : Fin L) :
    0 ≤ massAllowance r e L j := by
  unfold massAllowance
  split_ifs
  · norm_num
  · apply le_min (by norm_num)
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg r) (dyadicLower_pos L _).le)
      (Real.sqrt_nonneg _)

/-- The mass used by the next routine is proved from the preceding actual
Frobenius guarantee and from the structural eigenbasis updates. -/
theorem trueBlock_mass_le_allowance {L : ℕ} [NeZero L]
    (D : StageData (ι := ι) L (dyadicLower L)) (ρ : Density ι) {r : ℕ} {e : ℝ}
    (hr : ρ.matrix.rank ≤ r)
    (haccuracy : ∀ j, frobeniusSq (D.localError ρ j) ≤ stageAccuracy e L j) (j : Fin L) :
    (Matrix.trace (D.trueBlock ρ j)).re ≤ massAllowance r e L j := by
  unfold massAllowance
  split_ifs with hj
  · have hb : D.trueBlock ρ j = coordinates (D.basis j : Matrix ι ι ℂ) ρ.matrix := by
      ext i k
      simp [StageData.trueBlock, mask, StageData.active, hj]
    rw [hb, trace_coordinates, ρ.trace_one]
    norm_num
  · exact D.trueBlock_mass_bound ρ j (previousStage j hj) (by
      change j.val = j.val - 1 + 1
      omega) (dyadicLower_pos L _) hr (haccuracy _)

theorem dyadicLower_previous {L : ℕ} (j : Fin L) (hj : j.val ≠ 0) :
    dyadicLower L (previousStage j hj) = 2 * dyadicLower L j := by
  have hprev : (previousStage j hj).val + 1 = j.val := by dsimp [previousStage]; omega
  unfold dyadicLower
  rw [hprev, pow_succ]
  field_simp

theorem stageAccuracy_previous {L : ℕ} (e : ℝ) (j : Fin L) (hj : j.val ≠ 0) :
    stageAccuracy e L (previousStage j hj) = 2 * stageAccuracy e L j := by
  unfold stageAccuracy
  rw [dyadicLower_previous j hj]
  ring

/-- The source decreasing-mass estimate, now with its first-stage case. -/
theorem massAllowance_le {r : ℕ} (hr : 1 ≤ r) (e : ℝ) (L : ℕ) (j : Fin L) :
    massAllowance r e L j ≤ 2 * (r : ℝ) * dyadicLower L j +
      Real.sqrt (2 * (r : ℝ) * stageAccuracy e L j) := by
  unfold massAllowance
  split_ifs with hj
  · have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hl : dyadicLower L j = 1 / 2 := by norm_num [dyadicLower, hj]
    rw [hl]
    nlinarith [Real.sqrt_nonneg (2 * (r : ℝ) * stageAccuracy e L j)]
  · apply (min_le_right _ _).trans_eq
    rw [dyadicLower_previous j hj, stageAccuracy_previous e j hj]
    congr 1
    · ring
    · congr 1
      ring

namespace StageData
variable {L : ℕ} [NeZero L] {lower : Fin L → ℝ} (D : StageData (ι := ι) L lower)

/-- Dimension of the actual active coordinate block. -/
def activeDimension (j : Fin L) : ℕ := (Finset.univ.filter (D.active j.val)).card

theorem activeDimension_le (j : Fin L) : D.activeDimension j ≤ Fintype.card ι := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ)

end StageData

/-- The per-stage cost for the actual active dimension is bounded by the
full ambient dimension. -/
theorem stageCost_mono_dimension {r k d W η : ℝ}
    (hr : 0 ≤ r) (hkd : k ≤ d) (hW : 0 ≤ W) (hη : 0 < η) :
    stageCost r k W η ≤ stageCost r d W η := by
  unfold stageCost
  gcongr

/-- The complete finite-stage copy-cost arithmetic from Equation 44 before
its common logarithmic factor. No estimator-existence or probability
claim is folded into this statement. -/
theorem total_stageCost_le {L : ℕ} [NeZero L]
    (D : StageData (ι := ι) L (dyadicLower L)) {r : ℕ} {e : ℝ}
    (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι) (he : 0 < e)
    (hscale : e / (2 * (Fintype.card ι : ℝ)) ≤ dyadicLower L (lastStage L)) :
    (∑ j : Fin L, stageCost (r : ℝ) (D.activeDimension j : ℝ)
      (massAllowance r e L j) (stageAccuracy e L j)) ≤
        32 * ((r : ℝ) * Real.sqrt r * (Fintype.card ι : ℝ) *
          Real.sqrt (Fintype.card ι) * (L : ℝ) ^ 2 / e) := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.pos L
  have hp (j : Fin L) : 0 < stageAccuracy e L j := by
    unfold stageAccuracy
    exact div_pos (mul_pos he (dyadicLower_pos L j)) (by positivity)
  calc
    _ ≤ ∑ j : Fin L, stageCost (r : ℝ) (Fintype.card ι : ℝ)
        (massAllowance r e L j) (stageAccuracy e L j) := by
      apply Finset.sum_le_sum
      intro j _
      exact stageCost_mono_dimension (by positivity) (by exact_mod_cast D.activeDimension_le j)
        (massAllowance_nonneg r e L j) (hp j)
    _ ≤ ∑ _j : Fin L, 32 * ((r : ℝ) * Real.sqrt r * (Fintype.card ι : ℝ) *
        Real.sqrt (Fintype.card ι) * L / e) := by
      apply Finset.sum_le_sum
      intro j _
      exact stageCost_le (by exact_mod_cast hr) (by exact_mod_cast hrd) hL he
        (hscale.trans (dyadicLower_floor L j)) rfl (massAllowance_le hr e L j)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

omit [DecidableEq ι] in
/-- A positive integer stage count for the complete epsilon schedule. -/
theorem epsilon_stageCount_pos [Nonempty ι] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < dyadicStages (Fintype.card ι) (ε / 16) := by
  have hd : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  exact dyadicStages_pos _ (by positivity) (by linarith)

/-- Section 5.3's actual-matrix loss conclusion with its complete stage
schedule. The terminal mass scale is now proved from the schedule. -/
theorem scheduled_chiB_epsilon [Nonempty ι] {L : ℕ} [NeZero L]
    (D : StageData (ι := ι) L (dyadicLower L)) (ρ : Density ι)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hL : L = dyadicStages (Fintype.card ι) (ε / 16))
    (haccuracy : ∀ j, frobeniusSq (D.localError ρ j) ≤ stageAccuracy (ε / 16) L j) :
    chiB ρ (D.normalizedOutput (dyadicLower_pos L)) < ENNReal.ofReal ε := by
  have hd : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  apply dyadic_chiB_epsilon D ρ hε hε1 _ haccuracy
  rw [dyadicLower_last, hL]
  exact (dyadicStages_window (Fintype.card ι) (by positivity : 0 < ε / 16) (by linarith)).1

/-- The scheduled nonlogarithmic cost is an explicit finite sum with the
paper's rank and dimension exponents. -/
theorem scheduled_total_stageCost_le {L : ℕ} [NeZero L]
    (D : StageData (ι := ι) L (dyadicLower L)) {r : ℕ} {e : ℝ}
    (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι) (he : 0 < e) (hed : e < Fintype.card ι)
    (hL : L = dyadicStages (Fintype.card ι) e) :
    (∑ j : Fin L, stageCost (r : ℝ) (D.activeDimension j : ℝ)
      (massAllowance r e L j) (stageAccuracy e L j)) ≤
        32 * ((r : ℝ) * Real.sqrt r * (Fintype.card ι : ℝ) *
          Real.sqrt (Fintype.card ι) * (L : ℝ) ^ 2 / e) := by
  apply total_stageCost_le D hr hrd he
  rw [dyadicLower_last, hL]
  exact (dyadicStages_window _ he hed).2.le

/-- Epsilon form of the complete cost sum, with `e = epsilon / 16`. -/
theorem scheduled_total_stageCost_epsilon_le {L : ℕ} [NeZero L]
    (D : StageData (ι := ι) L (dyadicLower L)) {r : ℕ} {ε : ℝ}
    (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hL : L = dyadicStages (Fintype.card ι) (ε / 16)) :
    (∑ j : Fin L, stageCost (r : ℝ) (D.activeDimension j : ℝ)
      (massAllowance r (ε / 16) L j) (stageAccuracy (ε / 16) L j)) ≤
        512 * ((r : ℝ) * Real.sqrt r * (Fintype.card ι : ℝ) *
          Real.sqrt (Fintype.card ι) * (L : ℝ) ^ 2 / ε) := by
  have hd : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hr.trans hrd
  convert scheduled_total_stageCost_le D hr hrd (by positivity : 0 < ε / 16) (by linarith) hL using 1
  ring

theorem stageCost_nonneg {r d W η : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d)
    (hW : 0 ≤ W) (hη : 0 < η) : 0 ≤ stageCost r d W η := by
  unfold stageCost
  positivity

/-- Integer copy allocation after multiplying the source cost expression by
an explicit routine constant and common logarithmic factor. -/
def roundedStageCopies {L : ℕ} [NeZero L]
    (D : StageData (ι := ι) L (dyadicLower L)) (r : ℕ) (e C ell : ℝ) (j : Fin L) : ℕ :=
  Nat.ceil (C * ell * stageCost (r : ℝ) (D.activeDimension j : ℝ)
    (massAllowance r e L j) (stageAccuracy e L j))

/-- Rounding contributes at most one copy per stage. This is a proved
arithmetic budget, independent of the later probabilistic implementation. -/
theorem total_roundedStageCopies_le {L : ℕ} [NeZero L]
    (D : StageData (ι := ι) L (dyadicLower L)) {r : ℕ} {e C ell : ℝ}
    (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι) (he : 0 < e)
    (hscale : e / (2 * (Fintype.card ι : ℝ)) ≤ dyadicLower L (lastStage L))
    (hC : 0 ≤ C) (hell : 0 ≤ ell) :
    ((∑ j : Fin L, roundedStageCopies D r e C ell j : ℕ) : ℝ) ≤
      32 * C * ell * ((r : ℝ) * Real.sqrt r * (Fintype.card ι : ℝ) *
        Real.sqrt (Fintype.card ι) * (L : ℝ) ^ 2 / e) + L := by
  rw [Nat.cast_sum]
  have hLpos : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  have hp (j : Fin L) : 0 < stageAccuracy e L j := by
    unfold stageAccuracy
    exact div_pos (mul_pos he (dyadicLower_pos L j)) (by positivity)
  have hcost (j : Fin L) : 0 ≤ stageCost (r : ℝ) (D.activeDimension j : ℝ)
      (massAllowance r e L j) (stageAccuracy e L j) :=
    stageCost_nonneg (by positivity) (by positivity) (massAllowance_nonneg r e L j) (hp j)
  calc
    _ ≤ ∑ j : Fin L, (C * ell * stageCost (r : ℝ) (D.activeDimension j : ℝ)
        (massAllowance r e L j) (stageAccuracy e L j) + 1) := by
      apply Finset.sum_le_sum
      intro j _
      exact (Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg hC hell) (hcost j))).le
    _ = C * ell * (∑ j : Fin L, stageCost (r : ℝ) (D.activeDimension j : ℝ)
        (massAllowance r e L j) (stageAccuracy e L j)) + L := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ C * ell * (32 * ((r : ℝ) * Real.sqrt r * (Fintype.card ι : ℝ) *
        Real.sqrt (Fintype.card ι) * (L : ℝ) ^ 2 / e)) + L := by
      gcongr
      exact total_stageCost_le D hr hrd he hscale
    _ = _ := by ring

/-- The common logarithm for per-stage failure allocation `delta / L`. -/
def commonLog (d L δ : ℝ) : ℝ := Real.log (2 * d * L / δ)

theorem commonLog_nonneg {d L δ : ℝ} (hd : 1 ≤ d) (hL : 1 ≤ L)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 ≤ commonLog d L δ := by
  apply (Real.log_pos _).le
  have hp : (1 : ℝ) ≤ d * L := by nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hL)]
  apply (lt_div_iff₀ hδ).2
  nlinarith

/-- Replacing the actual positive active dimension by `d` also dominates
the per-stage logarithm; zero-dimensional stages use no copies. -/
theorem stageLog_le_common {k d L δ : ℝ} (hk : 0 < k) (hkd : k ≤ d)
    (hL : 0 < L) (hδ : 0 < δ) :
    Real.log (2 * k / (δ / L)) ≤ commonLog d L δ := by
  apply Real.log_le_log (by positivity)
  have he : 2 * k / (δ / L) = 2 * k * L / δ := by field_simp
  rw [he]
  apply div_le_div_of_nonneg_right _ hδ.le
  nlinarith

/-- Copy rounding with the actual common logarithmic factor. -/
theorem total_roundedStageCopies_commonLog_le {L : ℕ} [NeZero L]
    (D : StageData (ι := ι) L (dyadicLower L)) {r : ℕ} {e C δ : ℝ}
    (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι) (he : 0 < e) (hed : e < Fintype.card ι)
    (hL : L = dyadicStages (Fintype.card ι) e) (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((∑ j : Fin L, roundedStageCopies D r e C
      (commonLog (Fintype.card ι) L δ) j : ℕ) : ℝ) ≤
      32 * C * commonLog (Fintype.card ι) L δ *
        ((r : ℝ) * Real.sqrt r * (Fintype.card ι : ℝ) *
          Real.sqrt (Fintype.card ι) * (L : ℝ) ^ 2 / e) + L := by
  refine total_roundedStageCopies_le D hr hrd he ?_ hC ?_
  · rw [dyadicLower_last, hL]
    exact (dyadicStages_window _ he hed).2.le
  · exact commonLog_nonneg (by exact_mod_cast hr.trans hrd)
      (by exact_mod_cast NeZero.pos L) hδ hδ1

end Paper26.MultiscaleRefinement




