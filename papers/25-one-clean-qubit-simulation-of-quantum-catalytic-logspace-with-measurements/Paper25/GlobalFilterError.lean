import Paper25.FullspaceFilter
import Paper25.CoherentFilterCircuit

/-!
# Global error of the actual coherent filter

Only the published unitary spectral theorem is supplied externally, as
`UnitaryEigenbasis V`.  The circuit below is defined from controlled powers of
V, Fourier transforms, label rotations and their inverses, independently of
that eigenbasis.  The uniform scalar estimate of Appendix B is transferred to
the actual L2 operator norm, then to the compressed history subspace.
-/

noncomputable section
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
namespace Paper25

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma diagonal_l2_opNorm_le (d : n → ℂ) (b : ℝ) (hb : 0 ≤ b)
    (hd : ∀ i, ‖d i‖ ≤ b) : ‖Matrix.diagonal d‖ ≤ b := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro x
  have hsum : (∑ i, ‖d i * x i‖ ^ 2) ≤ b ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) hb).mpr (hd i)) (sq_nonneg _)
  have hout : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.diagonal d) x‖ ^ 2 =
      ∑ i, ‖d i * x i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    congr 1
    funext i
    change ‖Matrix.mulVec (Matrix.diagonal d) (WithLp.ofLp x) i‖ ^ 2 = _
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal]
  have hx : (∑ i, ‖x i‖ ^ 2) = ‖x‖ ^ 2 := (EuclideanSpace.norm_sq_eq x).symm
  rw [hx] at hsum
  rw [← hout] at hsum
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hb (norm_nonneg x))).mp
  simpa only [mul_pow] using hsum

lemma unitary_conjugate_opNorm_le (W A : Matrix n n ℂ)
    (hW : W ∈ Matrix.unitaryGroup n ℂ) : ‖W * A * star W‖ ≤ ‖A‖ := by
  have hE : (star W).conjTranspose * star W = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using hW.2
  simpa only [isometryCompression, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose] using isometryCompression_opNorm_le (star W) hE A

lemma filterRat_diagonal (t : n → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    filterRat (Matrix.diagonal (fun i => (t i : ℂ))) δ =
      Matrix.diagonal (fun i => ((filterFn δ (t i) : ℝ) : ℂ)) := by
  let d : n → ℂ := fun i => (t i : ℂ) ^ 2 + (δ : ℂ) ^ 2
  have hd (i : n) : d i ≠ 0 := by
    dsimp [d]
    have hr : (t i) ^ 2 + δ ^ 2 ≠ 0 := by positivity
    exact_mod_cast hr
  have hden : Matrix.diagonal (fun i => (t i : ℂ)) * Matrix.diagonal (fun i => (t i : ℂ)) +
      ((δ ^ 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ) = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [d, Matrix.diagonal_mul_diagonal, pow_two]
    · simp [d, Matrix.diagonal_mul_diagonal, hij]
  have hi : (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    simpa only [mul_inv_cancel₀ (hd _)] using (Matrix.diagonal_one (n := n) (α := ℂ))
  unfold filterRat
  rw [hden, hi]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.smul_mul, Matrix.diagonal_mul_diagonal, filterFn, d, div_eq_mul_inv]
  · simp [Matrix.smul_mul, Matrix.diagonal_mul_diagonal, hij]

lemma filterRat_unitary_conjugate (W A : Matrix n n ℂ)
    (hW : W ∈ Matrix.unitaryGroup n ℂ) (hA : A.IsHermitian) (δ : ℝ) (hδ : 0 < δ) :
    filterRat (W * A * star W) δ = W * filterRat A δ * star W := by
  have hE : (star W).conjTranspose * star W = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using hW.2
  have hH : (W * A * star W).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose W hA
  have hinter : A * star W = star W * (W * A * star W) := by
    calc
      _ = (star W * W) * A * star W := by rw [hW.1, one_mul]
      _ = _ := by simp only [mul_assoc]
  have h := filterRat_isometry_compression A (W * A * star W) (star W) hE hA hH hinter δ hδ
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using h.symm

lemma exp_phase_realPart (φ : ℝ) :
    (1 / 2 : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * (φ : ℂ)) +
      conj (Complex.exp (2 * Real.pi * Complex.I * (φ : ℂ)))) = (Real.cos (2 * Real.pi * φ) : ℂ) := by
  let z := Complex.exp (2 * Real.pi * Complex.I * (φ : ℂ))
  have hz : z.re = Real.cos (2 * Real.pi * φ) := by
    dsimp [z]
    have heq : 2 * Real.pi * Complex.I * (φ : ℂ) = ((2 * Real.pi * φ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [heq, Complex.exp_re]
    simp
  change (1 / 2 : ℂ) * (z + conj z) = _
  rw [Complex.add_conj, hz]
  push_cast
  ring

lemma walkRealPart_spectral (V : Matrix n n ℂ) (D : UnitaryEigenbasis V) :
    walkRealPart V = D.basis * Matrix.diagonal
      (fun i => (Real.cos (2 * Real.pi * D.phase i) : ℂ)) * star D.basis := by
  unfold walkRealPart
  conv_lhs => rw [D.phase_decomposition]
  simp only [star_mul, star_star]
  calc
    _ = D.basis * ((1 / 2 : ℂ) •
        (Matrix.diagonal (fun i => Complex.exp (2 * Real.pi * Complex.I * (D.phase i : ℂ))) +
          star (Matrix.diagonal (fun i => Complex.exp (2 * Real.pi * Complex.I * (D.phase i : ℂ)))))) * star D.basis := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_assoc]
    _ = _ := by
      congr 2
      ext i j
      by_cases hij : i = j
      · subst j
        simpa [Matrix.smul_apply, Matrix.star_apply] using exp_phase_realPart (D.phase i)
      · simp [Matrix.smul_apply, Matrix.star_apply, Matrix.diagonal_apply, hij, Ne.symm hij]

lemma walkFilter_spectral (V : Matrix n n ℂ) (D : UnitaryEigenbasis V) (δ : ℝ) (hδ : 0 < δ) :
    filterRat (walkRealPart V) δ = D.basis * Matrix.diagonal
      (fun i => ((filterG δ (2 * Real.pi * D.phase i) : ℝ) : ℂ)) * star D.basis := by
  let t : n → ℝ := fun i => Real.cos (2 * Real.pi * D.phase i)
  have hA : (Matrix.diagonal (fun i => (t i : ℂ))).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change conj (t i : ℂ) = (t i : ℂ)
    simp
  rw [walkRealPart_spectral V D,
    filterRat_unitary_conjugate _ _ D.basis_unitary hA δ hδ,
    filterRat_diagonal _ δ hδ]
  rfl

/-- Appendix B's uniform scalar estimate is a genuine full-space operator-norm
estimate for the controlled-power phase-estimation filter. -/
theorem phaseFilteredBlock_error (V : Matrix n n ℂ) (D : UnitaryEigenbasis V)
    (M : ℕ) (hM : 0 < M) (δ ε : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hε : 0 < ε) (hεle : ε ≤ 1) (hMdef : 4096 / (δ * ε ^ 2) ≤ (M : ℝ)) :
    ‖phaseFilteredBlock V M hM (fun j => filterG δ (2 * Real.pi * ((j : ℝ) / M))) -
      filterRat (walkRealPart V) δ‖ ≤ ε / 8 := by
  rw [phaseFilteredBlock_spectral V D, walkFilter_spectral V D δ hδ]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  apply (unitary_conjugate_opNorm_le _ _ D.basis_unitary).trans
  apply diagonal_l2_opNorm_le _ _ (by positivity)
  intro i
  have h := phaseEst_filter_average_error M δ ε (D.phase i) hδ hδle hε hεle hMdef
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h

/-- The full circuit is defined without using its external spectral input. -/
def coherentWalkFilter (V : Matrix n n ℂ) (M : ℕ) (δ : ℝ) :
    Matrix (Sum (Fin M × n) (Fin M × n)) (Sum (Fin M × n) (Fin M × n)) ℂ :=
  phaseFilterCircuit (phaseEstimationMatrix V M)
    (fun j => filterG δ (2 * Real.pi * ((j : ℝ) / M)))

theorem coherentWalkFilter_unitary (V : Matrix n n ℂ)
    (hV : V ∈ Matrix.unitaryGroup n ℂ) (M : ℕ) (hM : 0 < M) (δ : ℝ) (hδ : 0 < δ) :
    coherentWalkFilter V M δ ∈ Matrix.unitaryGroup (Sum (Fin M × n) (Fin M × n)) ℂ := by
  apply phaseFilterCircuit_unitary
  · exact phaseEstimationMatrix_unitary V hV M hM
  · intro j
    exact (filterG_range_bound δ _ hδ).trans (by norm_num)

lemma coherentWalkFilter_selected (V : Matrix n n ℂ) (M : ℕ) (hM : 0 < M) (δ : ℝ) :
    (coherentWalkFilter V M δ).submatrix
      (fun i => Sum.inl ((⟨0, hM⟩ : Fin M), i))
      (fun i => Sum.inl ((⟨0, hM⟩ : Fin M), i)) =
    phaseFilteredBlock V M hM (fun j => filterG δ (2 * Real.pi * ((j : ℝ) / M))) := by
  exact phaseFilterCircuit_selected _ _ _

/-- The actual zero phase/rotation block approximates fδ(Re V). -/
theorem coherentWalkFilter_error (V : Matrix n n ℂ) (D : UnitaryEigenbasis V)
    (M : ℕ) (hM : 0 < M) (δ ε : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hε : 0 < ε) (hεle : ε ≤ 1) (hMdef : 4096 / (δ * ε ^ 2) ≤ (M : ℝ)) :
    ‖(coherentWalkFilter V M δ).submatrix
        (fun i => Sum.inl ((⟨0, hM⟩ : Fin M), i))
        (fun i => Sum.inl ((⟨0, hM⟩ : Fin M), i)) - filterRat (walkRealPart V) δ‖ ≤ ε / 8 := by
  rw [coherentWalkFilter_selected]
  exact phaseFilteredBlock_error V D M hM δ ε hδ hδle hε hεle hMdef

section HistoryCompression

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Lemma 5's approximation after compressing the original history block ancillas.
The circuit includes the phase and rotation qubits, while E specifies only the
original block ancillas.  All errors are derived from the actual circuit. -/
theorem coherentWalkFilter_compression_error (U : Matrix N N ℂ) (E : Matrix N n ℂ)
    (hU : U.IsHermitian) (hE : E.conjTranspose * E = 1)
    (D : UnitaryEigenbasis (compressionWalk (isometryProjector E) U))
    (M : ℕ) (hM : 0 < M) (δ ε : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hε : 0 < ε) (hεle : ε ≤ 1) (hMdef : 4096 / (δ * ε ^ 2) ≤ (M : ℝ)) :
    ‖E.conjTranspose *
        (coherentWalkFilter (compressionWalk (isometryProjector E) U) M δ).submatrix
          (fun i => Sum.inl ((⟨0, hM⟩ : Fin M), i))
          (fun i => Sum.inl ((⟨0, hM⟩ : Fin M), i)) * E -
      filterRat (isometryCompression E U) δ‖ ≤ ε / 8 := by
  have herr := coherentWalkFilter_error (compressionWalk (isometryProjector E) U)
    D M hM δ ε hδ hδle hε hεle hMdef
  rw [← compressionWalk_filter U E hU hE δ hδ]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  exact (isometryCompression_opNorm_le E hE _).trans herr

/-- Legality of the same circuit used in the compressed error theorem. -/
theorem coherentWalkFilter_compression_unitary (U : Matrix N N ℂ) (E : Matrix N n ℂ)
    (hU : U.IsHermitian) (hUU : U ∈ Matrix.unitaryGroup N ℂ)
    (hE : E.conjTranspose * E = 1) (M : ℕ) (hM : 0 < M) (δ : ℝ) (hδ : 0 < δ) :
    coherentWalkFilter (compressionWalk (isometryProjector E) U) M δ ∈
      Matrix.unitaryGroup (Sum (Fin M × N) (Fin M × N)) ℂ := by
  apply coherentWalkFilter_unitary _ _ M hM δ hδ
  exact compressionWalk_unitary _ _ (isometryProjector_hermitian E) (isometryProjector_sq E hE) hUU

end HistoryCompression

end Paper25
