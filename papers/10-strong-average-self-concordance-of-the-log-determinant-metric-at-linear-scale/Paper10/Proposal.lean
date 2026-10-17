import Paper10.SASCProof
import Paper10.Rotation
import Paper10.StandardBasis

noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder
namespace Paper10
variable {q m : ℕ}

/-- Normalized covariance obtained from arbitrary auxiliary precision in congruence coordinates. -/
def auxiliaryCovariance (s : ℝ) (E : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  s • (s • (1 : Matrix (Fin m) (Fin m) ℝ) + E)⁻¹

theorem auxiliaryCovariance_bounds {s : ℝ} (hs : 0 < s)
    (E : Matrix (Fin m) (Fin m) ℝ) (hE : E.PosSemidef) :
    (auxiliaryCovariance s E).PosSemidef ∧ (1 - auxiliaryCovariance s E).PosSemidef := by
  have hh := lemma_2_1_contraction (1 : Matrix (Fin m) (Fin m) ℝ) E isUnit_one hE hs
  simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, auxiliaryCovariance] using hh

/-- Eigenvalues of the normalized proposal covariance. -/
def auxiliaryEigenvalues (s : ℝ) (E : Matrix (Fin m) (Fin m) ℝ)
    (hs : 0 < s) (hE : E.PosSemidef) : Fin m → ℝ :=
  (auxiliaryCovariance_bounds hs E hE).1.isHermitian.eigenvalues

/-- Eigenvector rotation of the normalized proposal covariance. -/
def auxiliaryRotation (s : ℝ) (E : Matrix (Fin m) (Fin m) ℝ)
    (hs : 0 < s) (hE : E.PosSemidef) : Matrix.unitaryGroup (Fin m) ℝ :=
  (auxiliaryCovariance_bounds hs E hE).1.isHermitian.eigenvectorUnitary

/-- All proposal covariance eigenvalues lie in [0,1], including singular cases. -/
theorem auxiliaryEigenvalues_bounds {s : ℝ} (hs : 0 < s)
    (E : Matrix (Fin m) (Fin m) ℝ) (hE : E.PosSemidef) (i : Fin m) :
    0 ≤ auxiliaryEigenvalues s E hs hE i ∧ auxiliaryEigenvalues s E hs hE i ≤ 1 := by
  let Q := auxiliaryCovariance s E
  have hQ := auxiliaryCovariance_bounds hs E hE
  let O := auxiliaryRotation s E hs hE
  let ev := auxiliaryEigenvalues s E hs hE
  have hO : (O : Matrix (Fin m) (Fin m) ℝ)ᴴ * (O : Matrix (Fin m) (Fin m) ℝ) = 1 := O.2.1
  have hd : (O : Matrix _ _ ℝ)ᴴ * Q * (O : Matrix _ _ ℝ) = Matrix.diagonal ev := by
    simpa only [Matrix.star_eq_conjTranspose, RCLike.ofReal_real_eq_id, Function.id_comp]
      using hQ.1.isHermitian.star_mul_self_mul_eq_diagonal
  have hc := hQ.2.conjTranspose_mul_mul_same (O : Matrix (Fin m) (Fin m) ℝ)
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one] at hc
  rw [hO, hd] at hc
  have hdiag : (Matrix.diagonal (fun j => 1 - ev j)).PosSemidef := by
    have he : (1 : Matrix (Fin m) (Fin m) ℝ) - Matrix.diagonal ev = Matrix.diagonal (fun j => 1 - ev j) := by
      ext a b
      by_cases hab : a = b <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hab]
    rwa [he] at hc
  have hh := (Matrix.posSemidef_diagonal_iff.mp hdiag) i
  exact ⟨hQ.1.eigenvalues_nonneg i, by change ev i ≤ 1; linarith⟩

/-- Exact covariance-eigenmode construction of the proposal (3), in the basis R F_a R*. -/
def proposalStep (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (R : Matrix (Fin q) (Fin q) ℝ) (s r : ℝ)
    (E : Matrix (Fin m) (Fin m) ℝ) (hs : 0 < s) (hE : E.PosSemidef)
    (ω : Fin m → ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  R * (tOf (q := q) r s • gaussianMatrix
    (fun a => Real.sqrt (auxiliaryEigenvalues s E hs hE a) •
      rotateF F (auxiliaryRotation s E hs hE) a) ω) * Rᴴ

/-- Two-sided SASC bound for every base-point factor and every auxiliary PSD precision.
The auxiliary form is expressed in the complete congruence basis R F_a R*; its coordinate
matrix E is completely arbitrary, may be singular and may correlate all entries. -/
theorem thm_1_3_two_sided_factor (hq : 0 < q)
    (F : Fin m → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F)
    (R : Matrix (Fin q) (Fin q) ℝ) (hR : IsUnit R)
    {s ε r : ℝ} (hs : c q ≤ s) (hε : 0 < ε) (hε1 : ε < 1) (hr : 0 < r) (hr1 : r ≤ rEps ε)
    (E : Matrix (Fin m) (Fin m) ℝ) (hE : E.PosSemidef) :
    let X := R * Rᴴ
    let H := proposalStep F R s r E (lt_of_lt_of_le (c_pos q) hs) hE
    1 - ε ≤ (stdGaussianMeasure m).real {ω | sascEventTwoSided s X (X + H ω) (H ω) ε r} := by
  have hs0 := lt_of_lt_of_le (c_pos q) hs
  exact sasc_of_covariance_eigenmodes hq
    (rotateF F (auxiliaryRotation s E hs0 hE))
    (rotateF_orthonormal F hF (auxiliaryRotation s E hs0 hE))
    (fun a => Real.sqrt (auxiliaryEigenvalues s E hs0 hE a))
    (fun a => ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr (auxiliaryEigenvalues_bounds hs0 E hE a).2⟩)
    R hR hs hε hε1 hr hr1

/-- Theorem 1.3 two-sided bound at every actual positive definite base point. -/
theorem thm_1_3_two_sided (hq : 0 < q)
    (F : Fin m → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F)
    (X : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef)
    {s ε r : ℝ} (hs : c q ≤ s) (hε : 0 < ε) (hε1 : ε < 1) (hr : 0 < r) (hr1 : r ≤ rEps ε)
    (E : Matrix (Fin m) (Fin m) ℝ) (hE : E.PosSemidef) :
    let H := proposalStep F (CFC.sqrt X) s r E (lt_of_lt_of_le (c_pos q) hs) hE
    1 - ε ≤ (stdGaussianMeasure m).real {ω | sascEventTwoSided s X (X + H ω) (H ω) ε r} := by
  have hh := thm_1_3_two_sided_factor hq F hF (CFC.sqrt X) hX.posDef_sqrt.isUnit hs hε hε1 hr hr1 E hE
  have hx : CFC.sqrt X * (CFC.sqrt X)ᴴ = X := by
    rw [hX.posDef_sqrt.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg
  simpa only [hx] using hh

/-- Theorem 1.3 one-sided SASC bound (4), for the same actual proposal and feasible endpoint. -/
theorem thm_1_3_sasc (hq : 0 < q)
    (F : Fin m → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F)
    (X : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef)
    {s ε r : ℝ} (hs : c q ≤ s) (hε : 0 < ε) (hε1 : ε < 1) (hr : 0 < r) (hr1 : r ≤ rEps ε)
    (E : Matrix (Fin m) (Fin m) ℝ) (hE : E.PosSemidef) :
    let H := proposalStep F (CFC.sqrt X) s r E (lt_of_lt_of_le (c_pos q) hs) hE
    1 - ε ≤ (stdGaussianMeasure m).real {ω | sascEvent s X (X + H ω) (H ω) ε r} := by
  apply (thm_1_3_two_sided hq F hF X hX hs hε hε1 hr hr1 E hE).trans
  apply measureReal_mono _ (by finiteness)
  intro ω hh
  exact ⟨hh.1, (le_abs_self _).trans hh.2⟩

end Paper10
