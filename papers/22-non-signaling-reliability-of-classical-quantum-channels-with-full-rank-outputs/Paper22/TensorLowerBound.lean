import Paper22.Tensor
import Paper22.ReliabilityPositivity

/-! Quantitative lower bounds for genuine Kronecker tensor powers (S3, Example 6). -/

open scoped MatrixOrder ComplexOrder Kronecker
open Matrix
noncomputable section
namespace Paper22

private theorem tensor_sub_left {a b : Type*} (A C : Matrix a a ℂ)
    (B : Matrix b b ℂ) : (A - C) ⊗ₖ B = A ⊗ₖ B - C ⊗ₖ B := by
  ext i j
  exact sub_mul _ _ _

private theorem tensor_sub_right {a b : Type*} (A : Matrix a a ℂ)
    (B C : Matrix b b ℂ) : A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext i j
  exact mul_sub _ _ _

/-- Scalar lower bounds multiply under the actual Kronecker product. -/
theorem kronecker_scalar_lower_bound {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b]
    {A : Matrix a a ℂ} {B : Matrix b b ℂ}
    (hB0 : 0 ≤ B) {u v : ℝ} (hu : 0 ≤ u)
    (hA : u • (1 : Matrix a a ℂ) ≤ A)
    (hB : v • (1 : Matrix b b ℂ) ≤ B) :
    (u * v) • (1 : Matrix (a × b) (a × b) ℂ) ≤ A ⊗ₖ B := by
  have hI : 0 ≤ u • (1 : Matrix a a ℂ) :=
    smul_nonneg hu (PosSemidef.one.nonneg)
  have hp := (posSemidef_kronecker (le_iff.mp hA) hB0.posSemidef).add
    (posSemidef_kronecker hI.posSemidef (le_iff.mp hB))
  apply le_iff.mpr
  convert hp using 1
  rw [tensor_sub_left, tensor_sub_right]
  simp only [Matrix.smul_kronecker, Matrix.kronecker_smul,
    Matrix.one_kronecker_one, smul_smul, mul_comm v u]
  abel

/-- Equivalence reindexing preserves a scalar matrix lower bound. -/
theorem submatrix_equiv_scalar_lower_bound {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] {A : Matrix a a ℂ}
    {u : ℝ} (hA : u • (1 : Matrix a a ℂ) ≤ A) (e : b ≃ a) :
    u • (1 : Matrix b b ℂ) ≤ A.submatrix e e := by
  apply le_iff.mpr
  simpa only [Matrix.submatrix_sub, Matrix.submatrix_smul,
    Pi.sub_apply, Pi.smul_apply, Matrix.submatrix_one_equiv] using (le_iff.mp hA).submatrix e

/-- A uniform output-state lower bound multiplies under channel tensor product. -/
theorem CQChannel.tensor_scalar_lower_bound {n d m e : ℕ}
    (V : CQChannel n d) (W : CQChannel m e)
    {u v : ℝ} (hu : 0 ≤ u)
    (hV : ∀ x, u • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ V.states x)
    (hW : ∀ x, v • (1 : Matrix (Fin e) (Fin e) ℂ) ≤ W.states x) :
    ∀ x, (u * v) • (1 : Matrix (Fin (d * e)) (Fin (d * e)) ℂ) ≤
      (V.tensor W).states x := by
  intro x
  exact submatrix_equiv_scalar_lower_bound
    (kronecker_scalar_lower_bound (W.nonneg _) hu (hV _) (hW _)) finProdFinEquiv.symm

/-- The lower eigenvalue of a genuine tensor-power output is at least `lam ^ k`. -/
theorem tensorPowerFamily_scalar_lower_bound {n d : ℕ} (W : CQChannel n d)
    {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam : ∀ x, lam • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ W.states x)
    (k : ℕ) :
    ∀ x, lam ^ k • (1 : Matrix (Fin (d ^ k)) (Fin (d ^ k)) ℂ) ≤
      (tensorPowerFamily W k).states x := by
  induction k with
  | zero =>
      intro x
      simp only [pow_zero, one_smul, tensorPowerFamily, tensorUnitChannel]
      exact le_refl _
  | succ k ih =>
      intro x
      change lam ^ (k + 1) • (1 : Matrix (Fin (d ^ (k + 1))) (Fin (d ^ (k + 1))) ℂ) ≤
        (((tensorPowerFamily W k).tensor W).states
          ((finCongr (Nat.pow_succ n k)) x)).submatrix
            (finCongr (Nat.pow_succ d k)) (finCongr (Nat.pow_succ d k))
      rw [pow_succ lam k]
      exact submatrix_equiv_scalar_lower_bound
        (CQChannel.tensor_scalar_lower_bound _ W (pow_nonneg hlam0 k) ih hlam _) _

/-- Convert the PSD scalar lower bound to the existing Hermitian eigenvalue API. -/
theorem eigenvalues_lower_bound_of_scalar {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) {lam : ℝ}
    (hlam : lam • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ A) :
    ∀ i, lam ≤ hA.eigenvalues i := by
  have hmap : algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) lam ≤ A := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hlam
  exact fun i => (algebraMap_le_iff_le_spectrum hA.isSelfAdjoint).mp hmap _
    (hA.eigenvalues_mem_spectrum_real i)

/-- A positive scalar lower state bound implies full rank, without an added hypothesis. -/
theorem CQChannel.fullRank_of_scalar_lower_bound {n d : ℕ} (W : CQChannel n d)
    {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : ∀ x, lam • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ W.states x) :
    W.FullRank := by
  intro x
  apply (W.density x).isHermitian.posDef_iff_eigenvalues_pos.mpr
  intro i
  exact hlam0.trans_le (eigenvalues_lower_bound_of_scalar (W.density x).isHermitian (hlam x) i)

/-- A scalar lower state bound directly bounds the MC error. -/
theorem epsMC_lower_bound_of_order {n d : ℕ} [NeZero n] (W : CQChannel n d)
    {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam : ∀ x, lam • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ W.states x)
    {L : ℝ} (hL : 0 < L) :
    lam * (d : ℝ) * (1 - 1 / L) ≤ epsMC W L := by
  exact epsMC_lower_bound_of_spectral W
    (fun x => eigenvalues_lower_bound_of_scalar (W.density x).isHermitian (hlam x)) hlam0 hL

/-- S3, Example 6: the finite-block MC error has the quantitative exponential lower bound. -/
theorem tensorPowerFamily_epsMC_lower_bound {n d : ℕ} [NeZero n]
    (W : CQChannel n d) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : ∀ x, lam • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ W.states x)
    (k : ℕ) {L : ℝ} (hL : 1 < L) :
    ((d : ℝ) * lam) ^ k * (1 - 1 / L) ≤ epsMC (tensorPowerFamily W k) L := by
  haveI : NeZero (n ^ k) := ⟨pow_ne_zero k (NeZero.ne n)⟩
  have hb := epsMC_lower_bound_of_order (tensorPowerFamily W k)
    (pow_nonneg hlam0.le k) (tensorPowerFamily_scalar_lower_bound W hlam0.le hlam k)
    (show 0 < L by linarith)
  simpa only [Nat.cast_pow, mul_pow, mul_comm (lam ^ k) ((d : ℝ) ^ k)] using hb

end Paper22
end
