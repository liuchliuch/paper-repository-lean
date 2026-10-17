import PsgEst.Basic

open Matrix BigOperators Real
open scoped InnerProductSpace

namespace PsgEst

section OrderedSpectrum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ}

/-- Parseval's identity in a real orthonormal basis. -/
theorem spectral_norm_sq (b : OrthonormalBasis (Fin n) ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, (b.repr x i) ^ 2 := by
  have h := b.repr.norm_map x
  rw [← h, EuclideanSpace.norm_sq_eq]
  simp

variable [FiniteDimensional ℝ E]

/-- The quadratic form in a sorted orthonormal eigenbasis. -/
theorem spectral_quadratic (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (x : E) :
    inner ℝ x (A x) = ∑ i,
      hA.eigenvalues hn i * ((hA.eigenvectorBasis hn).repr x i) ^ 2 := by
  rw [← (hA.eigenvectorBasis hn).repr.inner_map_map x (A x), PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hA.eigenvectorBasis_apply_self_apply hn]
  simp only [RCLike.inner_apply, conj_trivial, RCLike.ofReal_real_eq_id, id_eq]
  ring

/-- Extend coefficients on the first `k` eigenvectors by zero. -/
def spectralPad (k n : ℕ) : (Fin k → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun a := WithLp.toLp 2 (fun i => if h : i.val < k then a ⟨i.val, h⟩ else 0)
  map_add' a b := by
    ext i
    by_cases hi : i.val < k <;> simp [hi]
  map_smul' c a := by
    ext i
    by_cases hi : i.val < k <;> simp [hi]

@[simp] theorem spectralPad_apply (k n : ℕ) (a : Fin k → ℝ) (i : Fin n) :
    spectralPad k n a i = if h : i.val < k then a ⟨i.val, h⟩ else 0 := rfl

/-- Ordered spectral comparison from pointwise Rayleigh comparison, allowing an
arbitrary invertible linear change of variables. The proof uses the spectral
theorem and rank-nullity, and does not assume an eigenvalue inequality. -/
theorem ordered_spectral_affine_comparison (A B : E →ₗ[ℝ] E)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (e : E ≃ₗ[ℝ] E)
    (α β γ δ : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hcmp : ∀ x, (α * inner ℝ x (A x) + β * ‖x‖ ^ 2) * ‖e x‖ ^ 2 ≤
      (γ * inner ℝ (e x) (B (e x)) + δ * ‖e x‖ ^ 2) * ‖x‖ ^ 2) (j : Fin n) :
    α * hA.eigenvalues hn j + β ≤ γ * hB.eigenvalues hn j + δ := by
  classical
  let bA := hA.eigenvectorBasis hn
  let bB := hB.eigenvectorBasis hn
  let inc : (Fin (j.val + 1) → ℝ) →ₗ[ℝ] E :=
    bA.repr.symm.toLinearEquiv.toLinearMap.comp (spectralPad (j.val + 1) n)
  let proj : E →ₗ[ℝ] (Fin j.val → ℝ) :=
    { toFun := fun x i => bB.repr (e x) ⟨i.val, by omega⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  let g := proj.comp inc
  have hk : LinearMap.ker g ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp
  obtain ⟨a, ha, ha0⟩ := (LinearMap.ker g).ne_bot_iff.mp hk
  let x := inc a
  have hx : x ≠ 0 := by
    intro hx0
    apply ha0
    ext i
    have hi : i.val < n := by omega
    have hi' : i.val < j.val + 1 := i.isLt
    have heq := congrArg (fun v => bA.repr v ⟨i.val, hi⟩) hx0
    simpa [x, inc, spectralPad_apply, hi'] using heq
  have hex : e x ≠ 0 := e.map_ne_zero_iff.mpr hx
  have hAcoord : ∀ i : Fin n, j.val < i.val → bA.repr x i = 0 := by
    intro i hi
    have hni : ¬i.val < j.val + 1 := by omega
    simp [x, inc, spectralPad_apply, hni]
  have hBcoord : ∀ i : Fin n, i.val < j.val → bB.repr (e x) i = 0 := by
    intro i hi
    have heq := congrFun (LinearMap.mem_ker.mp ha) ⟨i.val, hi⟩
    simpa [g, proj, x] using heq
  have hAq : hA.eigenvalues hn j * ‖x‖ ^ 2 ≤ inner ℝ x (A x) := by
    rw [spectral_norm_sq bA, spectral_quadratic A hA hn, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change hA.eigenvalues hn j * (bA.repr x i) ^ 2 ≤
      hA.eigenvalues hn i * (bA.repr x i) ^ 2
    by_cases hij : i ≤ j
    · exact mul_le_mul_of_nonneg_right (hA.eigenvalues_antitone hn hij) (sq_nonneg _)
    · have hi : j.val < i.val := by omega
      simp only [hAcoord i hi, zero_pow (by omega : 2 ≠ 0), mul_zero]
      exact le_rfl
  have hBq : inner ℝ (e x) (B (e x)) ≤ hB.eigenvalues hn j * ‖e x‖ ^ 2 := by
    rw [spectral_norm_sq bB, spectral_quadratic B hB hn, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change hB.eigenvalues hn i * (bB.repr (e x) i) ^ 2 ≤
      hB.eigenvalues hn j * (bB.repr (e x) i) ^ 2
    by_cases hij : j ≤ i
    · exact mul_le_mul_of_nonneg_right (hB.eigenvalues_antitone hn hij) (sq_nonneg _)
    · have hi : i.val < j.val := by omega
      simp only [hBcoord i hi, zero_pow (by omega : 2 ≠ 0), mul_zero]
      exact le_rfl
  have hAq' : (α * hA.eigenvalues hn j + β) * ‖x‖ ^ 2 ≤
      α * inner ℝ x (A x) + β * ‖x‖ ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hAq hα]
  have hBq' : γ * inner ℝ (e x) (B (e x)) + δ * ‖e x‖ ^ 2 ≤
      (γ * hB.eigenvalues hn j + δ) * ‖e x‖ ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hBq hγ]
  have h1 := mul_le_mul_of_nonneg_right hAq' (sq_nonneg ‖e x‖)
  have h2 := mul_le_mul_of_nonneg_right hBq' (sq_nonneg ‖x‖)
  have h3 := (h1.trans (hcmp x)).trans h2
  have hpos : 0 < ‖x‖ ^ 2 * ‖e x‖ ^ 2 :=
    mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hx))
      (sq_pos_of_pos (norm_pos_iff.mpr hex))
  apply (mul_le_mul_iff_left₀ hpos).mp
  convert h3 using 1 <;> ring

/-- Ordered eigenvalues respect pointwise Rayleigh comparison under an
invertible linear change of variables. -/
theorem ordered_spectral_comparison (A B : E →ₗ[ℝ] E)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (e : E ≃ₗ[ℝ] E)
    (hcmp : ∀ x, inner ℝ x (A x) * ‖e x‖ ^ 2 ≤
      inner ℝ (e x) (B (e x)) * ‖x‖ ^ 2) (j : Fin n) :
    hA.eigenvalues hn j ≤ hB.eigenvalues hn j := by
  simpa only [one_mul, zero_mul, add_zero] using
    ordered_spectral_affine_comparison A B hA hB hn e 1 0 1 0
      zero_le_one zero_le_one (by simpa only [one_mul, zero_mul, add_zero] using hcmp) j

/-- Courant--Fischer transfer for a positive semidefinite quadratic form under
an invertible normalization whose squared norm lies between `1-η` and `1+η`.
All comparisons are proved from the two quadratic-form identities. -/
theorem ordered_spectral_scaling (A B : E →ₗ[ℝ] E)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (e : E ≃ₗ[ℝ] E)
    (η : ℝ) (hη : 0 ≤ η) (hη' : η < 1)
    (hpsd : ∀ x, 0 ≤ inner ℝ x (A x))
    (hq : ∀ x, inner ℝ (e x) (B (e x)) = inner ℝ x (A x))
    (hT : ∀ x, (1 - η) * ‖x‖ ^ 2 ≤ ‖e x‖ ^ 2 ∧
      ‖e x‖ ^ 2 ≤ (1 + η) * ‖x‖ ^ 2) (j : Fin n) :
    hA.eigenvalues hn j / (1 + η) ≤ hB.eigenvalues hn j ∧
      hB.eigenvalues hn j ≤ hA.eigenvalues hn j / (1 - η) := by
  have hp : 0 < 1 + η := by linarith
  have hm : 0 < 1 - η := by linarith
  constructor
  · have hc : ∀ x, (1 * inner ℝ x (A x) + 0 * ‖x‖ ^ 2) * ‖e x‖ ^ 2 ≤
        ((1 + η) * inner ℝ (e x) (B (e x)) + 0 * ‖e x‖ ^ 2) * ‖x‖ ^ 2 := by
      intro x
      simp only [one_mul, zero_mul, add_zero, hq x]
      nlinarith only [mul_le_mul_of_nonneg_left (hT x).2 (hpsd x)]
    have hc' := ordered_spectral_affine_comparison A B hA hB hn e 1 0 (1 + η) 0
      zero_le_one hp.le hc j
    apply (div_le_iff₀ hp).mpr
    simpa only [one_mul, add_zero, mul_comm] using hc'
  · have hc : ∀ y, ((1 - η) * inner ℝ y (B y) + 0 * ‖y‖ ^ 2) * ‖e.symm y‖ ^ 2 ≤
        (1 * inner ℝ (e.symm y) (A (e.symm y)) + 0 * ‖e.symm y‖ ^ 2) * ‖y‖ ^ 2 := by
      intro y
      have hq' : inner ℝ y (B y) = inner ℝ (e.symm y) (A (e.symm y)) := by
        simpa using hq (e.symm y)
      have ht := (hT (e.symm y)).1
      simp only [e.apply_symm_apply] at ht
      simp only [one_mul, zero_mul, add_zero, hq']
      nlinarith only [mul_le_mul_of_nonneg_left ht (hpsd (e.symm y))]
    have hc' := ordered_spectral_affine_comparison B A hB hA hn e.symm (1 - η) 0 1 0
      hm.le zero_le_one hc j
    apply (le_div_iff₀ hm).mpr
    simpa only [one_mul, add_zero, mul_comm] using hc'

end OrderedSpectrum

section MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Real Euclidean matrix quadratic form, with the function-vector convention
used for transition counts. -/
theorem euclidean_matrix_quadratic (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    inner ℝ x (Matrix.toEuclideanLin A x) =
      (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [Matrix.toEuclideanLin_apply, dotProduct_comm]

omit [DecidableEq ι] in
theorem euclidean_norm_sq_dot (x : EuclideanSpace ℝ ι) :
    ‖x‖ ^ 2 = (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp x := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- Loewner/affine comparison of every ordered eigenvalue, proved directly from
quadratic forms. Eigenvalues use Mathlib's decreasing order. -/
theorem matrix_ordered_affine_comparison (A B : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (α β γ δ : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hcmp : ∀ x : ι → ℝ,
      α * (x ⬝ᵥ (A *ᵥ x)) + β * (x ⬝ᵥ x) ≤
      γ * (x ⬝ᵥ (B *ᵥ x)) + δ * (x ⬝ᵥ x))
    (j : Fin (Fintype.card ι)) :
    α * hA.eigenvalues₀ j + β ≤ γ * hB.eigenvalues₀ j + δ := by
  apply ordered_spectral_affine_comparison
    (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B)
    (Matrix.isHermitian_iff_isSymmetric.mp hA)
    (Matrix.isHermitian_iff_isSymmetric.mp hB) finrank_euclideanSpace
    (LinearEquiv.refl ℝ _) α β γ δ hα hγ
  intro x
  simp only [LinearEquiv.refl_apply, euclidean_matrix_quadratic, euclidean_norm_sq_dot]
  exact mul_le_mul_of_nonneg_right (hcmp (WithLp.ofLp x)) (Finset.sum_nonneg fun i _ => mul_self_nonneg _)

/-- Ordinary quadratic-form order implies order of the complete sorted spectrum. -/
theorem matrix_ordered_comparison (A B : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hcmp : ∀ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x))
    (j : Fin (Fintype.card ι)) : hA.eigenvalues₀ j ≤ hB.eigenvalues₀ j := by
  simpa only [one_mul, zero_mul, add_zero] using
    matrix_ordered_affine_comparison A B hA hB 1 0 1 0 zero_le_one zero_le_one
      (by simpa only [one_mul, zero_mul, add_zero] using hcmp) j

/-- Ordered matrix eigenvalue comparison under an invertible congruence.
The quadratic identity is exactly `B = C⁻ᵀ A C⁻¹`, expressed without selecting
a matrix inverse; `e` is the invertible substitution `y = C x`. -/
theorem matrix_ordered_scaling (A B : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (e : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι)
    (η : ℝ) (hη : 0 ≤ η) (hη' : η < 1)
    (hpsd : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x))
    (hq : ∀ x : EuclideanSpace ℝ ι,
      WithLp.ofLp (e x) ⬝ᵥ (B *ᵥ WithLp.ofLp (e x)) =
        WithLp.ofLp x ⬝ᵥ (A *ᵥ WithLp.ofLp x))
    (hT : ∀ x : EuclideanSpace ℝ ι,
      (1 - η) * ‖x‖ ^ 2 ≤ ‖e x‖ ^ 2 ∧ ‖e x‖ ^ 2 ≤ (1 + η) * ‖x‖ ^ 2)
    (j : Fin (Fintype.card ι)) :
    hA.eigenvalues₀ j / (1 + η) ≤ hB.eigenvalues₀ j ∧
      hB.eigenvalues₀ j ≤ hA.eigenvalues₀ j / (1 - η) := by
  apply ordered_spectral_scaling
    (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B)
    (Matrix.isHermitian_iff_isSymmetric.mp hA)
    (Matrix.isHermitian_iff_isSymmetric.mp hB) finrank_euclideanSpace e η hη hη'
  · intro x
    rw [euclidean_matrix_quadratic]
    exact hpsd _
  · intro x
    simpa only [euclidean_matrix_quadratic] using hq x
  · exact hT

/-- Positive semidefinite quadratic forms have nonnegative sorted eigenvalues. -/
theorem matrix_ordered_nonneg (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (hpsd : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x))
    (j : Fin (Fintype.card ι)) : 0 ≤ hA.eigenvalues₀ j := by
  apply eigenvalue_nonneg_of_nonneg
    ((Matrix.isHermitian_iff_isSymmetric.mp hA).hasEigenvalue_eigenvalues
      finrank_euclideanSpace j)
  intro x
  simpa only [RCLike.re_to_real, euclidean_matrix_quadratic] using hpsd (WithLp.ofLp x)

/-- Inverse square root of a positive diagonal degree matrix. -/
noncomputable def inverseSqrtDiagonal (t : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => (Real.sqrt (t i))⁻¹)

/-- Normalization by the positive diagonal degree matrix. -/
noncomputable def diagonalNormalize (A : Matrix ι ι ℝ) (t : ι → ℝ) : Matrix ι ι ℝ :=
  inverseSqrtDiagonal t * A * inverseSqrtDiagonal t

theorem diagonalNormalize_isHermitian (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (t : ι → ℝ) : (diagonalNormalize A t).IsHermitian := by
  have hD : (inverseSqrtDiagonal t)ᴴ = inverseSqrtDiagonal t := by
    simp [inverseSqrtDiagonal]
  simpa only [diagonalNormalize, hD] using
    Matrix.isHermitian_conjTranspose_mul_mul (inverseSqrtDiagonal t) hA

/-- The actual invertible substitution by the square root of a positive diagonal
matrix, including its explicitly defined inverse. -/
noncomputable def diagonalSqrtEquiv (t : ι → ℝ) (ht : ∀ i, 0 < t i) :
    EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (fun i => Real.sqrt (t i) * x i)
  invFun y := WithLp.toLp 2 (fun i => y i / Real.sqrt (t i))
  left_inv x := by
    ext i
    simp [ne_of_gt (Real.sqrt_pos.mpr (ht i))]
  right_inv y := by
    ext i
    change Real.sqrt (t i) * (y i / Real.sqrt (t i)) = y i
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (ht i))]
  map_add' x y := by
    ext i
    simp [mul_add]
  map_smul' c x := by
    ext i
    simp [mul_left_comm]

omit [DecidableEq ι] in
@[simp] theorem diagonalSqrtEquiv_apply (t : ι → ℝ) (ht : ∀ i, 0 < t i)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    diagonalSqrtEquiv t ht x i = Real.sqrt (t i) * x i := rfl

omit [DecidableEq ι] in
theorem diagonalSqrtEquiv_norm_sq (t : ι → ℝ) (ht : ∀ i, 0 < t i)
    (x : EuclideanSpace ℝ ι) :
    ‖diagonalSqrtEquiv t ht x‖ ^ 2 = ∑ i, t i * (x i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_pow, Real.sq_sqrt (ht i).le]

/-- Cancellation of the normalization factors in the quadratic form. -/
theorem diagonalNormalize_quadratic (A : Matrix ι ι ℝ) (t : ι → ℝ)
    (ht : ∀ i, 0 < t i) (x : EuclideanSpace ℝ ι) :
    WithLp.ofLp (diagonalSqrtEquiv t ht x) ⬝ᵥ
        (diagonalNormalize A t *ᵥ WithLp.ofLp (diagonalSqrtEquiv t ht x)) =
      WithLp.ofLp x ⬝ᵥ (A *ᵥ WithLp.ofLp x) := by
  let y := WithLp.ofLp (diagonalSqrtEquiv t ht x)
  have h1 : inverseSqrtDiagonal t *ᵥ y = WithLp.ofLp x := by
    ext i
    simp [y, inverseSqrtDiagonal, Matrix.mulVec_diagonal, ne_of_gt (Real.sqrt_pos.mpr (ht i))]
  have h2 : y ᵥ* inverseSqrtDiagonal t = WithLp.ofLp x := by
    ext i
    simp [y, inverseSqrtDiagonal, Matrix.vecMul_diagonal, ne_of_gt (Real.sqrt_pos.mpr (ht i)), mul_comm]
  change y ⬝ᵥ (diagonalNormalize A t *ᵥ y) = _
  rw [diagonalNormalize, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1,
    Matrix.dotProduct_mulVec, h2]

/-- The full matrix min--max scaling conclusion used after (19), for the actual
normalization `diag(t)⁻¹ᐟ² A diag(t)⁻¹ᐟ²`. -/
theorem matrix_ordered_diagonal_scaling (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (t : ι → ℝ) (ht : ∀ i, 0 < t i)
    (η : ℝ) (hη : 0 ≤ η) (hη' : η < 1)
    (hpsd : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x))
    (hT : ∀ i, 1 - η ≤ t i ∧ t i ≤ 1 + η)
    (j : Fin (Fintype.card ι)) :
    hA.eigenvalues₀ j / (1 + η) ≤
      (diagonalNormalize_isHermitian A hA t).eigenvalues₀ j ∧
    (diagonalNormalize_isHermitian A hA t).eigenvalues₀ j ≤
      hA.eigenvalues₀ j / (1 - η) := by
  apply matrix_ordered_scaling A (diagonalNormalize A t) hA
    (diagonalNormalize_isHermitian A hA t) (diagonalSqrtEquiv t ht) η hη hη' hpsd
    (diagonalNormalize_quadratic A t ht)
  intro x
  rw [diagonalSqrtEquiv_norm_sq, EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hT i).1 (sq_nonneg _)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hT i).2 (sq_nonneg _)

end MatrixOrder

end PsgEst
