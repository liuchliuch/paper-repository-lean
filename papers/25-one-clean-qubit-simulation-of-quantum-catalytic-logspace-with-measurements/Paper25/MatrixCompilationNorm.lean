import Paper25.WalkFilter
import Paper25.CircuitModel

/-!
# Dimension-independent operator-norm bounds for compiling local gates

Every norm in this module is the actual Euclidean (`L2Operator`) matrix norm.
SELECT, adding an identity register, and computational-basis reindexing have
no dimension factor. All statements allow empty finite index types.
-/

noncomputable section
open scoped ComplexConjugate Matrix.Norms.L2Operator
namespace Paper25.MatrixCompilationNorm

section Reindex

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Reindexing a square matrix by an equivalence preserves the Euclidean operator norm. -/
theorem submatrix_equiv_opNorm (e : a ≃ b) (A : Matrix b b ℂ) :
    ‖A.submatrix e e‖ = ‖A‖ := by
  have hle (f : a ≃ b) (B : Matrix b b ℂ) : ‖B.submatrix f f‖ ≤ ‖B‖ := by
    have h := isometryCompression_opNorm_le (basisEmbedding f)
      (basisEmbedding_isometry f f.injective) B
    rwa [basisEmbedding_compression] at h
  apply le_antisymm (hle e A)
  have h := isometryCompression_opNorm_le (basisEmbedding e.symm)
    (basisEmbedding_isometry e.symm e.symm.injective) (A.submatrix e e)
  rw [basisEmbedding_compression] at h
  simpa [Matrix.submatrix_submatrix] using h

/-- The same reindexing preserves an approximation error exactly. -/
theorem submatrix_equiv_error (e : a ≃ b) (A B : Matrix b b ℂ) :
    ‖A.submatrix e e - B.submatrix e e‖ = ‖A - B‖ := by
  have heq : A.submatrix e e - B.submatrix e e = (A - B).submatrix e e := by
    ext i j
    rfl
  rw [heq]
  exact submatrix_equiv_opNorm e (A - B)

end Reindex

section Selection

variable {s n : Type*} [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n]

/-- A coherent block-diagonal selector is bounded by the largest branch bound,
with no factor depending on the number of selectors or data states. -/
theorem selectMatrix_opNorm_le (K : s → Matrix n n ℂ) (b : ℝ) (hb : 0 ≤ b)
    (hK : ∀ j, ‖K j‖ ≤ b) : ‖selectMatrix K‖ ≤ b := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro x
  let xs : s → EuclideanSpace ℂ n := fun j => WithLp.toLp 2 (fun i => x (j, i))
  let ys : s → EuclideanSpace ℂ n := fun j =>
    WithLp.toLp 2 (Matrix.mulVec (K j) (fun i => x (j, i)))
  have hbranch (j : s) : ‖ys j‖ ^ 2 ≤ b ^ 2 * ‖xs j‖ ^ 2 := by
    have h := (Matrix.l2_opNorm_mulVec (K j) (xs j)).trans
      (mul_le_mul_of_nonneg_right (hK j) (norm_nonneg (xs j)))
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hb (norm_nonneg (xs j)))).mpr h
    simpa only [mul_pow] using hs
  have hout : ‖Matrix.toEuclideanCLM (n := s × n) (𝕜 := ℂ) (selectMatrix K) x‖ ^ 2 =
      ∑ j, ‖ys j‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    change ‖Matrix.mulVec (selectMatrix K) (WithLp.ofLp x) (j, i)‖ ^ 2 =
      ‖Matrix.mulVec (K j) (fun k => x (j, k)) i‖ ^ 2
    simp [Matrix.mulVec, dotProduct, selectMatrix, Fintype.sum_prod_type]
  have hin : ‖x‖ ^ 2 = ∑ j, ‖xs j‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    rfl
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hb (norm_nonneg x))).mp
  rw [mul_pow, hout, hin, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => hbranch j

/-- Coherent selection preserves a uniform per-branch approximation bound. -/
theorem selectMatrix_error (K L : s → Matrix n n ℂ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hKL : ∀ j, ‖K j - L j‖ ≤ τ) : ‖selectMatrix K - selectMatrix L‖ ≤ τ := by
  have heq : selectMatrix K - selectMatrix L = selectMatrix (fun j => K j - L j) := by
    ext ⟨j, i⟩ ⟨k, l⟩
    by_cases h : j = k <;> simp [selectMatrix, h]
  rw [heq]
  exact selectMatrix_opNorm_le _ τ hτ hKL

end Selection

section IdentityRegister

variable {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]

/-- Adding an arbitrary identity register does not enlarge operator norm. -/
theorem tensor_identity_opNorm_le (A : Matrix n n ℂ) :
    ‖Matrix.kronecker A (1 : Matrix r r ℂ)‖ ≤ ‖A‖ := by
  have heq : (Matrix.kronecker A (1 : Matrix r r ℂ)).submatrix
      (Equiv.prodComm r n) (Equiv.prodComm r n) = selectMatrix (fun _ : r => A) := by
    ext ⟨j, i⟩ ⟨k, l⟩
    by_cases h : j = k <;> simp [Matrix.kronecker, selectMatrix, Matrix.one_apply, h]
  calc
    _ = ‖(Matrix.kronecker A (1 : Matrix r r ℂ)).submatrix
        (Equiv.prodComm r n) (Equiv.prodComm r n)‖ := (submatrix_equiv_opNorm _ _).symm
    _ = ‖selectMatrix (fun _ : r => A)‖ := by rw [heq]
    _ ≤ ‖A‖ := selectMatrix_opNorm_le _ _ (norm_nonneg A) (fun _ => le_rfl)

/-- Identity on the left likewise carries no dimension factor. -/
theorem identity_tensor_opNorm_le (A : Matrix n n ℂ) :
    ‖Matrix.kronecker (1 : Matrix r r ℂ) A‖ ≤ ‖A‖ := by
  have heq : Matrix.kronecker (1 : Matrix r r ℂ) A = selectMatrix (fun _ : r => A) := by
    ext ⟨j, i⟩ ⟨k, l⟩
    by_cases h : j = k <;> simp [Matrix.kronecker, selectMatrix, Matrix.one_apply, h]
  rw [heq]
  exact selectMatrix_opNorm_le _ _ (norm_nonneg A) (fun _ => le_rfl)

theorem tensor_identity_error (A B : Matrix n n ℂ) :
    ‖Matrix.kronecker A (1 : Matrix r r ℂ) - Matrix.kronecker B (1 : Matrix r r ℂ)‖ ≤ ‖A - B‖ := by
  have heq : Matrix.kronecker A (1 : Matrix r r ℂ) - Matrix.kronecker B (1 : Matrix r r ℂ) =
      Matrix.kronecker (A - B) (1 : Matrix r r ℂ) := by
    ext i j
    simp [Matrix.kronecker, sub_mul]
  rw [heq]
  exact tensor_identity_opNorm_le (r := r) (A - B)

end IdentityRegister

section Placement

open OperationalModel

/-- The actual physical wire-placement semantics is norm-contractive. -/
theorem placement_lift_opNorm_le {q k : ℕ} (p : Placement q k) (A : Operator k) :
    ‖p.lift A‖ ≤ ‖A‖ := by
  unfold Placement.lift
  rw [submatrix_equiv_opNorm]
  exact tensor_identity_opNorm_le A

/-- Local approximation error lifts to the whole physical register unchanged in size. -/
theorem placement_lift_error {q k : ℕ} (p : Placement q k) (A B : Operator k) :
    ‖p.lift A - p.lift B‖ ≤ ‖A - B‖ := by
  have heq : p.lift A - p.lift B = p.lift (A - B) := by
    ext i j
    by_cases h : (p.split i).2 = (p.split j).2 <;> simp [Placement.lift_apply, h]
  rw [heq]
  exact placement_lift_opNorm_le p (A - B)

end Placement

section Composition

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Adjoint compilation has exactly the same approximation error. -/
theorem adjoint_sub_opNorm (A B : Matrix n n ℂ) :
    ‖A.conjTranspose - B.conjTranspose‖ = ‖A - B‖ := by
  rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]

lemma unitary_opNorm_le_one (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) : ‖U‖ ≤ 1 := by
  have hu : ‖U‖ * ‖U‖ = ‖(1 : Matrix n n ℂ)‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self,
      show U.conjTranspose * U = 1 from hU.1]
  have h1 := matrix_opNorm_one_le n
  nlinarith [norm_nonneg U]

/-- Errors of two unitary factors add, including empty matrix index types. -/
theorem unitary_product_error_le (A A' B B' : Matrix n n ℂ)
    (hA' : A' ∈ Matrix.unitaryGroup n ℂ) (hB : B ∈ Matrix.unitaryGroup n ℂ)
    (a b : ℝ) (hA : ‖A - A'‖ ≤ a) (hBerr : ‖B - B'‖ ≤ b) :
    ‖A * B - A' * B'‖ ≤ a + b := by
  have hid : A * B - A' * B' = (A - A') * B + A' * (B - B') := by noncomm_ring
  rw [hid]
  calc
    _ ≤ ‖(A - A') * B‖ + ‖A' * (B - B')‖ := norm_add_le _ _
    _ ≤ (‖A - A'‖ * ‖B‖) + (‖A'‖ * ‖B - B'‖) :=
      add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ ≤ ‖A - A'‖ + ‖B - B'‖ := by
      apply add_le_add
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left (unitary_opNorm_le_one B hB) (norm_nonneg (A - A'))
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right (unitary_opNorm_le_one A' hA') (norm_nonneg (B - B'))
    _ ≤ a + b := add_le_add hA hBerr

/-- Preparing and unpreparing an approximate unitary costs at most twice its error. -/
theorem unitary_sandwich_error_le (P P' S : Matrix n n ℂ)
    (hP : P ∈ Matrix.unitaryGroup n ℂ) (hP' : P' ∈ Matrix.unitaryGroup n ℂ)
    (hS : S ∈ Matrix.unitaryGroup n ℂ) (τ : ℝ) (hPP : ‖P - P'‖ ≤ τ) :
    ‖P.conjTranspose * S * P - P'.conjTranspose * S * P'‖ ≤ 2 * τ := by
  have hadj : ‖P.conjTranspose - P'.conjTranspose‖ ≤ τ := by
    rw [adjoint_sub_opNorm]
    exact hPP
  have hleft : ‖P.conjTranspose * S - P'.conjTranspose * S‖ ≤ τ := by
    have h := unitary_product_error_le P.conjTranspose P'.conjTranspose S S
      (unitary.star_mem hP') hS τ 0 hadj (by simp)
    simpa only [add_zero] using h
  have h := unitary_product_error_le (P.conjTranspose * S) (P'.conjTranspose * S) P P'
    ((Matrix.unitaryGroup n ℂ).mul_mem (unitary.star_mem hP') hS) hP τ τ hleft hPP
  linarith

/-- When the selected operation is approximated as well, the preparation and
selection budgets add as 2τ + σ. -/
theorem unitary_sandwich_total_error_le (P P' S S' : Matrix n n ℂ)
    (hP : P ∈ Matrix.unitaryGroup n ℂ) (hP' : P' ∈ Matrix.unitaryGroup n ℂ)
    (hS : S ∈ Matrix.unitaryGroup n ℂ) (τ σ : ℝ)
    (hPP : ‖P - P'‖ ≤ τ) (hSS : ‖S - S'‖ ≤ σ) :
    ‖P.conjTranspose * S * P - P'.conjTranspose * S' * P'‖ ≤ 2 * τ + σ := by
  have hselect : ‖P'.conjTranspose * S * P' - P'.conjTranspose * S' * P'‖ ≤ σ := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    exact (isometryCompression_opNorm_le P' (show P'.conjTranspose * P' = 1 from hP'.1) _).trans hSS
  calc
    _ ≤ ‖P.conjTranspose * S * P - P'.conjTranspose * S * P'‖ +
        ‖P'.conjTranspose * S * P' - P'.conjTranspose * S' * P'‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le
        (P.conjTranspose * S * P - P'.conjTranspose * S * P')
        (P'.conjTranspose * S * P' - P'.conjTranspose * S' * P')
    _ ≤ 2 * τ + σ := add_le_add (unitary_sandwich_error_le P P' S hP hP' hS τ hPP) hselect

end Composition

end Paper25.MatrixCompilationNorm
