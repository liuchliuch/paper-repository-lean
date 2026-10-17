import Paper26.QuantumModel

/-!
# Finite Hermitian polarization and actual vector states

These are finite matrix identities. Positive-vector probes are genuine
normalized density matrices, and the real scalar probes recover every complex
entry of a Hermitian matrix, including coincident coordinate indices.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace Paper26.FinitePolarization
open QuantumModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def normSq (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

omit [DecidableEq ι] in
theorem normSq_nonneg (v : ι → ℂ) : 0 ≤ normSq v :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [DecidableEq ι] in
theorem normSq_zero : normSq (0 : ι → ℂ) = 0 := by simp [normSq]

omit [DecidableEq ι] in
theorem normSq_eq_zero (v : ι → ℂ) (h : normSq v = 0) : v = 0 := by
  funext i
  have hi : ‖v i‖ ^ 2 ≤ normSq v :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i)
  rw [h] at hi
  have hz : ‖v i‖ ^ 2 = 0 := le_antisymm hi (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

omit [DecidableEq ι] in
theorem normSq_eq_zero_iff (v : ι → ℂ) : normSq v = 0 ↔ v = 0 := by
  constructor
  · exact normSq_eq_zero v
  · intro h
    rw [h, normSq_zero]

omit [DecidableEq ι] in
theorem normSq_pos_iff (v : ι → ℂ) : 0 < normSq v ↔ v ≠ 0 := by
  rw [lt_iff_le_and_ne, and_iff_right (normSq_nonneg v), ne_eq, eq_comm,
    normSq_eq_zero_iff]

omit [DecidableEq ι] in
/-- The true trace of the rank-one outer product is its squared vector norm. -/
theorem trace_outer (v : ι → ℂ) :
    Matrix.trace (Matrix.vecMulVec v (star v)) = (normSq v : ℂ) := by
  rw [Matrix.trace_vecMulVec]
  simp [dotProduct, normSq, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- A genuine normalized density matrix for every nonzero vector. -/
def vectorDensity (v : ι → ℂ) (h : 0 < normSq v) : Density ι where
  matrix := (((normSq v)⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec v (star v)
  positive := (Matrix.posSemidef_vecMulVec_self_star v).smul
    (RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr (normSq_nonneg v)))
  trace_one := by
    rw [Matrix.trace_smul, trace_outer]
    change (((normSq v)⁻¹ : ℝ) : ℂ) * (normSq v : ℂ) = 1
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ h.ne', Complex.ofReal_one]

omit [DecidableEq ι] in
@[simp] theorem vectorDensity_matrix (v : ι → ℂ) (h : 0 < normSq v) :
    (vectorDensity v h).matrix =
      (((normSq v)⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec v (star v) := rfl

/-- Real scalar probe used to define a positive classical kernel. -/
def quadratic (E : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  (star v ⬝ᵥ E *ᵥ v).re

omit [DecidableEq ι] in
theorem quadratic_zero (E : Matrix ι ι ℂ) : quadratic E 0 = 0 := by
  simp [quadratic]

omit [DecidableEq ι] in
theorem quadratic_nonneg {E : Matrix ι ι ℂ} (hE : E.PosSemidef) (v : ι → ℂ) :
    0 ≤ quadratic E v := hE.2 v |>.1

omit [DecidableEq ι] in
theorem quadratic_im_zero {E : Matrix ι ι ℂ} (hE : E.IsHermitian) (v : ι → ℂ) :
    (star v ⬝ᵥ E *ᵥ v).im = 0 := hE.im_star_dotProduct_mulVec_self v

omit [DecidableEq ι] in
/-- Exact complex rank-one trace/quadratic identity, without positivity. -/
theorem outer_trace_complex (E : Matrix ι ι ℂ) (v : ι → ℂ) :
    Matrix.trace (Matrix.vecMulVec v (star v) * E) = star v ⬝ᵥ E *ᵥ v := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq ι] in
theorem outer_trace (E : Matrix ι ι ℂ) (v : ι → ℂ) :
    (Matrix.trace (Matrix.vecMulVec v (star v) * E)).re = quadratic E v := by
  rw [outer_trace_complex]
  rfl

omit [DecidableEq ι] in
/-- The probe is the vector mass times the Born trace of its true pure state. -/
theorem vectorDensity_trace_mul (E : Matrix ι ι ℂ) (v : ι → ℂ) (h : 0 < normSq v) :
    (Matrix.trace ((vectorDensity v h).matrix * E)).re = quadratic E v / normSq v := by
  rw [vectorDensity_matrix, Matrix.smul_mul, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, outer_trace]
  ring

omit [DecidableEq ι] in
theorem quadratic_eq_mass_born (E : Matrix ι ι ℂ) (v : ι → ℂ) (h : 0 < normSq v) :
    quadratic E v = normSq v * (Matrix.trace ((vectorDensity v h).matrix * E)).re := by
  rw [vectorDensity_trace_mul]
  field_simp

theorem quadratic_one (v : ι → ℂ) : quadratic (1 : Matrix ι ι ℂ) v = normSq v := by
  rw [← outer_trace, Matrix.mul_one, trace_outer, Complex.ofReal_re]

omit [DecidableEq ι] in
theorem quadratic_eq_zero_of_normSq_zero (E : Matrix ι ι ℂ) (v : ι → ℂ)
    (h : normSq v = 0) : quadratic E v = 0 := by
  rw [normSq_eq_zero v h, quadratic_zero]

theorem sesquilinear_single (E : Matrix ι ι ℂ) (i j : ι) (a b : ℂ) :
    star (Pi.single i a) ⬝ᵥ E *ᵥ Pi.single j b = star a * E i j * b := by
  have hs : star (Pi.single i a : ι → ℂ) = Pi.single i (star a) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [Pi.star_apply, Pi.single_apply, hk, Ne.symm hk]
  rw [hs, single_dotProduct, Matrix.mulVec_single]
  simp only [Pi.smul_apply, op_smul_eq_mul, Matrix.col_apply]
  ring

/-- Four positive real scalar probes recover the complete complex matrix
entry. No i≠j hypothesis is needed. The sign of the imaginary probe matches
the convention q(v)=v*Ev. -/
theorem polarization (E : Matrix ι ι ℂ) (hE : E.IsHermitian) (i j : ι) :
    E i j =
      (((quadratic E (Pi.single i 1 + Pi.single j 1) -
          quadratic E (Pi.single i 1 - Pi.single j 1)) / 4 : ℝ) : ℂ) -
        Complex.I * (((quadratic E (Pi.single i 1 + Pi.single j Complex.I) -
          quadratic E (Pi.single i 1 - Pi.single j Complex.I)) / 4 : ℝ) : ℂ) := by
  have hji : E j i = star (E i j) := by
    simpa only [Matrix.conjTranspose_apply] using
      (congrArg (fun A : Matrix ι ι ℂ => A j i) hE.eq).symm
  simp only [quadratic, star_add, star_sub, Matrix.mulVec_add, Matrix.mulVec_sub,
    add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub, sesquilinear_single,
    star_one, one_mul, mul_one, hji]
  apply Complex.ext <;>
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im] <;> ring

end Paper26.FinitePolarization
