import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic.Linarith

/-!
# Actual finite-rank adversary operators

Unlike `gammaWeight_sup_eq`, the results here concern the operator norm of
an actual continuous linear map. The two orthonormal families may live in
infinite-dimensional Hilbert spaces. Instantiating these families with the
paper's normalized Fourier–Dirichlet functions still requires the measure
and Fourier constructions; no such instantiation is assumed in this file.
-/

noncomputable section
open scoped ComplexConjugate
open InnerProductSpace

namespace PUT.FiniteAdversary

variable {ι E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The actual sum `∑ i ∈ s, wᵢ |eᵢ⟩⟨fᵢ|`. -/
def operator (s : Finset ι) (w : ι → ℝ) (e : ι → E) (f : ι → F) : F →L[ℂ] E :=
  ∑ i ∈ s, (toDualMap ℂ F (f i)).smulRight ((w i : ℂ) • e i)

@[simp] theorem operator_apply (s : Finset ι) (w : ι → ℝ) (e : ι → E)
    (f : ι → F) (x : F) :
    operator s w e f x = ∑ i ∈ s, ((w i : ℂ) * inner ℂ (f i) x) • e i := by
  simp only [operator, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, toDualMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, mul_comm]

/-- Exact Pythagoras identity for a finite orthonormal expansion. -/
theorem norm_sq_sum (s : Finset ι) (e : ι → E) (he : Orthonormal ℂ e)
    (c : ι → ℂ) :
    ‖∑ i ∈ s, c i • e i‖ ^ 2 = ∑ i ∈ s, ‖c i‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), he.inner_sum c c s]
  simp only [map_sum, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Bessel's inequality on the input family bounds the genuine operator. -/
theorem norm_operator_le (s : Finset ι) (w : ι → ℝ) (e : ι → E) (f : ι → F)
    (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ i ∈ s, |w i| ≤ A) : ‖operator s w e f‖ ≤ A := by
  apply ContinuousLinearMap.opNorm_le_bound _ hA
  intro x
  have hsq : ‖operator s w e f x‖ ^ 2 ≤ A ^ 2 * ‖x‖ ^ 2 := by
    rw [operator_apply, norm_sq_sum s e he]
    calc
      (∑ i ∈ s, ‖(w i : ℂ) * inner ℂ (f i) x‖ ^ 2)
          ≤ ∑ i ∈ s, A ^ 2 * ‖inner ℂ (f i) x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _) (hw i hi) 2) (sq_nonneg _)
      _ = A ^ 2 * ∑ i ∈ s, ‖inner ℂ (f i) x‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ A ^ 2 * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (hf.sum_inner_products_le x) (sq_nonneg A)
  have hnn : 0 ≤ A * ‖x‖ := mul_nonneg hA (norm_nonneg _)
  nlinarith [norm_nonneg (operator s w e f x)]

/-- Every retained input family vector is an exact singular direction. -/
theorem operator_on_family (s : Finset ι) (w : ι → ℝ) (e : ι → E) (f : ι → F)
    (hf : Orthonormal ℂ f) {j : ι} (hj : j ∈ s) :
    operator s w e f (f j) = (w j : ℂ) • e j := by
  classical
  simp [operator_apply, orthonormal_iff_ite.mp hf, hj]

/-- If a weight attains `A`, the actual operator norm equals `A`. -/
theorem norm_operator_eq (s : Finset ι) (w : ι → ℝ) (e : ι → E) (f : ι → F)
    (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ i ∈ s, |w i| ≤ A) {j : ι} (hj : j ∈ s) (hwj : w j = A) :
    ‖operator s w e f‖ = A := by
  apply le_antisymm (norm_operator_le s w e f he hf A hA hw)
  have h := (operator s w e f).le_opNorm (f j)
  rw [operator_on_family s w e f hf hj, hwj, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA,
    he.norm_eq_one j, hf.norm_eq_one j, mul_one, mul_one] at h
  exact h

/-- Directions orthogonal to the entire retained radial family are killed. -/
theorem operator_eq_zero_of_orthogonal (s : Finset ι) (w : ι → ℝ)
    (e : ι → E) (f : ι → F) (x : F)
    (hx : ∀ i ∈ s, inner ℂ (f i) x = 0) : operator s w e f x = 0 := by
  rw [operator_apply]
  exact Finset.sum_eq_zero (fun i hi => by rw [hx i hi, mul_zero, zero_smul])

end PUT.FiniteAdversary

