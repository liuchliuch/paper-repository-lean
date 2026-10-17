import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic

/-!
# Existence of a positive eigenvector for a strictly positive symmetric matrix

The quadratic form of a real symmetric matrix attains its maximum on a sphere.
Taking absolute values of the coordinates does not decrease that quadratic form
when every matrix entry is nonnegative. The resulting nonnegative maximizer is
an eigenvector, and strict positivity of the entries excludes zero coordinates.
-/

noncomputable section

open scoped BigOperators

namespace Paper18

/-- A finite nonempty real symmetric matrix with strictly positive entries has
a strictly positive eigenvector. The positive eigenvector is constructed by
maximizing the quadratic form on a sphere; its existence is not a hypothesis. -/
theorem posSymmMatrix_exists_positive_eigenvector
    {κ : Type*} [Fintype κ] [Nonempty κ] (A : Matrix κ κ ℝ)
    (hSymm : ∀ i j, A i j = A j i) (hA : ∀ i j, 0 < A i j) :
    ∃ (lam : ℝ) (v : κ → ℝ), (∀ i, 0 < v i) ∧
      ∀ i, ∑ j, A i j * v j = lam * v i := by
  classical
  have hHerm : A.IsHermitian := by
    ext i j
    simpa using hSymm j i
  let hT := Matrix.isHermitian_iff_isSymmetric.mp hHerm
  let T := hT.toSelfAdjoint
  obtain ⟨x, hx⟩ : ∃ x : EuclideanSpace ℝ κ, x ≠ 0 := exists_ne 0
  have hcompact : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ κ) ‖x‖) :=
    isCompact_sphere _ _
  have hnonempty : (Metric.sphere (0 : EuclideanSpace ℝ κ) ‖x‖).Nonempty :=
    ⟨x, by simp⟩
  obtain ⟨x₀, hx₀mem, hx₀max⟩ := hcompact.exists_isMaxOn hnonempty
    T.val.reApplyInnerSelf_continuous.continuousOn
  let y : EuclideanSpace ℝ κ := WithLp.toLp 2 (fun i => |x₀ i|)
  have hynorm : ‖y‖ = ‖x₀‖ := by
    simp [EuclideanSpace.norm_eq, y, Real.norm_eq_abs]
  have hx₀norm : ‖x₀‖ = ‖x‖ := by simpa using hx₀mem
  have hquad (z : EuclideanSpace ℝ κ) :
      T.val.reApplyInnerSelf z = ∑ i, z i * (∑ j, A i j * z j) := by
    change inner ℝ (Matrix.toEuclideanLin A z) z = _
    simp [EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]
  have hquad_abs : T.val.reApplyInnerSelf x₀ ≤ T.val.reApplyInnerSelf y := by
    rw [hquad, hquad]
    simp only [y, PiLp.toLp_apply, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    calc
      x₀ i * (A i j * x₀ j) ≤ |x₀ i * (A i j * x₀ j)| := le_abs_self _
      _ = |x₀ i| * (A i j * |x₀ j|) := by
        rw [abs_mul, abs_mul, abs_of_pos (hA i j)]
  have hymax : IsMaxOn T.val.reApplyInnerSelf
      (Metric.sphere (0 : EuclideanSpace ℝ κ) ‖y‖) y := by
    intro z hz
    have hz' : z ∈ Metric.sphere (0 : EuclideanSpace ℝ κ) ‖x‖ := by
      simpa [hynorm, hx₀norm] using hz
    exact (hx₀max hz').trans hquad_abs
  have hyne : y ≠ 0 := by
    intro hyzero
    have hxnorm : ‖x‖ = 0 := by
      rw [← hx₀norm, ← hynorm, hyzero, norm_zero]
    exact hx (norm_eq_zero.mp hxnorm)
  have hyeigen := T.prop.eq_smul_self_of_isLocalExtrOn (Or.inr hymax.localize)
  let lam := T.val.rayleighQuotient y
  have hye : ∀ i, ∑ j, A i j * y j = lam * y i := by
    intro i
    have hi := congrArg (fun z : EuclideanSpace ℝ κ => z i) hyeigen
    simpa [T, hT, lam, Matrix.toEuclideanLin_apply, Matrix.mulVec,
      dotProduct, PiLp.smul_apply] using hi
  have hynonneg : ∀ i, 0 ≤ y i := fun i => abs_nonneg _
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hyne (by ext i; exact h i)
  have hyj : 0 < y j := lt_of_le_of_ne (hynonneg j) (Ne.symm hj)
  have hypos : ∀ i, 0 < y i := by
    intro i
    have hrow : 0 < ∑ k, A i k * y k :=
      Finset.sum_pos' (fun k _ => mul_nonneg (hA i k).le (hynonneg k))
        ⟨j, Finset.mem_univ j, mul_pos (hA i j) hyj⟩
    by_contra h
    have hyzero : y i = 0 := le_antisymm (le_of_not_gt h) (hynonneg i)
    rw [hye i, hyzero, mul_zero] at hrow
    exact (lt_irrefl 0) hrow
  exact ⟨lam, fun i => y i, hypos, hye⟩

/-- The positive eigenvector can be normalized to be `1` at any chosen
coordinate, and its eigenvalue is strictly positive. -/
theorem posSymmMatrix_exists_normalized_positive_eigenvector
    {κ : Type*} [Fintype κ] [Nonempty κ] (A : Matrix κ κ ℝ)
    (hSymm : ∀ i j, A i j = A j i) (hA : ∀ i j, 0 < A i j) (i₀ : κ) :
    ∃ (lam : ℝ) (v : κ → ℝ), 0 < lam ∧ (∀ i, 0 < v i) ∧ v i₀ = 1 ∧
      ∀ i, ∑ j, A i j * v j = lam * v i := by
  classical
  obtain ⟨lam, v, hv, hve⟩ := posSymmMatrix_exists_positive_eigenvector A hSymm hA
  have hrow : 0 < ∑ j, A i₀ j * v j :=
    Finset.sum_pos' (fun j _ => (mul_pos (hA i₀ j) (hv j)).le)
      ⟨i₀, Finset.mem_univ _, mul_pos (hA i₀ i₀) (hv i₀)⟩
  have hlam : 0 < lam :=
    (mul_pos_iff_of_pos_right (hv i₀)).mp (by rwa [hve i₀] at hrow)
  refine ⟨lam, fun i => v i / v i₀, hlam, fun i => div_pos (hv i) (hv i₀),
    div_self (hv i₀).ne', ?_⟩
  intro i
  simp only [← mul_div_assoc, ← Finset.sum_div, hve]

end Paper18
