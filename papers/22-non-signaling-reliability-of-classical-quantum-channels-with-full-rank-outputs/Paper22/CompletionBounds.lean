import Paper22.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace Paper22

local instance (d : ℕ) : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) where

/-- A Hermitian matrix lies between its scalar operator-norm bounds. -/
theorem matrix_selfAdjoint_norm_bounds {d : ℕ}
    {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsSelfAdjoint X) :
    -(‖X‖ • (1 : Matrix (Fin d) (Fin d) ℂ)) ≤ X ∧
      X ≤ ‖X‖ • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  constructor
  · simpa only [Algebra.algebraMap_eq_smul_one] using IsSelfAdjoint.neg_algebraMap_norm_le_self (a := X) hX
  · simpa only [Algebra.algebraMap_eq_smul_one] using IsSelfAdjoint.le_algebraMap_norm_self (a := X) hX

/-- The operator norm of a Hermitian matrix is characterized by its scalar order interval. -/
theorem matrix_selfAdjoint_norm_le_iff {d : ℕ}
    {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsSelfAdjoint X)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖X‖ ≤ r ↔ -(r • (1 : Matrix (Fin d) (Fin d) ℂ)) ≤ X ∧
      X ≤ r • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  constructor
  · intro h
    obtain ⟨hl, hu⟩ := matrix_selfAdjoint_norm_bounds hX
    have hs : ‖X‖ • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ r • 1 :=
      smul_le_smul_of_nonneg_right h (zero_le_one_matrix d)
    exact ⟨(neg_le_neg hs).trans hl, hu.trans hs⟩
  · rintro ⟨hl, hu⟩
    by_cases htriv : Subsingleton (Matrix (Fin d) (Fin d) ℂ)
    · letI := htriv
      simpa [Subsingleton.elim X 0] using hr
    · haveI : Nontrivial (Matrix (Fin d) (Fin d) ℂ) := not_subsingleton_iff_nontrivial.mp htriv
      have hl' : algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) (-r) ≤ X := by
        simpa only [Algebra.algebraMap_eq_smul_one, neg_smul] using hl
      have hu' : X ≤ algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) r := by
        simpa only [Algebra.algebraMap_eq_smul_one] using hu
      have hls := (algebraMap_le_iff_le_spectrum hX).mp hl'
      have hus := (le_algebraMap_iff_spectrum_le hX).mp hu'
      rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (a := X) hX with h | h
      · exact hus _ h
      · have := hls _ h
        linarith

/-- The weighted conjugation map preserves Hermitian matrices. -/
theorem matrix_weighted_conjugate_selfAdjoint {n d : ℕ}
    (q : Fin n → ℝ) (D : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hD : ∀ x, IsSelfAdjoint (D x))
    {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (∑ x, q x • (D x * X * D x)) := by
  change star (∑ x, q x • (D x * X * D x)) = _
  simp only [star_sum, star_smul, star_trivial, Matrix.star_mul, hX.star_eq]
  apply Finset.sum_congr rfl
  intro x _
  rw [(hD x).star_eq, mul_assoc]

/-- A scalar bound on the second moment bounds weighted conjugation from above. -/
theorem matrix_weighted_conjugate_le {n d : ℕ}
    (q : Fin n → ℝ) (hq : ∀ x, 0 ≤ q x)
    (D : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hD : ∀ x, IsSelfAdjoint (D x))
    {k : ℝ}
    (hS : (∑ x, q x • (D x * D x)) ≤ k • (1 : Matrix (Fin d) (Fin d) ℂ))
    {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsSelfAdjoint X) :
    (∑ x, q x • (D x * X * D x)) ≤
      (k * ‖X‖) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  calc
    (∑ x, q x • (D x * X * D x)) ≤
        ∑ x, q x • (‖X‖ • (D x * D x)) := by
      apply Finset.sum_le_sum
      intro x _
      apply smul_le_smul_of_nonneg_left _ (hq x)
      simpa only [Matrix.mul_smul, smul_mul_assoc, mul_one] using
        (hD x).conjugate_le_conjugate (matrix_selfAdjoint_norm_bounds hX).2
    _ = ‖X‖ • (∑ x, q x • (D x * D x)) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro x _
      exact smul_comm _ _ _
    _ ≤ ‖X‖ • (k • (1 : Matrix (Fin d) (Fin d) ℂ)) :=
      smul_le_smul_of_nonneg_left hS (norm_nonneg X)
    _ = (k * ‖X‖) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      rw [smul_smul, mul_comm]

/-- A weighted Hermitian conjugation map has operator bound given by its second moment. -/
theorem matrix_weighted_conjugate_norm_le {n d : ℕ}
    (q : Fin n → ℝ) (hq : ∀ x, 0 ≤ q x)
    (D : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hD : ∀ x, IsSelfAdjoint (D x))
    {k : ℝ} (hk : 0 ≤ k)
    (hS : (∑ x, q x • (D x * D x)) ≤ k • (1 : Matrix (Fin d) (Fin d) ℂ))
    {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsSelfAdjoint X) :
    ‖∑ x, q x • (D x * X * D x)‖ ≤ k * ‖X‖ := by
  apply (matrix_selfAdjoint_norm_le_iff
    (matrix_weighted_conjugate_selfAdjoint q D hD hX) (mul_nonneg hk (norm_nonneg X))).mpr
  constructor
  · have hn := matrix_weighted_conjugate_le q hq D hD hS hX.neg
    simp only [mul_neg, neg_mul, smul_neg, Finset.sum_neg_distrib, norm_neg] at hn
    exact neg_le.mp hn
  · exact matrix_weighted_conjugate_le q hq D hD hS hX

/-- The defect of weighted conjugation is at most three times the scalar moment bound. -/
theorem matrix_completion_defect_norm_le {n d : ℕ}
    (q : Fin n → ℝ) (hq : ∀ x, 0 ≤ q x)
    (D : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hD : ∀ x, IsSelfAdjoint (D x))
    {k : ℝ} (hk : 0 ≤ k)
    (hB0 : 0 ≤ (∑ x, q x • D x))
    (hB : (∑ x, q x • D x) ≤ k • (1 : Matrix (Fin d) (Fin d) ℂ))
    (hS : (∑ x, q x • (D x * D x)) ≤ k • (1 : Matrix (Fin d) (Fin d) ℂ))
    {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsSelfAdjoint X) :
    ‖(∑ x, q x • D x) * X + X * (∑ x, q x • D x) -
      (∑ x, q x • (D x * X * D x))‖ ≤ 3 * k * ‖X‖ := by
  have hBn : ‖∑ x, q x • D x‖ ≤ k := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ hk hB0).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using hB
  have hPsi := matrix_weighted_conjugate_norm_le q hq D hD hk hS hX
  calc
    _ ≤ ‖(∑ x, q x • D x) * X + X * (∑ x, q x • D x)‖ +
        ‖∑ x, q x • (D x * X * D x)‖ := norm_sub_le _ _
    _ ≤ (‖(∑ x, q x • D x) * X‖ + ‖X * (∑ x, q x • D x)‖) +
        ‖∑ x, q x • (D x * X * D x)‖ := add_le_add_right (norm_add_le _ _) _
    _ ≤ (‖∑ x, q x • D x‖ * ‖X‖ + ‖X‖ * ‖∑ x, q x • D x‖) +
        ‖∑ x, q x • (D x * X * D x)‖ :=
      add_le_add_right (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)) _
    _ ≤ (k * ‖X‖ + ‖X‖ * k) + k * ‖X‖ :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hBn (norm_nonneg X))
        (mul_le_mul_of_nonneg_left hBn (norm_nonneg X))) hPsi
    _ = 3 * k * ‖X‖ := by ring

end Paper22
