import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.Tactic.NormNum

/-! Deterministic empirical covariance and its exact affine-rank endpoint (P38, Proposition 7.3).
The covariance uses the paper's normalization `1/N`, with no regularization. -/

noncomputable section
open scoped BigOperators Matrix Pointwise
open AffineSubspace

namespace Paper38.Empirical

variable {N d : ℕ}

/-- Arithmetic sample mean of the actual Euclidean point cloud. -/
def mean (x : Fin N → Fin d → ℝ) : Fin d → ℝ :=
  (N : ℝ)⁻¹ • ∑ i, x i

/-- Centered point cloud. -/
def centered (x : Fin N → Fin d → ℝ) (i : Fin N) : Fin d → ℝ := x i - mean x

/-- Matrix whose columns are the centered particles. -/
def centeredMatrix (x : Fin N → Fin d → ℝ) : Matrix (Fin d) (Fin N) ℝ :=
  fun j i => centered x i j

/-- Centered empirical covariance with the biased (`1/N`) normalization of the paper. -/
def covariance (x : Fin N → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (N : ℝ)⁻¹ • (centeredMatrix x * (centeredMatrix x)ᵀ)

lemma covariance_apply (x : Fin N → Fin d → ℝ) (j k : Fin d) :
    covariance x j k = (N : ℝ)⁻¹ * ∑ i, (x i j - mean x j) * (x i k - mean x k) := by
  simp [covariance, centeredMatrix, centered, Matrix.mul_apply, Matrix.transpose_apply]

lemma sum_centered (hN : 0 < N) (x : Fin N → Fin d → ℝ) :
    ∑ i, centered x i = 0 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [centered, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, mean]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hNr, one_smul, sub_self]

lemma mean_mem_affineSpan (hN : 0 < N) (x : Fin N → Fin d → ℝ) :
    mean x ∈ affineSpan ℝ (Set.range x) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hw : ∑ _i : Fin N, (N : ℝ)⁻¹ = 1 := by simp [hNr]
  have hm := affineCombination_mem_affineSpan (s := Finset.univ) hw x
  simpa [Finset.affineCombination_eq_linear_combination _ _ _ hw, mean,
    Finset.smul_sum] using hm

lemma span_centered_eq_vectorSpan (hN : 0 < N) (x : Fin N → Fin d → ℝ) :
    Submodule.span ℝ (Set.range (centered x)) = vectorSpan ℝ (Set.range x) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
      (mem_affineSpan ℝ (Set.mem_range_self i)) (mean_mem_affineSpan hN x)
  · let i₀ : Fin N := ⟨0, hN⟩
    rw [vectorSpan_range_eq_span_range_vsub_right ℝ x i₀]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have hi := Submodule.sub_mem (Submodule.span ℝ (Set.range (centered x)))
      (Submodule.subset_span (Set.mem_range_self i))
      (Submodule.subset_span (Set.mem_range_self i₀))
    convert hi using 1
    simp [centered, vsub_eq_sub, sub_sub_sub_cancel_right]

lemma rank_smul_of_ne_zero {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) {c : ℝ} (hc : c ≠ 0) : (c • A).rank = A.rank := by
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  have hset : Set.range (c • A).col = c • Set.range A.col := by
    ext v
    simp only [Set.mem_range, Set.mem_smul_set]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨A.col i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hset, Submodule.span_smul_eq_of_isUnit _ _ (isUnit_iff_ne_zero.mpr hc)]

/-- The covariance rank is exactly the affine dimension of the cloud. -/
theorem rank_covariance (hN : 0 < N) (x : Fin N → Fin d → ℝ) :
    (covariance x).rank = Module.finrank ℝ (vectorSpan ℝ (Set.range x)) := by
  rw [covariance, rank_smul_of_ne_zero _ (inv_ne_zero (by exact_mod_cast hN.ne')),
    Matrix.rank_self_mul_transpose, Matrix.rank_eq_finrank_span_cols]
  change Module.finrank ℝ (Submodule.span ℝ (Set.range (centered x))) = _
  rw [span_centered_eq_vectorSpan hN]

/-- Every nonempty `N`-point covariance has rank at most `N-1`. -/
theorem rank_covariance_le (hN : 0 < N) (x : Fin N → Fin d → ℝ) :
    (covariance x).rank ≤ N - 1 := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [rank_covariance hN]
  have h := finrank_vectorSpan_range_add_one_le ℝ x
  simp only [Fintype.card_fin] at h
  omega

/-- The algebraic rank bound also includes the empty-cloud convention `N = 0`. -/
theorem rank_covariance_le_all (x : Fin N → Fin d → ℝ) :
    (covariance x).rank ≤ N - 1 := by
  cases N with
  | zero => simp [covariance]
  | succ n => exact rank_covariance_le (Nat.succ_pos n) x

lemma covariance_posSemidef (x : Fin N → Fin d → ℝ) :
    (covariance x).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (centeredMatrix x)
  have ht : (centeredMatrix x)ᴴ = (centeredMatrix x)ᵀ := by simp
  rw [ht] at h
  exact h.smul (inv_nonneg.mpr (Nat.cast_nonneg N))

lemma posSemidef_posDef_iff_rank {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosSemidef) : A.PosDef ↔ A.rank = d := by
  rw [hA.posDef_iff_isUnit]
  constructor
  · intro h
    simpa using Matrix.rank_of_isUnit A h
  · intro h
    apply Matrix.mulVec_surjective_iff_isUnit.mp
    change Function.Surjective A.mulVecLin
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using h

/-- Positive definiteness is equivalent to affine spanning of the actual cloud. -/
theorem covariance_posDef_iff_affineSpan (hN : 0 < N) (x : Fin N → Fin d → ℝ) :
    (covariance x).PosDef ↔ affineSpan ℝ (Set.range x) = ⊤ := by
  rw [posSemidef_posDef_iff_rank (covariance_posSemidef x), rank_covariance hN]
  rw [affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ (Fin d → ℝ)
    (Fin d → ℝ) (by exact ⟨x ⟨0, hN⟩, Set.mem_range_self _⟩)]
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    simpa using h
  · intro h
    rw [h, finrank_top, Module.finrank_fin_fun]

/-- Necessary sample-count endpoint of the unregularized dynamics. -/
theorem dimension_add_one_le_of_posDef (hN : 0 < N) (x : Fin N → Fin d → ℝ)
    (h : (covariance x).PosDef) : d + 1 ≤ N := by
  have hr : (covariance x).rank = d :=
    (posSemidef_posDef_iff_rank (covariance_posSemidef x)).mp h
  have hb := rank_covariance_le hN x
  omega

/-- At the minimal sample count, positivity is exactly affine independence. -/
theorem covariance_posDef_iff_affineIndependent
    (x : Fin (d + 1) → Fin d → ℝ) :
    (covariance x).PosDef ↔ AffineIndependent ℝ x := by
  rw [posSemidef_posDef_iff_rank (covariance_posSemidef x),
    rank_covariance (Nat.succ_pos d)]
  exact (affineIndependent_iff_finrank_vectorSpan_eq ℝ x (Fintype.card_fin _)).symm

/-- An affine map carries sample means to the affine image of the mean. -/
theorem mean_affine (hN : 0 < N) (x : Fin N → Fin d → ℝ)
    (b : Fin d → ℝ) (L : Matrix (Fin d) (Fin d) ℝ) :
    mean (fun i => b + L *ᵥ x i) = b + L *ᵥ mean x := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [mean, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Matrix.mulVec_sum, smul_add, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ hNr, one_smul, Matrix.mulVec_smul]

/-- Centering commutes with the linear part of an affine map. -/
theorem centered_affine (hN : 0 < N) (x : Fin N → Fin d → ℝ)
    (b : Fin d → ℝ) (L : Matrix (Fin d) (Fin d) ℝ) (i : Fin N) :
    centered (fun i => b + L *ᵥ x i) i = L *ᵥ centered x i := by
  rw [centered, mean_affine hN]
  simp [centered, Matrix.mulVec_sub]

/-- Exact congruence transformation of the empirical covariance (Eq. 6.3 algebra). -/
theorem covariance_affine (hN : 0 < N) (x : Fin N → Fin d → ℝ)
    (b : Fin d → ℝ) (L : Matrix (Fin d) (Fin d) ℝ) :
    covariance (fun i => b + L *ᵥ x i) = L * covariance x * Lᵀ := by
  have hY : centeredMatrix (fun i => b + L *ᵥ x i) = L * centeredMatrix x := by
    ext j i
    exact congrFun (centered_affine hN x b L i) j
  simp only [covariance, hY, Matrix.transpose_mul, Matrix.mul_assoc,
    Matrix.mul_smul, Matrix.smul_mul]

/-- The affine lift of Eq. 6.2 has exactly the prescribed mean. -/
theorem mean_affine_lift (hN : 0 < N) (x : Fin N → Fin d → ℝ)
    (b : Fin d → ℝ) (L : Matrix (Fin d) (Fin d) ℝ) :
    mean (fun i => b + L *ᵥ centered x i) = b := by
  rw [mean_affine hN]
  have hm : mean (centered x) = 0 := by
    simp [mean, sum_centered hN]
  simp [hm]

/-- Exact covariance of the centered affine lift in Eq. 6.2. -/
theorem covariance_affine_lift (hN : 0 < N) (x : Fin N → Fin d → ℝ)
    (b : Fin d → ℝ) (L : Matrix (Fin d) (Fin d) ℝ) :
    covariance (fun i => b + L *ᵥ centered x i) = L * covariance x * Lᵀ := by
  have hc : covariance (centered x) = covariance x := by
    have hm : mean (centered x) = 0 := by simp [mean, sum_centered hN]
    have hY : centeredMatrix (centered x) = centeredMatrix x := by
      ext j i
      simp [centeredMatrix, centered, hm]
    simp only [covariance, hY]
  rw [covariance_affine hN, hc]

/-- Every invertible affine lift preserves strict positive definiteness. -/
theorem covariance_affine_lift_posDef (hN : 0 < N) (x : Fin N → Fin d → ℝ)
    (b : Fin d → ℝ) (L : Matrix (Fin d) (Fin d) ℝ)
    (hS : (covariance x).PosDef) (hL : IsUnit L) :
    (covariance (fun i => b + L *ᵥ centered x i)).PosDef := by
  rw [covariance_affine_lift hN]
  simpa using hS.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hL)

end Paper38.Empirical
