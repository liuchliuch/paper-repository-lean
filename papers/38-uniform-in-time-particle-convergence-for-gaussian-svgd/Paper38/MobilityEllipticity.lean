import Paper38.Mobility
import Mathlib.Tactic.Positivity

/-!
# Quantitative lower bounds for the Stein mobility

This file proves the matrix inequalities used in Proposition 4.3. Bounds on
matrices are expressed as genuine pointwise Euclidean singular-value bounds.
No ellipticity statement for the mobility is assumed.
-/

namespace Paper38.MobilityEllipticity

open Matrix
open Paper38.Mobility

variable {d : Type*} [Fintype d] [DecidableEq d]

set_option linter.unusedSectionVars false

/-- The Frobenius square is the sum of the Euclidean squares of the rows. -/
theorem frobenius_rows (B : Mat d) :
    frobenius B B = ∑ i, B i ⬝ᵥ B i := by
  simp only [frobenius_self_eq_sum, dotProduct, pow_two]

/-- Transposition preserves the ordinary Frobenius square. -/
theorem frobenius_transpose_self (B : Mat d) :
    frobenius Bᵀ Bᵀ = frobenius B B := by
  simp only [frobenius_self_eq_sum, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- The Frobenius square of an outer product factors into the two vector squares. -/
theorem frobenius_outer (a μ : Vec d) :
    frobenius (Matrix.vecMulVec a μ) (Matrix.vecMulVec a μ) =
      (a ⬝ᵥ a) * (μ ⬝ᵥ μ) := by
  rw [frobenius_vecMulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul]
  ring

/-- The elementary squared triangle bound, with its exact constant two. -/
theorem frobenius_add_bound (U V : Mat d) :
    frobenius (U + V) (U + V) ≤ 2 * frobenius U U + 2 * frobenius V V := by
  simp only [frobenius_self_eq_sum, Matrix.add_apply]
  calc
    ∑ i, ∑ j, (U i j + V i j) ^ 2 ≤
        ∑ i, ∑ j, (2 * (U i j) ^ 2 + 2 * (V i j) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      nlinarith [sq_nonneg (U i j - V i j)]
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- A shifted version of the squared triangle bound. -/
theorem frobenius_shift_bound (U V : Mat d) :
    frobenius U U ≤ 2 * frobenius (U + V) (U + V) + 2 * frobenius V V := by
  simp only [frobenius_self_eq_sum, Matrix.add_apply]
  calc
    ∑ i, ∑ j, (U i j) ^ 2 ≤
        ∑ i, ∑ j, (2 * (U i j + V i j) ^ 2 + 2 * (V i j) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      nlinarith [sq_nonneg (U i j + 2 * V i j)]
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The first inequality in the proof of Proposition 4.3, source Ex8. -/
theorem shifted_feature_bound (μ a : Vec d) (U : Mat d) :
    frobenius U U + a ⬝ᵥ a ≤
      2 * (1 + μ ⬝ᵥ μ) *
        (frobenius (U + Matrix.vecMulVec a μ) (U + Matrix.vecMulVec a μ) + a ⬝ᵥ a) := by
  have h := frobenius_shift_bound U (Matrix.vecMulVec a μ)
  rw [frobenius_outer] at h
  have ha := vector_self_nonneg a
  have hμ := vector_self_nonneg μ
  have hF := frobenius_self_nonneg (U + Matrix.vecMulVec a μ)
  nlinarith [mul_nonneg hμ hF]

private theorem row_mul_eq_mulVec (S B : Mat d) (hS : Sᵀ = S) (i : d) :
    (B * S) i = S *ᵥ B i := by
  ext j
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : S k j = S j k := congrFun (congrFun hS j) k
  rw [hkj]
  ring

/-- A pointwise lower singular bound implies the corresponding Frobenius bound
for right multiplication. This is derived row by row, rather than assumed. -/
theorem frobenius_mul_lower (S B : Mat d) (s : ℝ) (hS : Sᵀ = S)
    (hSingular : ∀ v : Vec d, s ^ 2 * (v ⬝ᵥ v) ≤ (S *ᵥ v) ⬝ᵥ (S *ᵥ v)) :
    s ^ 2 * frobenius B B ≤ frobenius (B * S) (B * S) := by
  rw [frobenius_rows, frobenius_rows, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [row_mul_eq_mulVec S B hS i]
  exact hSingular (B i)

/-- The matching upper Frobenius bound for right multiplication. -/
theorem frobenius_mul_upper (A B : Mat d) (b : ℝ) (hA : Aᵀ = A)
    (hSingular : ∀ v : Vec d, (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ b ^ 2 * (v ⬝ᵥ v)) :
    frobenius (B * A) (B * A) ≤ b ^ 2 * frobenius B B := by
  rw [frobenius_rows, frobenius_rows, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [row_mul_eq_mulVec A B hA i]
  exact hSingular (B i)

/-- The upper Frobenius bound for left multiplication, derived by transposition. -/
theorem frobenius_mul_upper_left (A B : Mat d) (b : ℝ) (hA : Aᵀ = A)
    (hSingular : ∀ v : Vec d, (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ b ^ 2 * (v ⬝ᵥ v)) :
    frobenius (A * B) (A * B) ≤ b ^ 2 * frobenius B B := by
  calc
    frobenius (A * B) (A * B) = frobenius (A * B)ᵀ (A * B)ᵀ :=
      (frobenius_transpose_self _).symm
    _ = frobenius (Bᵀ * A) (Bᵀ * A) := by rw [Matrix.transpose_mul, hA]
    _ ≤ b ^ 2 * frobenius Bᵀ Bᵀ := frobenius_mul_upper A Bᵀ b hA hSingular
    _ = b ^ 2 * frobenius B B := by rw [frobenius_transpose_self]

/-- The second inequality in the proof of Proposition 4.3, source Ex9. -/
theorem scaled_covariance_bound (S B : Mat d) (a : Vec d) (s : ℝ) (hS : Sᵀ = S)
    (hSingular : ∀ v : Vec d, s ^ 2 * (v ⬝ᵥ v) ≤ (S *ᵥ v) ⬝ᵥ (S *ᵥ v)) :
    min 1 (4 * s ^ 2) * (frobenius B B + a ⬝ᵥ a) ≤
      frobenius ((2 : ℝ) • (B * S)) ((2 : ℝ) • (B * S)) + a ⬝ᵥ a := by
  have h := frobenius_mul_lower S B s hS hSingular
  have hB := frobenius_self_nonneg B
  have ha := vector_self_nonneg a
  have hm4 : min (1 : ℝ) (4 * s ^ 2) ≤ 4 * s ^ 2 := min_le_right _ _
  have hm1 : min (1 : ℝ) (4 * s ^ 2) ≤ 1 := min_le_left _ _
  have hleft := mul_le_mul_of_nonneg_right hm4 hB
  have hright := mul_le_mul_of_nonneg_right hm1 ha
  simp only [frobenius_smul_left, frobenius_smul_right]
  nlinarith

/-- The explicit covariance-coordinate mobility lower bound, source Ex10. -/
theorem mobility_lower_bound (μ a : Vec d) (S B : Mat d) (s : ℝ)
    (hS : Sᵀ = S) (hB : Bᵀ = B)
    (hSingular : ∀ v : Vec d, s ^ 2 * (v ⬝ᵥ v) ≤ (S *ᵥ v) ⬝ᵥ (S *ᵥ v)) :
    (min 1 (4 * s ^ 2) / (2 * (1 + μ ⬝ᵥ μ))) *
        (frobenius B B + a ⬝ᵥ a) ≤
      pairing a B (mobilityMean μ S a B) (mobilityCov μ S a B) := by
  have hlow := scaled_covariance_bound S B a s hS hSingular
  have hhigh := shifted_feature_bound μ a ((2 : ℝ) • (B * S))
  have hd : 0 < 2 * (1 + μ ⬝ᵥ μ) := by
    nlinarith [vector_self_nonneg μ]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  rw [quadratic_identity μ S a B hS hB]
  change min 1 (4 * s ^ 2) * (frobenius B B + a ⬝ᵥ a) ≤
    (frobenius (feature μ S a B) (feature μ S a B) + a ⬝ᵥ a) * (2 * (1 + μ ⬝ᵥ μ))
  exact (le_trans hlow hhigh).trans_eq (by unfold feature; ring)

/-- Positivity of the explicit covariance-coordinate ellipticity constant. -/
theorem mobility_constant_pos (μ : Vec d) (s : ℝ) (hs : 0 < s) :
    0 < min 1 (4 * s ^ 2) / (2 * (1 + μ ⬝ᵥ μ)) := by
  apply div_pos
  · exact lt_min zero_lt_one (by positivity)
  · nlinarith [vector_self_nonneg μ]

/-- The actual covariance differential in square-root coordinates (4.9). -/
def sylvester (A H : Mat d) : Mat d := A * H + H * A

/-- The actual product-space Jacobian (4.9). -/
def coordinateJacobian (A : Mat d) (u : Vec d) (H : Mat d) : Vec d × Mat d :=
  (u, sylvester A H)

/-- The Sylvester differential is self-adjoint for the ordinary Frobenius product. -/
theorem sylvester_self_adjoint (A H K : Mat d) (hA : Aᵀ = A) :
    frobenius H (sylvester A K) = frobenius (sylvester A H) K := by
  simp only [sylvester, frobenius_add_right, frobenius_add_left]
  rw [frobenius_mul_left, frobenius_mul_right, hA]

/-- The square of the Sylvester differential has the sharp elementary bound
used for the Jacobian norm in the proof of (4.12). -/
theorem sylvester_square_upper (A H : Mat d) (b : ℝ) (hA : Aᵀ = A)
    (hUpper : ∀ v : Vec d, (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ b ^ 2 * (v ⬝ᵥ v)) :
    frobenius (sylvester A H) (sylvester A H) ≤ 4 * b ^ 2 * frobenius H H := by
  have hadd := frobenius_add_bound (A * H) (H * A)
  have hl := frobenius_mul_upper_left A H b hA hUpper
  have hr := frobenius_mul_upper A H b hA hUpper
  change frobenius (A * H + H * A) (A * H + H * A) ≤ _
  linarith

/-- The ordinary squared product-norm estimate for J in (4.9):
`‖J(u,H)‖² ≤ max(1,4b²) ‖(u,H)‖²`. -/
theorem coordinateJacobian_square_upper (A H : Mat d) (u : Vec d) (b : ℝ)
    (hA : Aᵀ = A)
    (hUpper : ∀ v : Vec d, (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ b ^ 2 * (v ⬝ᵥ v)) :
    u ⬝ᵥ u + frobenius (sylvester A H) (sylvester A H) ≤
      max 1 (4 * b ^ 2) * (u ⬝ᵥ u + frobenius H H) := by
  have hJ := sylvester_square_upper A H b hA hUpper
  have hu := vector_self_nonneg u
  have hH := frobenius_self_nonneg H
  have hv := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (4 * b ^ 2)) hu
  have hM := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (4 * b ^ 2)) hH
  nlinarith

/-- A lower singular bound for A gives the corresponding bound for its actual
square covariance A*A. -/
theorem covariance_square_singular_lower (A : Mat d) (a : ℝ)
    (hLower : ∀ v : Vec d, a ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v)) :
    ∀ v : Vec d, (a ^ 2) ^ 2 * (v ⬝ᵥ v) ≤
      ((A * A) *ᵥ v) ⬝ᵥ ((A * A) *ᵥ v) := by
  intro v
  have hv := hLower v
  have hAv := hLower (A *ᵥ v)
  have hmul := mul_le_mul_of_nonneg_left hv (sq_nonneg a)
  rw [Matrix.mulVec_mulVec] at hAv
  nlinarith

/-- The Sylvester differential as an actual linear endomorphism. -/
def sylvesterLinearMap (A : Mat d) : Mat d →ₗ[ℝ] Mat d where
  toFun := sylvester A
  map_add' H K := by
    simp only [sylvester, Matrix.mul_add, Matrix.add_mul]
    ext i j
    simp only [Matrix.add_apply]
    ring
  map_smul' r H := by
    simp only [sylvester, Matrix.mul_smul, Matrix.smul_mul, smul_add, RingHom.id_apply]

private theorem frobenius_rows_bilinear (H K : Mat d) :
    frobenius H K = ∑ i, H i ⬝ᵥ K i := by
  simp only [Paper38.Mobility.frobenius, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, dotProduct]
  exact Finset.sum_comm

private theorem frobenius_transpose_bilinear (H K : Mat d) :
    frobenius H K = frobenius Hᵀ Kᵀ := by
  simpa only [Matrix.transpose_transpose] using frobenius_transpose_right H Kᵀ

private theorem frobenius_mul_nonneg (A H : Mat d) (hA : A.PosSemidef) :
    0 ≤ frobenius H (H * A) := by
  have hs : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  rw [frobenius_rows_bilinear]
  apply Finset.sum_nonneg
  intro i hi
  rw [row_mul_eq_mulVec A H hs i]
  simpa only [star_trivial] using hA.2 (H i)

private theorem frobenius_mul_left_nonneg (A H : Mat d) (hA : A.PosSemidef) :
    0 ≤ frobenius H (A * H) := by
  have hs : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  rw [frobenius_transpose_bilinear, Matrix.transpose_mul, hs]
  exact frobenius_mul_nonneg A Hᵀ hA

private theorem frobenius_mul_zero (A H : Mat d) (hA : A.PosDef)
    (hzero : frobenius H (H * A) = 0) : H = 0 := by
  have hs : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hrow (i : d) : 0 ≤ H i ⬝ᵥ (H * A) i := by
    rw [row_mul_eq_mulVec A H hs i]
    simpa only [star_trivial] using hA.posSemidef.2 (H i)
  rw [frobenius_rows_bilinear] at hzero
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hrow i)).mp hzero
  ext i j
  have hi : H i = 0 := by
    by_contra hne
    have hp : 0 < H i ⬝ᵥ (A *ᵥ H i) := by
      simpa only [star_trivial] using hA.2 (H i) hne
    have he := hz i (Finset.mem_univ i)
    rw [row_mul_eq_mulVec A H hs i] at he
    linarith
  exact congrFun hi j

/-- Positive definiteness of A implies injectivity of the actual Sylvester map. -/
theorem sylvesterLinearMap_injective (A : Mat d) (hA : A.PosDef) :
    Function.Injective (sylvesterLinearMap A) := by
  intro H K hHK
  have hzero : sylvester A (H - K) = 0 := by
    change sylvesterLinearMap A (H - K) = 0
    rw [map_sub, hHK, sub_self]
  have hpair := congrArg (fun L => frobenius (H - K) L) hzero
  change frobenius (H - K) (sylvester A (H - K)) = frobenius (H - K) 0 at hpair
  rw [sylvester, frobenius_add_right] at hpair
  have hleft := frobenius_mul_left_nonneg A (H - K) hA.posSemidef
  have hright := frobenius_mul_nonneg A (H - K) hA.posSemidef
  have hsum : frobenius (H - K) (A * (H - K)) +
      frobenius (H - K) ((H - K) * A) = 0 := by
    simpa [Paper38.Mobility.frobenius] using hpair
  have hz : frobenius (H - K) ((H - K) * A) = 0 := by linarith
  exact sub_eq_zero.mp (frobenius_mul_zero A (H - K) hA hz)

/-- The real Sylvester inverse is constructed from injectivity and finite dimension. -/
noncomputable def sylvesterEquiv (A : Mat d) (hA : A.PosDef) : Mat d ≃ₗ[ℝ] Mat d :=
  LinearEquiv.ofBijective (sylvesterLinearMap A)
    ⟨sylvesterLinearMap_injective A hA,
      LinearMap.surjective_of_injective (sylvesterLinearMap_injective A hA)⟩

/-- The actual inverse Sylvester map, not an arbitrary right inverse. -/
noncomputable def inverseSylvester (A : Mat d) (hA : A.PosDef) (K : Mat d) : Mat d :=
  (sylvesterEquiv A hA).symm K

@[simp] theorem sylvester_inverse (A : Mat d) (hA : A.PosDef) (K : Mat d) :
    sylvester A (inverseSylvester A hA K) = K :=
  (sylvesterEquiv A hA).apply_symm_apply K

@[simp] theorem inverse_sylvester (A : Mat d) (hA : A.PosDef) (H : Mat d) :
    inverseSylvester A hA (sylvester A H) = H :=
  (sylvesterEquiv A hA).symm_apply_apply H

/-- Transposition commutes with the Sylvester differential for symmetric A. -/
theorem sylvester_transpose (A H : Mat d) (hA : Aᵀ = A) :
    sylvester A Hᵀ = (sylvester A H)ᵀ := by
  simp [sylvester, Matrix.transpose_add, Matrix.transpose_mul, hA, add_comm]

/-- The constructed inverse maps symmetric matrices to symmetric matrices. -/
theorem inverseSylvester_symmetric (A : Mat d) (hA : A.PosDef) (K : Mat d)
    (hK : Kᵀ = K) : (inverseSylvester A hA K)ᵀ = inverseSylvester A hA K := by
  have hs : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  apply sylvesterLinearMap_injective A hA
  change sylvester A (inverseSylvester A hA K)ᵀ = sylvester A (inverseSylvester A hA K)
  rw [sylvester_transpose A _ hs, sylvester_inverse, hK]

/-- Self-adjointness of the actual inverse, derived from that of the Sylvester map. -/
theorem inverseSylvester_self_adjoint (A : Mat d) (hA : A.PosDef) (H K : Mat d) :
    frobenius H (inverseSylvester A hA K) = frobenius (inverseSylvester A hA H) K := by
  have hs : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have h := sylvester_self_adjoint A (inverseSylvester A hA H) (inverseSylvester A hA K) hs
  rw [sylvester_inverse, sylvester_inverse] at h
  exact h.symm

/-- The explicit constant in source (4.12), before the compact-sublevel bounds
are supplied by the analytic part of Proposition 4.3. -/
noncomputable def sublevelConstant (a M b : ℝ) : ℝ :=
  min 1 (4 * a ^ 4) / (2 * (1 + M ^ 2) * max 1 (4 * b ^ 2))

theorem sublevelConstant_pos (a M b : ℝ) (ha : 0 < a) :
    0 < sublevelConstant a M b := by
  unfold sublevelConstant
  apply div_pos
  · exact lt_min zero_lt_one (by positivity)
  · apply mul_pos
    · nlinarith [sq_nonneg M]
    · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- Quantitative congruence lower bound with an actual Sylvester preimage.

When H is `J^{-T}(u,K)`'s matrix component, self-adjointness of J makes
`AH+HA=K`; this theorem is exactly the quadratic lower bound for
`J^{-1} M J^{-T}`. It derives the source constant from the true mobility and
pointwise singular bounds on A, and does not assume mobility ellipticity.
Existence and smoothness of the inverse Sylvester map are separate assertions. -/
theorem sylvester_preimage_ellipticity
    (μ u : Vec d) (A H K : Mat d) (a M b : ℝ)
    (hA : Aᵀ = A) (hH : Hᵀ = H)
    (hLower : ∀ v : Vec d, a ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v))
    (hUpper : ∀ v : Vec d, (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ b ^ 2 * (v ⬝ᵥ v))
    (hMean : μ ⬝ᵥ μ ≤ M ^ 2) (hPreimage : sylvester A H = K) :
    sublevelConstant a M b * (u ⬝ᵥ u + frobenius K K) ≤
      pairing u H (mobilityMean μ (A * A) u H) (mobilityCov μ (A * A) u H) := by
  have hS : (A * A)ᵀ = A * A := by simp [Matrix.transpose_mul, hA]
  have hSingular := covariance_square_singular_lower A a hLower
  have hlow := scaled_covariance_bound (A * A) H u (a ^ 2) hS hSingular
  have hhigh := shifted_feature_bound μ u ((2 : ℝ) • (H * (A * A)))
  have hQ := quadratic_nonneg μ (A * A) u H hS hH
  have hJ := coordinateJacobian_square_upper A H u b hA hUpper
  rw [hPreimage] at hJ
  have hNum : 0 ≤ min (1 : ℝ) (4 * a ^ 4) :=
    le_min zero_le_one (by positivity)
  have hMax : 0 ≤ max (1 : ℝ) (4 * b ^ 2) :=
    le_trans zero_le_one (le_max_left _ _)
  have hDen : 0 < 2 * (1 + M ^ 2) * max (1 : ℝ) (4 * b ^ 2) := by
    apply mul_pos
    · nlinarith [sq_nonneg M]
    · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hM : 2 * (1 + μ ⬝ᵥ μ) ≤ 2 * (1 + M ^ 2) := by linarith
  have hFeature :
      frobenius ((2 : ℝ) • (H * (A * A)) + Matrix.vecMulVec u μ)
        ((2 : ℝ) • (H * (A * A)) + Matrix.vecMulVec u μ) + u ⬝ᵥ u =
      pairing u H (mobilityMean μ (A * A) u H) (mobilityCov μ (A * A) u H) := by
    exact (quadratic_identity μ (A * A) u H hS hH).symm
  rw [hFeature] at hhigh
  have hMulMean := mul_le_mul_of_nonneg_right hM hQ
  have hBase : min (1 : ℝ) (4 * a ^ 4) * (frobenius H H + u ⬝ᵥ u) ≤
      2 * (1 + M ^ 2) *
        pairing u H (mobilityMean μ (A * A) u H) (mobilityCov μ (A * A) u H) := by
    have heq : (a ^ 2) ^ 2 = a ^ 4 := by ring
    rw [heq] at hlow
    exact le_trans (le_trans hlow hhigh) hMulMean
  have hPull := mul_le_mul_of_nonneg_left hJ hNum
  have hScaled := mul_le_mul_of_nonneg_left hBase hMax
  unfold sublevelConstant
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hDen).mpr
  nlinarith

/-- The vector component of the actual congruence P=J⁻¹ M J⁻ᵀ in (4.10). -/
noncomputable def pullbackMobilityMean (μ : Vec d) (A : Mat d) (hA : A.PosDef)
    (u : Vec d) (K : Mat d) : Vec d :=
  mobilityMean μ (A * A) u (inverseSylvester A hA K)

/-- The covariance-coordinate component of the actual congruence P=J⁻¹ M J⁻ᵀ.
The transpose inverse equals the constructed inverse because the true Sylvester
map and its inverse are self-adjoint for the ordinary Frobenius product. -/
noncomputable def pullbackMobilityCov (μ : Vec d) (A : Mat d) (hA : A.PosDef)
    (u : Vec d) (K : Mat d) : Mat d :=
  inverseSylvester A hA
    (mobilityCov μ (A * A) u (inverseSylvester A hA K))

/-- The usual quadratic-form identity for the genuine congruence. -/
theorem pullback_quadratic_identity (μ u : Vec d) (A K : Mat d) (hA : A.PosDef) :
    pairing u K (pullbackMobilityMean μ A hA u K) (pullbackMobilityCov μ A hA u K) =
      pairing u (inverseSylvester A hA K)
        (mobilityMean μ (A * A) u (inverseSylvester A hA K))
        (mobilityCov μ (A * A) u (inverseSylvester A hA K)) := by
  unfold pairing pullbackMobilityMean pullbackMobilityCov
  rw [inverseSylvester_self_adjoint]

/-- The exact quantitative ellipticity estimate (4.12) for the actual pulled-back
mobility. The hypotheses are genuine Euclidean bounds on A and μ; neither
mobility nor pulled-back mobility ellipticity is assumed. -/
theorem pullback_mobility_ellipticity (μ u : Vec d) (A K : Mat d) (hA : A.PosDef)
    (a M b : ℝ) (hK : Kᵀ = K)
    (hLower : ∀ v : Vec d, a ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v))
    (hUpper : ∀ v : Vec d, (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ b ^ 2 * (v ⬝ᵥ v))
    (hMean : μ ⬝ᵥ μ ≤ M ^ 2) :
    sublevelConstant a M b * (u ⬝ᵥ u + frobenius K K) ≤
      pairing u K (pullbackMobilityMean μ A hA u K) (pullbackMobilityCov μ A hA u K) := by
  have hs : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  rw [pullback_quadratic_identity]
  exact sylvester_preimage_ellipticity μ u A (inverseSylvester A hA K) K a M b hs
    (inverseSylvester_symmetric A hA K hK) hLower hUpper hMean
    (sylvester_inverse A hA K)

end Paper38.MobilityEllipticity
