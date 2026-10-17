import Paper28.NormFoldings
import Paper28.DeterminantBound
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! Actual Frechet differentials of the norm-folding maps off the zero
folded block. These are derived from mathlib calculus, without an external
input or a Jacobian assumption. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open WithLp
open scoped InnerProductSpace
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The derivative of the Hilbert norm at a nonzero vector. -/
def hilbertNormDerivative (u : K) : K →L[ℝ] ℝ :=
  (1 / ‖u‖) • innerSL ℝ u

theorem hasFDerivAt_hilbertNorm (u : K) (hu : u ≠ 0) :
    HasFDerivAt (fun x : K => ‖x‖) (hilbertNormDerivative u) u := by
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have h := (hasStrictFDerivAt_norm_sq u).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  convert h using 1
  · funext x
    exact (Real.sqrt_sq (norm_nonneg x)).symm
  · ext v
    simp [hilbertNormDerivative, Real.sqrt_sq (norm_nonneg u)]
    ring

def lpFst : WithLp 2 (H × K) →L[ℝ] H :=
  (ContinuousLinearMap.fst ℝ H K).comp
    (prodContinuousLinearEquiv 2 ℝ H K).toContinuousLinearMap

def lpSnd : WithLp 2 (H × K) →L[ℝ] K :=
  (ContinuousLinearMap.snd ℝ H K).comp
    (prodContinuousLinearEquiv 2 ℝ H K).toContinuousLinearMap

/-- The differential `(h,k) ↦ (h, <u.snd,k>/‖u.snd‖)`. -/
def normFoldDerivative (u : WithLp 2 (H × K)) :
    WithLp 2 (H × K) →L[ℝ] WithLp 2 (H × ℝ) :=
  (prodContinuousLinearEquiv 2 ℝ H ℝ).symm.toContinuousLinearMap.comp
    ((lpFst : WithLp 2 (H × K) →L[ℝ] H).prod
      ((hilbertNormDerivative u.snd).comp lpSnd))

theorem normFoldDerivative_apply (u h : WithLp 2 (H × K)) :
    normFoldDerivative u h = toLp 2 (h.fst, ⟪u.snd, h.snd⟫_ℝ / ‖u.snd‖) := by
  simp [normFoldDerivative, lpFst, lpSnd, hilbertNormDerivative, div_eq_mul_inv, mul_comm]

theorem hasFDerivAt_normFold (u : WithLp 2 (H × K)) (hu : u.snd ≠ 0) :
    HasFDerivAt normFold (normFoldDerivative u) u := by
  have hf := (lpFst : WithLp 2 (H × K) →L[ℝ] H).hasFDerivAt (x := u)
  have hg := (hasFDerivAt_hilbertNorm u.snd hu).comp u
    (lpSnd : WithLp 2 (H × K) →L[ℝ] K).hasFDerivAt
  exact (prodContinuousLinearEquiv 2 ℝ H ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp u
    (hf.prodMk hg)

/-- Directions perpendicular to the folded radial block are sent to the
orthogonal projection onto the retained block. -/
theorem normFoldDerivative_orthogonal (u h : WithLp 2 (H × K))
    (hh : ⟪u.snd, h.snd⟫_ℝ = 0) :
    normFoldDerivative u h = toLp 2 (h.fst, 0) := by
  rw [normFoldDerivative_apply, hh, zero_div]

/-- The actual Frechet derivative is a contraction, including every
nonradial direction, at every differentiability point in this domain. -/
theorem normFoldDerivative_norm_le (u h : WithLp 2 (H × K)) (hu : u.snd ≠ 0) :
    ‖normFoldDerivative u h‖ ≤ ‖h‖ := by
  have hn : 0 < ‖u.snd‖ := norm_pos_iff.mpr hu
  have hc := abs_real_inner_le_norm u.snd h.snd
  have hd : |⟪u.snd, h.snd⟫_ℝ / ‖u.snd‖| ≤ ‖h.snd‖ := by
    rw [abs_div, abs_of_pos hn]
    exact (div_le_iff₀ hn).mpr (by simpa [mul_comm] using hc)
  have hs : ‖normFoldDerivative u h‖ ^ 2 ≤ ‖h‖ ^ 2 := by
    rw [normFoldDerivative_apply]
    simp only [prod_norm_sq_eq_of_L2, toLp_fst, toLp_snd, Real.norm_eq_abs]
    nlinarith [abs_nonneg (⟪u.snd, h.snd⟫_ℝ / ‖u.snd‖), norm_nonneg h.snd]
  nlinarith [norm_nonneg (normFoldDerivative u h), norm_nonneg h]

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]

/-- Reordering the orthogonal blocks is an actual linear isometry. -/
def reverseTripleIsometry : Triple H₁ H₂ →ₗᵢ[ℝ] Triple H₂ H₁ where
  toFun := reverseTriple
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := reverseTriple_norm

/-- The Frechet derivative of the right folding, including reordering. -/
def rightFoldDerivative (u : Triple H₁ H₂) : Triple H₁ H₂ →L[ℝ] WithLp 2 (H₂ × ℝ) :=
  (normFoldDerivative (reverseTriple u)).comp reverseTripleIsometry.toContinuousLinearMap

theorem hasFDerivAt_leftFold (u : Triple H₁ H₂) (hu : u.snd ≠ 0) :
    HasFDerivAt leftFold (normFoldDerivative u) u := hasFDerivAt_normFold u hu

theorem hasFDerivAt_rightFold (u : Triple H₁ H₂) (hu : (reverseTriple u).snd ≠ 0) :
    HasFDerivAt rightFold (rightFoldDerivative u) u :=
  (hasFDerivAt_normFold (reverseTriple u) hu).comp u
    (reverseTripleIsometry (H₁ := H₁) (H₂ := H₂)).toContinuousLinearMap.hasFDerivAt

/-- On the common nonradial space inside the sphere tangent space, the
two actual differentials have complementary Gram forms. -/
theorem folding_differential_inner_add (u v w : Triple H₁ H₂)
    (htv : ⟪u, v⟫_ℝ = 0) (htw : ⟪u, w⟫_ℝ = 0)
    (hxv : ⟪u.fst, v.fst⟫_ℝ = 0) (hxw : ⟪u.fst, w.fst⟫_ℝ = 0)
    (hzv : v.snd.fst = 0) (hzw : w.snd.fst = 0) :
    ⟪normFoldDerivative u v, normFoldDerivative u w⟫_ℝ +
      ⟪rightFoldDerivative u v, rightFoldDerivative u w⟫_ℝ = ⟪v, w⟫_ℝ := by
  have hvL : ⟪u.snd, v.snd⟫_ℝ = 0 := by
    rw [prod_inner_apply] at htv
    simp only [ofLp_fst, ofLp_snd] at htv
    rw [hxv, zero_add] at htv
    exact htv
  have hwL : ⟪u.snd, w.snd⟫_ℝ = 0 := by
    rw [prod_inner_apply] at htw
    simp only [ofLp_fst, ofLp_snd] at htw
    rw [hxw, zero_add] at htw
    exact htw
  have hvR : ⟪(reverseTriple u).snd, (reverseTriple v).snd⟫_ℝ = 0 := by
    simp [reverseTriple, prod_inner_apply, hzv, hxv]
  have hwR : ⟪(reverseTriple u).snd, (reverseTriple w).snd⟫_ℝ = 0 := by
    simp [reverseTriple, prod_inner_apply, hzw, hxw]
  change ⟪normFoldDerivative u v, normFoldDerivative u w⟫_ℝ +
    ⟪normFoldDerivative (reverseTriple u) (reverseTriple v),
      normFoldDerivative (reverseTriple u) (reverseTriple w)⟫_ℝ = _
  rw [normFoldDerivative_orthogonal u v hvL, normFoldDerivative_orthogonal u w hwL,
    normFoldDerivative_orthogonal _ _ hvR, normFoldDerivative_orthogonal _ _ hwR]
  simp [reverseTriple, prod_inner_apply, hzv, hzw]

/-- The two-plane determinant estimate for the actual folding differentials,
with the tangency and common nonradial conditions written explicitly. -/
theorem folding_differential_two_area_le_one (u : Triple H₁ H₂)
    (e : Fin 2 → Triple H₁ H₂) (he : Orthonormal ℝ e)
    (ht : ∀ i, ⟪u, e i⟫_ℝ = 0)
    (hx : ∀ i, ⟪u.fst, (e i).fst⟫_ℝ = 0) (hz : ∀ i, (e i).snd.fst = 0) :
    Real.sqrt (Matrix.gram ℝ (fun i => normFoldDerivative u (e i))).det +
      Real.sqrt (Matrix.gram ℝ (fun i => rightFoldDerivative u (e i))).det ≤ 1 := by
  apply two_gram_det_bound _ _ (Matrix.posSemidef_gram _ _) (Matrix.posSemidef_gram _ _)
  ext i j
  change ⟪normFoldDerivative u (e i), normFoldDerivative u (e j)⟫_ℝ +
    ⟪rightFoldDerivative u (e i), rightFoldDerivative u (e j)⟫_ℝ = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j
  rw [folding_differential_inner_add u (e i) (e j) (ht i) (ht j) (hx i) (hx j) (hz i) (hz j)]
  exact (orthonormal_iff_ite.mp he) i j

end Paper28
