import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FunProp

/-!
# The log-determinant geometry in Lemmas 4.1 and 4.2

The determinant derivative is obtained from its actual continuous multilinear
row map.  The resulting row-replacement sum is identified with the adjugate
trace by Cramer's rule, before composition with the real logarithm.
-/

noncomputable section

namespace Paper38.LogDetGeometry

open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

variable {n : Type*} [Fintype n] [DecidableEq n]
abbrev Mat (n : Type*) := Matrix n n ℝ

/-- The determinant as a continuous multilinear function of the rows. -/
def determinantMultilinear : ContinuousMultilinearMap ℝ (fun _ : n => n → ℝ) ℝ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

@[simp] theorem determinantMultilinear_apply (A : Mat n) :
    determinantMultilinear A = A.det := rfl

/-- The differential of the genuine determinant, before identifying its trace formula. -/
def determinantDifferential (A : Mat n) : Mat n →L[ℝ] ℝ :=
  determinantMultilinear.linearDeriv A

theorem determinant_hasFDerivAt (A : Mat n) :
    HasFDerivAt Matrix.det (determinantDifferential A) A :=
  (determinantMultilinear (n := n)).hasFDerivAt A

theorem determinantDifferential_apply (A H : Mat n) :
    determinantDifferential A H = Matrix.trace (A.adjugate * H) := by
  change (determinantMultilinear (n := n)).linearDeriv A H = _
  rw [show (determinantMultilinear (n := n)).linearDeriv A H =
      ∑ i, determinantMultilinear (Function.update A i (H i)) from
    (determinantMultilinear (n := n)).linearDeriv_apply A H]
  have hrow (i : n) :
      determinantMultilinear (Function.update A i (H i)) =
        ∑ j, A.adjugate j i * H i j := by
    change (A.updateRow i (H i)).det = _
    rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
      ← Matrix.adjugate_transpose]
    rfl
  simp_rw [hrow]
  change (∑ i, ∑ j, A.adjugate j i * H i j) =
    ∑ j, ∑ i, A.adjugate j i * H i j
  exact Finset.sum_comm

/-- The entropy contribution in square-root covariance coordinates. -/
def negLogDet (A : Mat n) : ℝ := -Real.log A.det

def negLogDetDifferential (A : Mat n) : Mat n →L[ℝ] ℝ :=
  -((A.det)⁻¹ • determinantDifferential A)

theorem negLogDet_hasFDerivAt {A : Mat n} (hA : A.det ≠ 0) :
    HasFDerivAt negLogDet (negLogDetDifferential A) A := by
  simpa only [negLogDet, negLogDetDifferential] using
    ((determinant_hasFDerivAt A).log hA).neg

theorem negLogDetDifferential_apply (A H : Mat n) :
    negLogDetDifferential A H = -Matrix.trace (A⁻¹ * H) := by
  simp only [negLogDetDifferential, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, determinantDifferential_apply]
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mul, Matrix.trace_smul]

theorem negLogDet_fderiv_apply_of_det_ne_zero {A : Mat n} (hA : A.det ≠ 0) (H : Mat n) :
    fderiv ℝ negLogDet A H = -Matrix.trace (A⁻¹ * H) := by
  rw [(negLogDet_hasFDerivAt hA).fderiv]
  exact negLogDetDifferential_apply A H

/-- The actual Fréchet differential, with no gradient formula assumed. -/
theorem negLogDet_fderiv_apply {A : Mat n} (hA : A.PosDef) (H : Mat n) :
    fderiv ℝ negLogDet A H = -Matrix.trace (A⁻¹ * H) :=
  negLogDet_fderiv_apply_of_det_ne_zero hA.det_pos.ne' H

/-- The directional derivative at any nonsingular point of an affine matrix line. -/
theorem negLogDet_affine_hasDerivAt (A H : Mat n) (t : ℝ)
    (hA : (A + t • H).det ≠ 0) :
    HasDerivAt (fun s : ℝ => negLogDet (A + s • H))
      (-Matrix.trace ((A + t • H)⁻¹ * H)) t := by
  have hline : HasDerivAt (fun s : ℝ => A + s • H) H t := by
    convert (hasDerivAt_const t A).add ((hasDerivAt_id t).smul_const H) using 1
    simp only [zero_add, one_smul]
  convert (negLogDet_hasFDerivAt hA).comp_hasDerivAt t hline using 1
  exact (negLogDetDifferential_apply (A + t • H) H).symm

/-- The directional derivative along an affine matrix line at the base point. -/
theorem negLogDet_line_hasDerivAt {A : Mat n} (hA : A.det ≠ 0)
    (H : Mat n) :
    HasDerivAt (fun t : ℝ => negLogDet (A + t • H))
      (-Matrix.trace (A⁻¹ * H)) 0 := by
  simpa only [zero_smul, add_zero] using
    negLogDet_affine_hasDerivAt A H 0 (by simpa using hA)

/-- Arbitrary finite-order regularity follows from the actual determinant polynomial. -/
theorem negLogDet_contDiffAt {k : WithTop ℕ∞} {A : Mat n} (hA : A.det ≠ 0) :
    ContDiffAt ℝ k negLogDet A := by
  have hdet : ContDiff ℝ k (Matrix.det : Mat n → ℝ) := by
    classical
    have hentry (i j : n) : ContDiff ℝ k (fun A : Mat n => A i j) := by
      let L : Mat n →ₗ[ℝ] ℝ :=
        { toFun := fun A => A i j
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      exact L.toContinuousLinearMap.contDiff
    change ContDiff ℝ k (fun A : Mat n => A.det)
    simp only [Matrix.det_apply']
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hentry (σ i) i)
  exact (hdet.contDiffAt.log hA).neg

theorem negLogDet_contDiffOn {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (negLogDet : Mat n → ℝ) {A | A.det ≠ 0} :=
  fun _ hA => (negLogDet_contDiffAt hA).contDiffWithinAt

theorem negLogDet_contDiffOn_posDef {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (negLogDet : Mat n → ℝ) {A | A.PosDef} :=
  fun _ hA => (negLogDet_contDiffAt hA.det_pos.ne').contDiffWithinAt

section OperatorNorm

open scoped Matrix.Norms.Operator

local instance : IsScalarTower ℝ (Mat n) (Mat n) :=
  Matrix.Semiring.isScalarTower

local instance : SMulCommClass ℝ (Mat n) (Mat n) :=
  Matrix.Semiring.smulCommClass

private def traceRightLinear (H : Mat n) : Mat n →ₗ[ℝ] ℝ where
  toFun B := Matrix.trace (B * H)
  map_add' B C := by simp [Matrix.add_mul, Matrix.trace_add]
  map_smul' c B := by simp [Matrix.trace_smul]

private def traceRightCLM (H : Mat n) : Mat n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (traceRightLinear H)

/-- The genuine matrix inverse derivative at an invertible matrix. -/
theorem matrixInverse_hasFDerivAt {A : Mat n} (hA : IsUnit A) :
    HasFDerivAt (fun B : Mat n => B⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Mat n) A⁻¹ A⁻¹) A := by
  have h : HasFDerivAt (Ring.inverse : Mat n → Mat n)
      (-ContinuousLinearMap.mulLeftRight ℝ (Mat n) A⁻¹ A⁻¹) A := by
    simpa only [Matrix.coe_units_inv, hA.unit_spec] using
      (hasFDerivAt_ringInverse (𝕜 := ℝ) hA.unit)
  exact h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun B => Matrix.nonsing_inv_eq_ringInverse (A := B))

/-- Differentiation of the first log-determinant variation along a matrix line. -/
theorem inverseTrace_line_hasDerivAt {A : Mat n} (hA : A.det ≠ 0) (H : Mat n) :
    HasDerivAt (fun t : ℝ => -Matrix.trace ((A + t • H)⁻¹ * H))
      (Matrix.trace (A⁻¹ * H * A⁻¹ * H)) 0 := by
  have hunit : IsUnit A := A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hA)
  have hline : HasDerivAt (fun t : ℝ => A + t • H) H 0 := by
    convert (hasDerivAt_const (0 : ℝ) A).add ((hasDerivAt_id (0 : ℝ)).smul_const H) using 1
    simp only [zero_add, one_smul]
  have hi : HasDerivAt (fun t : ℝ => (A + t • H)⁻¹)
      (-(A⁻¹ * H * A⁻¹)) 0 := by
    simpa only [Function.comp_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.mulLeftRight_apply] using
      (matrixInverse_hasFDerivAt hunit).comp_hasDerivAt_of_eq 0 hline (by simp)
  have htrace : HasFDerivAt (fun B : Mat n => -Matrix.trace (B * H))
      (-(traceRightCLM H)) A⁻¹ := (traceRightCLM H).hasFDerivAt.neg
  simpa only [Function.comp_apply, ContinuousLinearMap.neg_apply,
    traceRightCLM, LinearMap.coe_toContinuousLinearMap', traceRightLinear,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.neg_mul, Matrix.trace_neg, neg_neg] using
    htrace.comp_hasDerivAt_of_eq 0 hi (by simp)

/-- The second derivative is a derivative of the actual first derivative,
not a separately supplied Hessian expression. -/
theorem negLogDet_second_hasDerivAt {A : Mat n} (hA : A.det ≠ 0) (H : Mat n) :
    HasDerivAt (deriv (fun t : ℝ => negLogDet (A + t • H)))
      (Matrix.trace (A⁻¹ * H * A⁻¹ * H)) 0 := by
  have hcont : Continuous (fun t : ℝ => (A + t • H).det) := by fun_prop
  have hne : ∀ᶠ t in nhds (0 : ℝ), (A + t • H).det ≠ 0 :=
    hcont.continuousAt.eventually_ne (by simpa using hA)
  apply (inverseTrace_line_hasDerivAt hA H).congr_of_eventuallyEq
  filter_upwards [hne] with t ht
  exact (negLogDet_affine_hasDerivAt A H t ht).deriv

/-- The second directional variation of −log det. -/
theorem negLogDet_second_variation {A : Mat n} (hA : A.PosDef) (H : Mat n) :
    deriv (deriv (fun t : ℝ => negLogDet (A + t • H))) 0 =
      Matrix.trace (A⁻¹ * H * A⁻¹ * H) :=
  (negLogDet_second_hasDerivAt hA.det_pos.ne' H).deriv

end OperatorNorm

/-- The same second variation in ambient, iterated Fréchet-derivative notation. -/
theorem negLogDet_fderiv_second_of_det_ne_zero {A : Mat n}
    (hA : A.det ≠ 0) (H : Mat n) :
    fderiv ℝ (fderiv ℝ negLogDet) A H H = Matrix.trace (A⁻¹ * H * A⁻¹ * H) := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (negLogDet : Mat n → ℝ)) A :=
    ((negLogDet_contDiffAt (k := 2) hA).fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  have hline : HasDerivAt (fun t : ℝ => A + t • H) H 0 := by
    convert (hasDerivAt_const (0 : ℝ) A).add ((hasDerivAt_id (0 : ℝ)).smul_const H) using 1
    simp only [zero_add, one_smul]
  have hc := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hd : HasDerivAt (fun t : ℝ => fderiv ℝ negLogDet (A + t • H) H)
      (fderiv ℝ (fderiv ℝ negLogDet) A H H) 0 := by
    simpa only [Function.comp_apply, map_zero, add_zero] using
      hc.clm_apply (hasDerivAt_const (0 : ℝ) H)
  have hcont : Continuous (fun t : ℝ => (A + t • H).det) := by fun_prop
  have hne : ∀ᶠ t in nhds (0 : ℝ), (A + t • H).det ≠ 0 :=
    hcont.continuousAt.eventually_ne (by simpa using hA)
  have heq : deriv (fun t : ℝ => negLogDet (A + t • H)) =ᶠ[nhds (0 : ℝ)]
      (fun t : ℝ => fderiv ℝ negLogDet (A + t • H) H) := by
    filter_upwards [hne] with t ht
    rw [(negLogDet_affine_hasDerivAt A H t ht).deriv]
    exact (negLogDet_fderiv_apply_of_det_ne_zero ht H).symm
  exact (hd.congr_of_eventuallyEq heq).unique (negLogDet_second_hasDerivAt hA H)

theorem negLogDet_fderiv_second {A : Mat n} (hA : A.PosDef) (H : Mat n) :
    fderiv ℝ (fderiv ℝ negLogDet) A H H = Matrix.trace (A⁻¹ * H * A⁻¹ * H) :=
  negLogDet_fderiv_second_of_det_ne_zero hA.det_pos.ne' H


section Positivity

open scoped MatrixOrder

omit [DecidableEq n] in
private theorem trace_transpose_mul_nonneg (X : Mat n) :
    0 ≤ Matrix.trace (Xᵀ * X) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

/-- The source trace term is a Frobenius square, hence nonnegative, on symmetric directions. -/
theorem second_variation_trace_square {A H : Mat n} (hA : A.PosDef) (hH : Hᵀ = H) :
    Matrix.trace (A⁻¹ * H * A⁻¹ * H) =
      Matrix.trace ((CFC.sqrt A⁻¹ * H * CFC.sqrt A⁻¹)ᵀ *
        (CFC.sqrt A⁻¹ * H * CFC.sqrt A⁻¹)) := by
  let R := CFC.sqrt A⁻¹
  have hR : R.PosDef := hA.inv.posDef_sqrt
  have hRs : Rᵀ = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  have hR2 : R * R = A⁻¹ := CFC.sqrt_mul_sqrt_self A⁻¹ hA.inv.posSemidef.nonneg
  have hX : (R * H * R)ᵀ = R * H * R := by
    simp only [Matrix.transpose_mul, hRs, hH]
    exact (Matrix.mul_assoc R H R).symm
  change Matrix.trace (A⁻¹ * H * A⁻¹ * H) = Matrix.trace ((R * H * R)ᵀ * (R * H * R))
  rw [hX]
  calc
    Matrix.trace (A⁻¹ * H * A⁻¹ * H) = Matrix.trace ((R * R) * H * (R * R) * H) := by rw [hR2]
    _ = Matrix.trace (R * (R * H * R * R * H)) := by congr 1; noncomm_ring
    _ = Matrix.trace ((R * H * R * R * H) * R) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((R * H * R) * (R * H * R)) := by congr 1; noncomm_ring

/-- The nonnegative log-determinant contribution in equation (4.7). -/
theorem second_variation_nonneg {A H : Mat n} (hA : A.PosDef) (hH : Hᵀ = H) :
    0 ≤ Matrix.trace (A⁻¹ * H * A⁻¹ * H) := by
  rw [second_variation_trace_square hA hH]
  exact trace_transpose_mul_nonneg _

theorem negLogDet_second_variation_nonneg {A H : Mat n}
    (hA : A.PosDef) (hH : Hᵀ = H) :
    0 ≤ deriv (deriv (fun t : ℝ => negLogDet (A + t • H))) 0 := by
  rw [negLogDet_second_variation hA H]
  exact second_variation_nonneg hA hH

theorem negLogDet_fderiv_second_nonneg {A H : Mat n}
    (hA : A.PosDef) (hH : Hᵀ = H) :
    0 ≤ fderiv ℝ (fderiv ℝ negLogDet) A H H := by
  rw [negLogDet_fderiv_second hA H]
  exact second_variation_nonneg hA hH

end Positivity

end Paper38.LogDetGeometry
