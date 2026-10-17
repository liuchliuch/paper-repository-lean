import Paper38.HilbertCoordinates
import Paper38.MobilityEllipticity
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The genuine Stein mobility on the intrinsic Euclidean--Frobenius tangent
space. Inversion below is inversion of the actual Sylvester differential. -/

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.Frobenius InnerProductSpace

namespace Paper38.HilbertMobility


variable {d : ℕ}

set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 80000

/-- A continuous linear extension of the inverse coordinate identification.
On symmetric raw coordinates it is exactly `Paper38.HilbertCoordinates.ofModel`; the projection only
provides a globally defined linear map for the calculus statements. -/
def encode (d : ℕ) : Paper38.Model.Coordinates d →L[ℝ] Paper38.HilbertCoordinates.Tangent d :=
  (Paper38.HilbertCoordinates.tangentSubmodule d).orthogonalProjection.comp (Paper38.HilbertCoordinates.ambientEquiv d).toContinuousLinearMap

@[simp] theorem encode_toModel (w : Paper38.HilbertCoordinates.Tangent d) : encode d (Paper38.HilbertCoordinates.toModel d w) = w := by
  change (Paper38.HilbertCoordinates.tangentSubmodule d).orthogonalProjection
    (Paper38.HilbertCoordinates.ambientEquiv d (Paper38.HilbertCoordinates.toModel d w)) = w
  rw [Paper38.HilbertCoordinates.ambient_toModel, Submodule.orthogonalProjection_mem_subspace_eq_self]

theorem encode_symmetric (r : Paper38.Model.Coordinates d) (hr : r.2ᵀ = r.2) :
    encode d r = Paper38.HilbertCoordinates.ofModel r hr := by
  calc
    encode d r = encode d (Paper38.HilbertCoordinates.toModel d
        (Paper38.HilbertCoordinates.ofModel r hr)) :=
      congrArg (encode d) (Paper38.HilbertCoordinates.toModel_ofModel r hr).symm
    _ = _ := encode_toModel _

@[simp] theorem toModel_encode (r : Paper38.Model.Coordinates d) (hr : r.2ᵀ = r.2) :
    Paper38.HilbertCoordinates.toModel d (encode d r) = r := by
  rw [encode_symmetric r hr, Paper38.HilbertCoordinates.toModel_ofModel]

/-- The source Sylvester differential in raw coordinates. -/
def rawJ (A : Paper38.Model.Mat d) : Paper38.Model.Coordinates d →L[ℝ] Paper38.Model.Coordinates d :=
  (ContinuousLinearMap.id ℝ (Paper38.Model.E d)).prodMap
    (Paper38.MobilityEllipticity.sylvesterLinearMap A).toContinuousLinearMap

@[simp] theorem rawJ_apply (A : Paper38.Model.Mat d) (w : Paper38.Model.Coordinates d) :
    rawJ A w = (w.1, Paper38.MobilityEllipticity.sylvester A w.2) := rfl

private theorem sylvester_symmetric (A H : Paper38.Model.Mat d) (hA : Aᵀ = A) (hH : Hᵀ = H) :
    (Paper38.MobilityEllipticity.sylvester A H)ᵀ = Paper38.MobilityEllipticity.sylvester A H := by
  simp [Paper38.MobilityEllipticity.sylvester, Matrix.transpose_add, Matrix.transpose_mul, hA, hH, add_comm]

/-- The raw source mobility (4.3) as a real linear map. -/
def rawMLinear (μ : Paper38.Model.E d) (S : Paper38.Model.Mat d) :
    Paper38.Model.Coordinates d →ₗ[ℝ] Paper38.Model.Coordinates d where
  toFun w := (Paper38.Model.vec d (Paper38.Mobility.mobilityMean (WithLp.ofLp μ) S (WithLp.ofLp w.1) w.2),
    Paper38.Mobility.mobilityCov (WithLp.ofLp μ) S (WithLp.ofLp w.1) w.2)
  map_add' w z := by
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin d) ℝ).injective
      simpa only [Paper38.Model.vec, WithLp.ofLp_toLp, WithLp.ofLp_add] using
        Paper38.Mobility.mobilityMean_add (WithLp.ofLp μ) S (WithLp.ofLp w.1) (WithLp.ofLp z.1) w.2 z.2
    · simpa only [WithLp.ofLp_add] using
        Paper38.Mobility.mobilityCov_add (WithLp.ofLp μ) S (WithLp.ofLp w.1) (WithLp.ofLp z.1) w.2 z.2
  map_smul' c w := by
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin d) ℝ).injective
      simpa only [Paper38.Model.vec, WithLp.ofLp_toLp, WithLp.ofLp_smul, RingHom.id_apply] using
        Paper38.Mobility.mobilityMean_smul (WithLp.ofLp μ) S c (WithLp.ofLp w.1) w.2
    · simpa only [WithLp.ofLp_smul, RingHom.id_apply] using
        Paper38.Mobility.mobilityCov_smul (WithLp.ofLp μ) S c (WithLp.ofLp w.1) w.2

def rawM (μ : Paper38.Model.E d) (S : Paper38.Model.Mat d) :
    Paper38.Model.Coordinates d →L[ℝ] Paper38.Model.Coordinates d := (rawMLinear μ S).toContinuousLinearMap

@[simp] theorem rawM_apply (μ : Paper38.Model.E d) (S : Paper38.Model.Mat d) (w : Paper38.Model.Coordinates d) :
    rawM μ S w =
      (Paper38.Model.vec d (Paper38.Mobility.mobilityMean (WithLp.ofLp μ) S (WithLp.ofLp w.1) w.2),
        Paper38.Mobility.mobilityCov (WithLp.ofLp μ) S (WithLp.ofLp w.1) w.2) := rfl

/-- The actual differential J(u,H)=(u,AH+HA) on E×Sym. -/
def J (q : Paper38.HilbertCoordinates.Tangent d) : Paper38.HilbertCoordinates.Tangent d →L[ℝ] Paper38.HilbertCoordinates.Tangent d :=
  (encode d).comp ((rawJ (Paper38.HilbertCoordinates.matrixProjection d q)).comp (Paper38.HilbertCoordinates.toModel d))

/-- The actual covariance-coordinate Stein mobility at (μ,A²), on E×Sym. -/
def mobility (q : Paper38.HilbertCoordinates.Tangent d) : Paper38.HilbertCoordinates.Tangent d →L[ℝ] Paper38.HilbertCoordinates.Tangent d :=
  (encode d).comp ((rawM (Paper38.HilbertCoordinates.meanProjection d q)
    (Paper38.HilbertCoordinates.matrixProjection d q * Paper38.HilbertCoordinates.matrixProjection d q)).comp (Paper38.HilbertCoordinates.toModel d))

@[simp] theorem toModel_J (q w : Paper38.HilbertCoordinates.Tangent d) :
    Paper38.HilbertCoordinates.toModel d (J q w) =
      ((Paper38.HilbertCoordinates.toModel d w).1, Paper38.MobilityEllipticity.sylvester (Paper38.HilbertCoordinates.matrixProjection d q) (Paper38.HilbertCoordinates.toModel d w).2) := by
  change Paper38.HilbertCoordinates.toModel d (encode d
    ((Paper38.HilbertCoordinates.toModel d w).1,
      Paper38.MobilityEllipticity.sylvester (Paper38.HilbertCoordinates.matrixProjection d q)
        (Paper38.HilbertCoordinates.toModel d w).2)) = _
  exact toModel_encode _ (sylvester_symmetric _ _
    (Paper38.HilbertCoordinates.toModel_symmetric q) (Paper38.HilbertCoordinates.toModel_symmetric w))

@[simp] theorem toModel_mobility (q w : Paper38.HilbertCoordinates.Tangent d) :
    Paper38.HilbertCoordinates.toModel d (mobility q w) =
      rawM (Paper38.HilbertCoordinates.meanProjection d q) (Paper38.HilbertCoordinates.matrixProjection d q * Paper38.HilbertCoordinates.matrixProjection d q)
        (Paper38.HilbertCoordinates.toModel d w) := by
  change Paper38.HilbertCoordinates.toModel d (encode d _) = _
  apply toModel_encode
  exact Paper38.Mobility.mobilityCov_symmetric _ _ _ _
    (by
      change (((Paper38.HilbertCoordinates.toModel d q).2 *
        (Paper38.HilbertCoordinates.toModel d q).2)ᵀ = _)
      rw [Matrix.transpose_mul, Paper38.HilbertCoordinates.toModel_symmetric q]
      rfl)
    (Paper38.HilbertCoordinates.toModel_symmetric w)

/-- The constructed actual inverse in raw coordinates. -/
def rawJEquiv (A : Paper38.Model.Mat d) (hA : A.PosDef) :
    Paper38.Model.Coordinates d ≃L[ℝ] Paper38.Model.Coordinates d :=
  ((LinearEquiv.refl ℝ (Paper38.Model.E d)).prodCongr (Paper38.MobilityEllipticity.sylvesterEquiv A hA)).toContinuousLinearEquiv

def inverseJOn (q : Paper38.HilbertCoordinates.Tangent d) (hq : q ∈ Paper38.HilbertCoordinates.Domain d) :
    Paper38.HilbertCoordinates.Tangent d →L[ℝ] Paper38.HilbertCoordinates.Tangent d :=
  (encode d).comp (((rawJEquiv (Paper38.HilbertCoordinates.matrixProjection d q) hq).symm.toContinuousLinearMap).comp
    (Paper38.HilbertCoordinates.toModel d))

@[simp] theorem toModel_inverseJOn (q w : Paper38.HilbertCoordinates.Tangent d) (hq : q ∈ Paper38.HilbertCoordinates.Domain d) :
    Paper38.HilbertCoordinates.toModel d (inverseJOn q hq w) =
      ((Paper38.HilbertCoordinates.toModel d w).1,
        Paper38.MobilityEllipticity.inverseSylvester (Paper38.HilbertCoordinates.matrixProjection d q) hq (Paper38.HilbertCoordinates.toModel d w).2) := by
  change Paper38.HilbertCoordinates.toModel d (encode d
    ((Paper38.HilbertCoordinates.toModel d w).1,
      Paper38.MobilityEllipticity.inverseSylvester (Paper38.HilbertCoordinates.matrixProjection d q)
        hq (Paper38.HilbertCoordinates.toModel d w).2)) = _
  exact toModel_encode _ (Paper38.MobilityEllipticity.inverseSylvester_symmetric _ hq _
    (Paper38.HilbertCoordinates.toModel_symmetric w))

theorem inverseJOn_J (q w : Paper38.HilbertCoordinates.Tangent d) (hq : q ∈ Paper38.HilbertCoordinates.Domain d) :
    inverseJOn q hq (J q w) = w := by
  apply Paper38.HilbertCoordinates.toModel_injective d
  simp only [toModel_inverseJOn, toModel_J, Paper38.MobilityEllipticity.inverse_sylvester]

theorem J_inverseJOn (q w : Paper38.HilbertCoordinates.Tangent d) (hq : q ∈ Paper38.HilbertCoordinates.Domain d) :
    J q (inverseJOn q hq w) = w := by
  apply Paper38.HilbertCoordinates.toModel_injective d
  simp only [toModel_inverseJOn, toModel_J, Paper38.MobilityEllipticity.sylvester_inverse]

def JEquiv (q : Paper38.HilbertCoordinates.Tangent d) (hq : q ∈ Paper38.HilbertCoordinates.Domain d) : Paper38.HilbertCoordinates.Tangent d ≃L[ℝ] Paper38.HilbertCoordinates.Tangent d :=
  ContinuousLinearEquiv.equivOfInverse (J q) (inverseJOn q hq)
    (fun w => inverseJOn_J q w hq) (fun w => J_inverseJOn q w hq)

/-- The total continuous-linear-map inverse, agreeing with the constructed
Sylvester inverse throughout the source domain. -/
def inverseJ (q : Paper38.HilbertCoordinates.Tangent d) : Paper38.HilbertCoordinates.Tangent d →L[ℝ] Paper38.HilbertCoordinates.Tangent d := (J q).inverse

theorem inverseJ_eq (q : Paper38.HilbertCoordinates.Tangent d) (hq : q ∈ Paper38.HilbertCoordinates.Domain d) :
    inverseJ q = inverseJOn q hq := by
  change (JEquiv q hq : Paper38.HilbertCoordinates.Tangent d →L[ℝ] Paper38.HilbertCoordinates.Tangent d).inverse = _
  rw [ContinuousLinearMap.inverse_equiv]
  rfl

/-- The actual pulled-back Stein mobility P=J⁻¹ M J⁻ᵀ. J and its inverse are
self-adjoint, as proved below, so the transpose inverse is the same operator. -/
def P (q : Paper38.HilbertCoordinates.Tangent d) : Paper38.HilbertCoordinates.Tangent d →L[ℝ] Paper38.HilbertCoordinates.Tangent d :=
  (inverseJ q).comp ((mobility q).comp (inverseJ q))

theorem J_self_adjoint (q u v : Paper38.HilbertCoordinates.Tangent d) :
    ⟪u, J q v⟫_ℝ = ⟪J q u, v⟫_ℝ := by
  simp only [Paper38.HilbertCoordinates.inner_toModel, toModel_J,
    Paper38.HilbertCoordinates.matrixInner_eq_frobenius]
  congr 1
  exact Paper38.MobilityEllipticity.sylvester_self_adjoint
    (Paper38.HilbertCoordinates.matrixProjection d q) _ _
    (Paper38.HilbertCoordinates.toModel_symmetric q)

theorem inverseJ_J (q w : Paper38.HilbertCoordinates.Tangent d)
    (hq : q ∈ Paper38.HilbertCoordinates.Domain d) : inverseJ q (J q w) = w := by
  rw [inverseJ_eq q hq]
  exact inverseJOn_J q w hq

theorem J_inverseJ (q w : Paper38.HilbertCoordinates.Tangent d)
    (hq : q ∈ Paper38.HilbertCoordinates.Domain d) : J q (inverseJ q w) = w := by
  rw [inverseJ_eq q hq]
  exact J_inverseJOn q w hq

theorem inverseJ_self_adjoint (q u v : Paper38.HilbertCoordinates.Tangent d)
    (hq : q ∈ Paper38.HilbertCoordinates.Domain d) :
    ⟪u, inverseJ q v⟫_ℝ = ⟪inverseJ q u, v⟫_ℝ := by
  have h := J_self_adjoint q (inverseJ q u) (inverseJ q v)
  rw [J_inverseJ q v hq, J_inverseJ q u hq] at h
  exact h.symm

theorem mobility_symmetric (q u v : Paper38.HilbertCoordinates.Tangent d) :
    ⟪u, mobility q v⟫_ℝ = ⟪v, mobility q u⟫_ℝ := by
  rw [Paper38.HilbertCoordinates.inner_eq_mobility_pairing,
    Paper38.HilbertCoordinates.inner_eq_mobility_pairing, toModel_mobility, toModel_mobility]
  simp only [rawM_apply, Paper38.Model.vec, WithLp.ofLp_toLp]
  apply Paper38.Mobility.self_adjoint
  · change (((Paper38.HilbertCoordinates.toModel d q).2 *
        (Paper38.HilbertCoordinates.toModel d q).2)ᵀ = _)
    rw [Matrix.transpose_mul, Paper38.HilbertCoordinates.toModel_symmetric q]
    rfl
  · exact Paper38.HilbertCoordinates.toModel_symmetric u
  · exact Paper38.HilbertCoordinates.toModel_symmetric v

theorem P_symmetric (q u v : Paper38.HilbertCoordinates.Tangent d)
    (hq : q ∈ Paper38.HilbertCoordinates.Domain d) : ⟪u, P q v⟫_ℝ = ⟪v, P q u⟫_ℝ := by
  simp only [P, ContinuousLinearMap.comp_apply]
  rw [inverseJ_self_adjoint q u _ hq, inverseJ_self_adjoint q v _ hq]
  exact mobility_symmetric q _ _

private theorem covariance_posDef (q : Paper38.HilbertCoordinates.Tangent d)
    (hq : q ∈ Paper38.HilbertCoordinates.Domain d) :
    (Paper38.HilbertCoordinates.matrixProjection d q *
      Paper38.HilbertCoordinates.matrixProjection d q).PosDef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self
    (Paper38.HilbertCoordinates.matrixProjection d q)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  change (((Paper38.HilbertCoordinates.toModel d q).2)ᵀ *
    (Paper38.HilbertCoordinates.toModel d q).2).PosSemidef at h
  rw [Paper38.HilbertCoordinates.toModel_symmetric q] at h
  exact h.posDef_iff_isUnit.mpr (hq.isUnit.mul hq.isUnit)

private theorem decoded_nonzero (w : Paper38.HilbertCoordinates.Tangent d) (hw : w ≠ 0) :
    WithLp.ofLp (Paper38.HilbertCoordinates.toModel d w).1 ≠ 0 ∨
      (Paper38.HilbertCoordinates.toModel d w).2 ≠ 0 := by
  by_contra h
  push_neg at h
  apply hw
  apply Paper38.HilbertCoordinates.toModel_injective d
  rw [map_zero]
  apply Prod.ext
  · apply (EuclideanSpace.equiv (Fin d) ℝ).injective
    simpa using h.1
  · exact h.2

theorem mobility_quadratic_pos (q w : Paper38.HilbertCoordinates.Tangent d)
    (hq : q ∈ Paper38.HilbertCoordinates.Domain d) (hw : w ≠ 0) :
    0 < ⟪w, mobility q w⟫_ℝ := by
  rw [Paper38.HilbertCoordinates.inner_eq_mobility_pairing, toModel_mobility]
  simp only [rawM_apply, Paper38.Model.vec, WithLp.ofLp_toLp]
  exact Paper38.Mobility.quadratic_pos _ _ _ _ (covariance_posDef q hq)
    (Paper38.HilbertCoordinates.toModel_symmetric w) (decoded_nonzero w hw)

theorem P_quadratic_pos (q w : Paper38.HilbertCoordinates.Tangent d)
    (hq : q ∈ Paper38.HilbertCoordinates.Domain d) (hw : w ≠ 0) : 0 < ⟪w, P q w⟫_ℝ := by
  have hinv : inverseJ q w ≠ 0 := by
    intro h
    apply hw
    rw [← J_inverseJ q w hq, h, map_zero]
  simpa only [P, ContinuousLinearMap.comp_apply,
    inverseJ_self_adjoint q w _ hq] using mobility_quadratic_pos q (inverseJ q w) hq hinv

theorem P_quadratic_nonneg (q w : Paper38.HilbertCoordinates.Tangent d)
    (hq : q ∈ Paper38.HilbertCoordinates.Domain d) : 0 ≤ ⟪w, P q w⟫_ℝ := by
  by_cases hw : w = 0
  · simp [hw]
  · exact (P_quadratic_pos q w hq hw).le

/-- Matrix-vector action as a bounded bilinear map in the actual Euclidean norm. -/
def matrixAction (d : ℕ) : Paper38.Model.Mat d →L[ℝ]
    Paper38.Model.E d →L[ℝ] Paper38.Model.E d :=
  (((LinearMap.toContinuousLinearMap : (Paper38.Model.E d →ₗ[ℝ] Paper38.Model.E d) ≃ₗ[ℝ]
    (Paper38.Model.E d →L[ℝ] Paper38.Model.E d)).toLinearMap).comp
    (Matrix.toEuclideanLin : Paper38.Model.Mat d ≃ₗ[ℝ]
      (Paper38.Model.E d →ₗ[ℝ] Paper38.Model.E d)).toLinearMap).toContinuousLinearMap

@[simp] theorem matrixAction_apply (A : Paper38.Model.Mat d) (v : Paper38.Model.E d) :
    matrixAction d A v = Paper38.Model.matVec A v := rfl

/-- Fixing either factor of the ordinary outer product gives a continuous linear map. -/
def outerLeft (a : Paper38.Model.E d) : Paper38.Model.E d →L[ℝ] Paper38.Model.Mat d :=
  ((vecMulVecBilin ℝ ℝ (WithLp.ofLp a)).comp
    (EuclideanSpace.equiv (Fin d) ℝ).toLinearMap).toContinuousLinearMap

def outerRight (a : Paper38.Model.E d) : Paper38.Model.E d →L[ℝ] Paper38.Model.Mat d :=
  (((vecMulVecBilin ℝ ℝ).flip (WithLp.ofLp a)).comp
    (EuclideanSpace.equiv (Fin d) ℝ).toLinearMap).toContinuousLinearMap

@[simp] theorem outerLeft_apply (a v : Paper38.Model.E d) :
    outerLeft a v = Matrix.vecMulVec (WithLp.ofLp a) (WithLp.ofLp v) := rfl

@[simp] theorem outerRight_apply (a v : Paper38.Model.E d) :
    outerRight a v = Matrix.vecMulVec (WithLp.ofLp v) (WithLp.ofLp a) := rfl

theorem rawM_formula (μ : Paper38.Model.E d) (S : Paper38.Model.Mat d)
    (w : Paper38.Model.Coordinates d) : rawM μ S w =
    ((2 : ℝ) • matrixAction d (w.2 * S) μ + (1 + ⟪μ, μ⟫_ℝ) • w.1,
      S * ((2 : ℝ) • (S * w.2) + outerRight w.1 μ) +
        ((2 : ℝ) • (w.2 * S) + outerLeft w.1 μ) * S) := by
  apply Prod.ext
  · apply (EuclideanSpace.equiv (Fin d) ℝ).injective
    change Paper38.Mobility.mobilityMean (WithLp.ofLp μ) S (WithLp.ofLp w.1) w.2 =
      WithLp.ofLp ((2 : ℝ) • matrixAction d (w.2 * S) μ + (1 + ⟪μ, μ⟫_ℝ) • w.1)
    simp only [Paper38.Mobility.mobilityMean, matrixAction_apply, Paper38.Model.matVec,
      Paper38.Model.vec, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_toLp,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  · rfl

/-- J is a polynomial family of actual tangent operators. -/
theorem J_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n (J (d := d)) := by
  apply contDiff_clm_apply_iff.mpr
  intro w
  change ContDiff ℝ n (fun q => encode d
    ((Paper38.HilbertCoordinates.toModel d w).1,
      Paper38.MobilityEllipticity.sylvester (Paper38.HilbertCoordinates.matrixProjection d q)
        (Paper38.HilbertCoordinates.toModel d w).2))
  apply (encode d).contDiff.comp
  apply ContDiff.prodMk contDiff_const
  unfold Paper38.MobilityEllipticity.sylvester
  exact ((Paper38.HilbertCoordinates.matrixProjection d).contDiff.mul contDiff_const).add
    (contDiff_const.mul (Paper38.HilbertCoordinates.matrixProjection d).contDiff)

/-- The true covariance-coordinate mobility is polynomial in the source state. -/
theorem mobility_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n (mobility (d := d)) := by
  apply contDiff_clm_apply_iff.mpr
  intro w
  change ContDiff ℝ n (fun q => encode d
    (rawM (Paper38.HilbertCoordinates.meanProjection d q)
      (Paper38.HilbertCoordinates.matrixProjection d q * Paper38.HilbertCoordinates.matrixProjection d q)
      (Paper38.HilbertCoordinates.toModel d w)))
  simp only [rawM_formula]
  apply (encode d).contDiff.comp
  apply ContDiff.prodMk
  · have hμ : ContDiff ℝ n (fun q : Paper38.HilbertCoordinates.Tangent d =>
        Paper38.HilbertCoordinates.meanProjection d q) :=
      (Paper38.HilbertCoordinates.meanProjection d).contDiff
    have hA : ContDiff ℝ n (fun q : Paper38.HilbertCoordinates.Tangent d =>
        Paper38.HilbertCoordinates.matrixProjection d q) :=
      (Paper38.HilbertCoordinates.matrixProjection d).contDiff
    exact (((matrixAction d).contDiff.comp (contDiff_const.mul (hA.mul hA))).clm_apply hμ).const_smul
      (2 : ℝ) |>.add ((contDiff_const.add (hμ.inner ℝ hμ)).smul contDiff_const)
  · have hμ := (Paper38.HilbertCoordinates.meanProjection d).contDiff (n := n)
    have hA := (Paper38.HilbertCoordinates.matrixProjection d).contDiff (n := n)
    have hS := hA.mul hA
    exact (hS.mul (((hS.mul contDiff_const).const_smul (2 : ℝ)).add
      ((outerRight (Paper38.HilbertCoordinates.toModel d w).1).contDiff.comp hμ))).add
      ((((contDiff_const.mul hS).const_smul (2 : ℝ)).add
        ((outerLeft (Paper38.HilbertCoordinates.toModel d w).1).contDiff.comp hμ)).mul hS)

/-- The actual inverse is smooth at each positive-definite source state. -/
theorem inverseJ_contDiffAt (n : WithTop ℕ∞) (q : Paper38.HilbertCoordinates.Tangent d)
    (hq : q ∈ Paper38.HilbertCoordinates.Domain d) : ContDiffAt ℝ n (inverseJ (d := d)) q := by
  have h := (contDiffAt_map_inverse (𝕜 := ℝ) (n := n) (JEquiv q hq)).comp q
    (J_contDiff (d := d) n).contDiffAt
  exact h

/-- Arbitrary-order smoothness of the true P on the intrinsic SPD domain. -/
theorem P_contDiffAt (n : WithTop ℕ∞) (q : Paper38.HilbertCoordinates.Tangent d)
    (hq : q ∈ Paper38.HilbertCoordinates.Domain d) : ContDiffAt ℝ n (P (d := d)) q :=
  (inverseJ_contDiffAt n q hq).clm_comp
    ((mobility_contDiff (d := d) n).contDiffAt.clm_comp (inverseJ_contDiffAt n q hq))

theorem P_contDiffOn (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (P (d := d)) (Paper38.HilbertCoordinates.Domain d) :=
  fun q hq => (P_contDiffAt n q hq).contDiffWithinAt

end Paper38.HilbertMobility
