import Paper38.HilbertMobility

/-!
# Explicit standard principal-matrix-square-root differential input

The sole external input below is the classical Fréchet differentiability of the
principal matrix square root on real symmetric positive definite matrices. Its
derivative sends H to the unique X satisfying sqrt(S) X + X sqrt(S) = H.
Here that unique inverse Sylvester operator has already been constructed and
proved invertible in MobilityEllipticity/HilbertMobility.

Source: Nicholas J. Higham, *Functions of Matrices: Theory and Computation*,
SIAM, 2008, Chapter 6 (matrix square roots), DOI 10.1137/1.9780898717778.ch6.
This is an explicit ordinary baseline theorem argument, authorized by the user.
It contains no source trajectory, energy, mobility, or convergence conclusion.
-/
noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.Frobenius

namespace Paper38.ExternalMatrixAnalysis
open Paper38.Model Paper38.HilbertCoordinates

/-- Actual principal covariance-root state in the intrinsic symmetric space. -/
def principalRoot {d : ℕ} (q : Tangent d) : Tangent d :=
  ofModel (meanProjection d q, CFC.sqrt (matrixProjection d q)) (by
    have hp : (CFC.sqrt (matrixProjection d q)).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hp.isHermitian.eq)

@[simp] theorem toModel_principalRoot {d : ℕ} (q : Tangent d) :
    toModel d (principalRoot q) = (meanProjection d q, CFC.sqrt (matrixProjection d q)) :=
  toModel_ofModel _ _

theorem principalRoot_mem_Domain {d : ℕ} (q : Tangent d) (hq : q ∈ Domain d) :
    principalRoot q ∈ Domain d := by
  change (toModel d (principalRoot q)).2.PosDef
  rw [toModel_principalRoot]
  exact hq.posDef_sqrt

/-- External classical principal matrix square-root differential, restricted to
the actual symmetric tangent space. The mean component has derivative identity;
the matrix component is the actual inverse Sylvester operator at sqrt(S). -/
def PrincipalRootDifferentiation (d : ℕ) : Prop :=
  ∀ (q : Tangent d), q ∈ Domain d →
    HasFDerivAt principalRoot (HilbertMobility.inverseJ (principalRoot q)) q

theorem principalRoot_hasFDerivAt {d : ℕ} (sqrt : PrincipalRootDifferentiation d)
    (q : Tangent d) (hq : q ∈ Domain d) :
    HasFDerivAt principalRoot (HilbertMobility.inverseJ (principalRoot q)) q := sqrt q hq

end Paper38.ExternalMatrixAnalysis
