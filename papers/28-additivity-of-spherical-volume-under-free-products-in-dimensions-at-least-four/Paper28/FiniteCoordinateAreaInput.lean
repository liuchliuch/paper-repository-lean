import Paper28.HilbertPartitionFold
import Paper28.FiniteCoordinateCurrentGroup
import Paper28.RectifiableCalculusInput
import Paper28.FiniteShadows
import Paper28.SphericalQuotientMetricInput
import Paper28.GlobalAngularChordBound
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Standard finite-dimensional AK representation and individual area
formula, with canonical coordinate inclusion and norm-partition
compatibility. The coordinate routing identity is an explicit hypothesis
and is checked natively for the actual Bass--Serre hull. This input has
no tree, joint Jacobian bound, transfer sum or mass-subadditivity claim.
It is a disclosed standard-calculus corollary, not a numbered theorem
asserting any result of this paper. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open MeasureTheory Set
open scoped Topology
variable {G : Type} [Group G] [DecidableEq G] [Countable G]

def partitionQuotientShadow {K : Type} [Group K] [DecidableEq K]
    (π : G → K) (u : RegularSphere G) : RegularOrbitQuotient K :=
  regularQuotientMap ⟨hilbertPartitionFold π u.val,(hilbertPartitionFold_norm _ _).trans u.property⟩

theorem partitionQuotientShadow_lipschitz {K : Type} [Group K] [DecidableEq K] [Countable K]
    (MK : SphericalQuotientMetricInput K) (π : G → K) :
    letI := MK.metric
    ∃ L : NNReal, LipschitzWith L (partitionQuotientShadow π) := by
  letI := MK.metric
  refine ⟨⟨Real.pi/2,by positivity⟩,LipschitzWith.of_dist_le_mul (fun u v => ?_)⟩
  have h := spherical_quotient_dist_le_angle MK
    ⟨hilbertPartitionFold π u.val,(hilbertPartitionFold_norm _ _).trans u.property⟩
    ⟨hilbertPartitionFold π v.val,(hilbertPartitionFold_norm _ _).trans v.property⟩ 1
  rw [leftRegular_one] at h
  exact (h.trans (hilbertPartitionFold_angular π u.val v.val)).trans
    (angular_le_pi_half_chord u.val v.val u.property v.property)

variable (J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance)
  {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι ↪ G) (n : ℕ) (C : J.Current n)

structure FiniteCoordinateAreaRepresentation where
  calculus : RectifiableSphereCalculusInput.{0,0} (EuclideanSpace ℝ ι)
  current : calculus.Current n
  finiteMass : IsFiniteMeasure (calculus.massMeasure current)
  mass_integral_one : (∫ _x, (1 : ℝ) ∂calculus.massMeasure current) = J.mass C
  jacobian_integrable : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (β : ι → κ),
    Integrable (currentJacobian calculus (finiteShadow β) current) (calculus.massMeasure current)
  individual_area : ∀ {κ K : Type} [Fintype κ] [DecidableEq κ]
    [Group K] [DecidableEq K] [Countable K]
    (MK : SphericalQuotientMetricInput K)
    (IK : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient K) MK.metric)
    (F : CanonicalGlobalCurrentCalculusInput) (π : G → K) (β : ι → κ) (d : κ ↪ K),
    (∀ i, π (s i) = d (β i)) →
    IK.mass ((letI := MK.metric
      F.map J IK (partitionQuotientShadow π) (partitionQuotientShadow_lipschitz MK π)).push n C) ≤
      ∫ x, currentJacobian calculus (finiteShadow β) current x ∂calculus.massMeasure current

/-- Canonical finite-coordinate pullback of an actual sphere current and
the generic individual AK area formula. No sum over maps or joint bound
is supplied; the representation is tied to the actual current mass. -/
structure FiniteCoordinateCurrentAreaInput where
  representation : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι ↪ G) (n : ℕ) (C : J.Current n),
    J.support C ⊆ regularCoordinateSphere (Finset.univ.image s) →
      Nonempty (FiniteCoordinateAreaRepresentation J s n C)

end Paper28
