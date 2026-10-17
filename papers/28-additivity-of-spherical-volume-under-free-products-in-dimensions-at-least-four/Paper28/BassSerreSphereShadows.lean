import Paper28.BassSerreFiniteHull
import Paper28.HilbertPartitionFold
import Paper28.SphericalQuotientMetricInput
import Paper28.GlobalAngularChordBound

/-! Actual branch shadows (7) on the native regular Hilbert sphere.
Their contraction in round distance and constancy outside an explicit
finite hull are native proofs; the Bass--Serre input supplies only the
standard coset-tree object. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {G : Type} [Group G] [DecidableEq G] [Countable G] {A B : Subgroup G}
  (T : BassSerreObject A B)

def bassSerreSphereShadowA (v : G ⧸ A) (u : RegularSphere G) : RegularSphere A :=
  ⟨hilbertPartitionFold (bassSerreBranchA T v) u.val,
    (hilbertPartitionFold_norm _ _).trans u.property⟩

def bassSerreSphereShadowB (v : G ⧸ B) (u : RegularSphere G) : RegularSphere B :=
  ⟨hilbertPartitionFold (bassSerreBranchB T v) u.val,
    (hilbertPartitionFold_norm _ _).trans u.property⟩

def bassSerreQuotientShadowA (v : G ⧸ A) (u : RegularSphere G) : RegularOrbitQuotient A :=
  regularQuotientMap (bassSerreSphereShadowA T v u)

def bassSerreQuotientShadowB (v : G ⧸ B) (u : RegularSphere G) : RegularOrbitQuotient B :=
  regularQuotientMap (bassSerreSphereShadowB T v u)

theorem bassSerreQuotientShadowA_round_contraction (MA : SphericalQuotientMetricInput A)
    (v : G ⧸ A) (u w : RegularSphere G) :
    @dist (RegularOrbitQuotient A) MA.metric.toDist
      (bassSerreQuotientShadowA T v u) (bassSerreQuotientShadowA T v w) ≤ angular u.val w.val := by
  have h := spherical_quotient_dist_le_angle MA (bassSerreSphereShadowA T v u) (bassSerreSphereShadowA T v w) 1
  rw [leftRegular_one] at h
  exact h.trans (hilbertPartitionFold_angular _ _ _)

theorem bassSerreQuotientShadowB_round_contraction (MB : SphericalQuotientMetricInput B)
    (v : G ⧸ B) (u w : RegularSphere G) :
    @dist (RegularOrbitQuotient B) MB.metric.toDist
      (bassSerreQuotientShadowB T v u) (bassSerreQuotientShadowB T v w) ≤ angular u.val w.val := by
  have h := spherical_quotient_dist_le_angle MB (bassSerreSphereShadowB T v u) (bassSerreSphereShadowB T v w) 1
  rw [leftRegular_one] at h
  exact h.trans (hilbertPartitionFold_angular _ _ _)

theorem bassSerreQuotientShadowA_lipschitz (MA : SphericalQuotientMetricInput A) (v : G ⧸ A) :
    letI := MA.metric
    LipschitzWith ⟨Real.pi/2,by positivity⟩ (bassSerreQuotientShadowA T v) := by
  letI := MA.metric
  apply LipschitzWith.of_dist_le_mul
  intro u w
  exact (bassSerreQuotientShadowA_round_contraction T MA v u w).trans
    (angular_le_pi_half_chord u.val w.val u.property w.property)

theorem bassSerreQuotientShadowB_lipschitz (MB : SphericalQuotientMetricInput B) (v : G ⧸ B) :
    letI := MB.metric
    LipschitzWith ⟨Real.pi/2,by positivity⟩ (bassSerreQuotientShadowB T v) := by
  letI := MB.metric
  apply LipschitzWith.of_dist_le_mul
  intro u w
  exact (bassSerreQuotientShadowB_round_contraction T MB v u w).trans
    (angular_le_pi_half_chord u.val w.val u.property w.property)

theorem bassSerreQuotientShadowA_outside_hull (F : Finset G) (v : G ⧸ A)
    (hv : Sum.inl v ∉ bassSerreHullVertices T F) :
    ∃ c : RegularOrbitQuotient A, ∀ u : RegularSphere G,
      u.val ∈ coordinateSupportSubspace F → bassSerreQuotientShadowA T v u = c := by
  obtain ⟨a,ha⟩ := bassSerreBranchA_outside_hull T F v hv
  let e : RegularSphere A := ⟨lp.single 2 a 1,by rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]; norm_num⟩
  refine ⟨regularQuotientMap e,?_⟩
  intro u hu
  apply congrArg regularQuotientMap
  apply Subtype.ext
  change hilbertPartitionFold (bassSerreBranchA T v) u.val = lp.single 2 a 1
  rw [hilbertPartitionFold_constant_on_support _ F a u.val hu ha,u.property]

theorem bassSerreQuotientShadowB_outside_hull (F : Finset G) (v : G ⧸ B)
    (hv : Sum.inr v ∉ bassSerreHullVertices T F) :
    ∃ c : RegularOrbitQuotient B, ∀ u : RegularSphere G,
      u.val ∈ coordinateSupportSubspace F → bassSerreQuotientShadowB T v u = c := by
  obtain ⟨b,hb⟩ := bassSerreBranchB_outside_hull T F v hv
  let e : RegularSphere B := ⟨lp.single 2 b 1,by rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]; norm_num⟩
  refine ⟨regularQuotientMap e,?_⟩
  intro u hu
  apply congrArg regularQuotientMap
  apply Subtype.ext
  change hilbertPartitionFold (bassSerreBranchB T v) u.val = lp.single 2 b 1
  rw [hilbertPartitionFold_constant_on_support _ F b u.val hu hb,u.property]

end Paper28
