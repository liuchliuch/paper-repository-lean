import Paper27.Geometry.LeadingNormalTensor
import Paper27.Geometry.CommonComponents

/-!
# Third-fibration tangency using the intrinsic normal tensor isomorphism

This version retains arbitrary honest holomorphic normal frames and an actual
holomorphic gauge for the normal tensor isomorphism. It does not require
normal-coordinate nth roots on entire canonical curve chart domains. The
record is intermediate geometric output, not an external theorem.
-/
noncomputable section
namespace Paper27.Geometry
open NormalDegreeInvariance
variable {X : CompactComplexSurface}

structure ComponentNormalTensorData (D : EmbeddedCurve X) where
  normal : HolomorphicLineCocycle D.curve
  tangent : TangentLineCocycle D.curve
  exponent : ℕ
  exponent_ge_two : 2 ≤ exponent
  frames : EmbeddedFrames.RawEmbeddedFrames D normal tangent.bundle
  tensorGauge : HolomorphicLineGauge (normal.tensorPower exponent) tangent.bundle

namespace ComponentNormalTensorData

theorem degree_facts (theory : LineBundleDegreeTheory)
    (invariance : LineBundleDegreeGaugeInvariance theory) {D : EmbeddedCurve X}
    (A : ComponentNormalTensorData D) (hD : D.curve.Hyperbolic) :
    (A.exponent : ℤ) * theory.degree D.curve A.normal =
      theory.degree D.curve A.tangent.bundle ∧ theory.degree D.curve A.normal < 0 := by
  have hdegree : (A.exponent : ℤ) * theory.degree D.curve A.normal =
      theory.degree D.curve A.tangent.bundle := by
    rw [← theory.tensor_power D.curve A.normal A.exponent]
    exact invariance D.curve _ _ A.tensorGauge
  refine ⟨hdegree, ?_⟩
  have hg : (2 : ℤ) ≤ D.curve.genus := by exact_mod_cast hD
  have hnegative : (A.exponent : ℤ) * theory.degree D.curve A.normal < 0 := by
    rw [hdegree, theory.tangent_degree D.curve A.tangent]
    omega
  by_contra hnonneg
  exact (not_lt_of_ge (mul_nonneg (by have hn := A.exponent_ge_two; omega)
    (le_of_not_gt hnonneg))) hnegative

theorem exponents_equal (calculus : HolomorphicMixedFrameCalculus)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    {D : EmbeddedCurve X} (A B : ComponentNormalTensorData D) (hD : D.curve.Hyperbolic) :
    A.exponent = B.exponent := by
  have hnormal := normal_degree_eq calculus theory invariance A.frames B.frames
  obtain ⟨ha, hnegative⟩ := A.degree_facts theory invariance hD
  obtain ⟨hb, _⟩ := B.degree_facts theory invariance hD
  rw [← hnormal] at hb
  rw [theory.tangent_degree D.curve A.tangent] at ha
  rw [theory.tangent_degree D.curve B.tangent] at hb
  exact_mod_cast (mul_right_cancel₀ (ne_of_lt hnegative) (ha.trans hb.symm))

end ComponentNormalTensorData

theorem intrinsic_tangency_from_intersection
    (metrics : MetricTangency.HyperbolicMetricTheory)
    (calculus : EmbeddedFrames.HolomorphicFrameCalculus)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (homLaw : HomDegreeLaw theory)
    (f h : Fibration X) (hf : f.Smooth) (hh : h.Smooth)
    (hB : f.Hyperbolic) (hC : h.Hyperbolic)
    (D E : EmbeddedCurve X) (A : ComponentNormalTensorData D)
    (hD : D.curve.Hyperbolic) (hE : E.curve.Hyperbolic)
    (hDf : D.Unramified f) (hEf : E.Unramified f) (hEh : E.Unramified h)
    (hEtangent : E.TangentToPair f h)
    (p : D.curve) (q : E.curve) (hpq : D.inclusion p = E.inclusion q) :
    D.TangentToPair f h := by
  have hDh : D.Unramified h := MetricTangency.third_restriction_unramified_of_intersection
    metrics f h hf hh hB hC D.inclusion E.inclusion hD hE p q hpq
    (hEtangent ⟨q, rfl⟩) hDf hEf hEh
  obtain ⟨ht, hn⟩ := A.degree_facts theory invariance hD
  exact EmbeddedFrames.tangentToPair_from_normal_tensor calculus theory homLaw A.frames
    f h hDf hDh A.exponent A.exponent_ge_two hn ht

theorem intrinsic_ramification_component_dichotomy
    (metrics : MetricTangency.HyperbolicMetricTheory)
    (calculus : EmbeddedFrames.HolomorphicFrameCalculus)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (homLaw : HomDegreeLaw theory)
    (f g h : Fibration X) (hf : f.Smooth) (hg : g.Smooth) (hh : h.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic) (hH : h.Hyperbolic)
    (D : EmbeddedCurve X) (A : ComponentNormalTensorData D) (hD : D.curve.Hyperbolic)
    (hDf : D.Unramified f) (hDg : D.Unramified g) (hDfg : D.TangentToPair f g)
    (F : RamificationCurveFamily f h) (G : RamificationCurveFamily g h) :
    (D.DisjointFromPair f h ∧ D.DisjointFromPair g h) ∨
      (D.TangentToPair f h ∧ D.TangentToPair g h) := by
  classical
  by_cases hd : D.DisjointFromPair f h ∧ D.DisjointFromPair g h
  · exact Or.inl hd
  right
  have hm : (∃ p : D.curve, D.inclusion p ∈ RamificationSupport.ramificationSet f h) ∨
      (∃ p : D.curve, D.inclusion p ∈ RamificationSupport.ramificationSet g h) := by
    by_contra hm
    apply hd
    push_neg at hm
    constructor
    · apply Set.disjoint_left.mpr
      rintro x ⟨p, rfl⟩ hx
      exact hm.1 p hx
    · apply Set.disjoint_left.mpr
      rintro x ⟨p, rfl⟩ hx
      exact hm.2 p hx
  rcases hm with ⟨p, hp⟩ | ⟨p, hp⟩
  · rw [← F.support_eq] at hp
    obtain ⟨i, q, hq⟩ := Set.mem_iUnion.mp hp
    have hE : (F.member i).TangentToPair f h := by
      intro x hx
      rw [← F.support_eq]
      exact Set.mem_iUnion.mpr ⟨i, hx⟩
    have hfh := intrinsic_tangency_from_intersection metrics calculus theory invariance homLaw
      f h hf hh hB hH D (F.member i) A hD (F.hyperbolic i) hDf (F.first_unramified i)
      (F.second_unramified i) hE p q hq.symm
    exact ⟨hfh, D.tangentToPair_trans f g h hf hg hh hDfg hfh⟩
  · rw [← G.support_eq] at hp
    obtain ⟨i, q, hq⟩ := Set.mem_iUnion.mp hp
    have hE : (G.member i).TangentToPair g h := by
      intro x hx
      rw [← G.support_eq]
      exact Set.mem_iUnion.mpr ⟨i, hx⟩
    have hgh := intrinsic_tangency_from_intersection metrics calculus theory invariance homLaw
      g h hg hh hC hH D (G.member i) A hD (G.hyperbolic i) hDg (G.first_unramified i)
      (G.second_unramified i) hE p q hq.symm
    exact ⟨D.tangentToPair_trans g f h hg hf hh (D.tangentToPair_symm f g hDfg) hgh, hgh⟩

end Paper27.Geometry
