import Paper27.Geometry.NormalAtlasTensor
import Paper27.Geometry.ThreeRetractionOrders

/-!
# The common-tangency obstruction from three actual pair normal atlases

Each tensor gauge is constructed from actual retractions, actual normalized
normal charts, and honest holomorphic adapted frames. Intrinsic normal degree
forces the three exponents to agree. The actual pair normal forms then give
the two scalar orders used in the Appendix connection calculation.

A final theorem eliminates free frame data using only a general classical
adapted-frame existence statement for arbitrary embedded complex curves. It
contains no retraction, exponent, normal tensor, or obstruction conclusion.
-/
noncomputable section
open scoped Manifold

namespace Paper27.Geometry.ThreePairNormalObstruction
open RetractionCoordinateGerms RetractionCoefficientHolomorphic
open EmbeddedFrames NormalDegreeInvariance

variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ r₃ : D.Retraction U} {n m k : ℕ}

/-- Intrinsic normal degree compares exponents even when the three pairs use
independently chosen honest ambient frames and normal line cocycles. -/
theorem three_exponents_equal
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (calculus : HolomorphicMixedFrameCalculus)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (A : NormalAtlas D U r₁ r₂ n) (B : NormalAtlas D U r₁ r₃ m)
    (C : NormalAtlas D U r₂ r₃ k)
    {N₁ N₂ N₃ : HolomorphicLineCocycle D.curve}
    {T₁ T₂ T₃ : TangentLineCocycle D.curve}
    (F₁ : RawEmbeddedFrames D N₁ T₁.bundle) (F₂ : RawEmbeddedFrames D N₂ T₂.bundle)
    (F₃ : RawEmbeddedFrames D N₃ T₃.bundle)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hk : 2 ≤ k) (hg : D.curve.Hyperbolic) :
    n = m ∧ n = k := by
  have hnm := (A.componentNormalTensorData regularity F₁ hn).exponents_equal
    calculus theory invariance (B.componentNormalTensorData regularity F₂ hm) hg
  have hnk := (A.componentNormalTensorData regularity F₁ hn).exponents_equal
    calculus theory invariance (C.componentNormalTensorData regularity F₃ hk) hg
  exact ⟨hnm, hnk⟩

/-- When all three actual pairs use the same honest frames of the same actual
normal quotient, degree cancellation needs no mixed-frame regularity input. -/
theorem three_exponents_equal_common_frames
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (A : NormalAtlas D U r₁ r₂ n) (B : NormalAtlas D U r₁ r₃ m)
    (C : NormalAtlas D U r₂ r₃ k)
    {N : HolomorphicLineCocycle D.curve} {T : TangentLineCocycle D.curve}
    (F : RawEmbeddedFrames D N T.bundle)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hk : 2 ≤ k) (hg : D.curve.Hyperbolic) :
    n = m ∧ n = k := by
  have hA := A.normal_tensor_degree regularity F (by omega) theory invariance
  have hB := B.normal_tensor_degree regularity F (by omega) theory invariance
  have hC := C.normal_tensor_degree regularity F (by omega) theory invariance
  have hnegative := A.normal_degree_negative regularity F (by omega) theory invariance hg
  constructor
  · exact_mod_cast mul_right_cancel₀ (ne_of_lt hnegative) (hA.trans hB.symm)
  · exact_mod_cast mul_right_cancel₀ (ne_of_lt hnegative) (hA.trans hC.symm)

/-- No equality of the indices, scalar order, leading constant, or connection
is an input: all are derived from the three actual pair normal atlases. -/
theorem impossible_with_common_frames
    (J : TaylorGerms.TaylorCalculus) (P : ParametricTaylorCalculus J)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (A : NormalAtlas D U r₁ r₂ n) (B : NormalAtlas D U r₁ r₃ m)
    (C : NormalAtlas D U r₂ r₃ k)
    {N : HolomorphicLineCocycle D.curve} {T : TangentLineCocycle D.curve}
    (F : RawEmbeddedFrames D N T.bundle)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hk : 2 ≤ k) (hg : D.curve.Hyperbolic) : False := by
  obtain ⟨hnm, hnk⟩ := three_exponents_equal_common_frames P.regularity theory invariance
    A B C F hn hm hk hg
  subst m
  subst k
  exact A.common_tangency_impossible_of_three_pair_atlases J P B C hn T theory hg

/-- Universal adapted-frame existence for an arbitrary actual embedded compact
complex curve. Canonical curve chart domains are open Riemann surfaces, where
holomorphic vector bundles are trivial (Grauert-Roehrl / Oka-Grauert); Cartan B
splits the restricted tangent/normal exact sequence. The tangent cocycle is
identified with actual chart derivatives by `TangentLineCocycle` and the frames
are the actual holomorphic frames of `RawEmbeddedFrames`.

A primary published reference for the open-Riemann-surface triviality used here
is Forstneric, *Divisors defined by noncritical functions*,
Proc. AMS 146 (2018), 2985-2994, p. 2987, preceding Corollary 1.5
(https://users.fmf.uni-lj.si/forstneric/papers/2018PAMS.pdf,
DOI 10.1090/proc/13990); it cites his book,
Theorem 5.3.1(iii). This interface has no maps to compare, normal forms,
exponents, degree identities, ramification, or obstruction statement. -/
def NormalFrameExistence : Prop :=
  ∀ (X : CompactComplexSurface) (D : EmbeddedCurve X),
    ∃ (N : HolomorphicLineCocycle D.curve) (T : TangentLineCocycle D.curve),
      Nonempty (RawEmbeddedFrames D N T.bundle)

/-- The three-pair obstruction requires only actual pair normal atlases and
the displayed universal classical analytic and bundle facts. One honest frame
is chosen for the actual embedded curve and reused for all three pairs. -/
theorem impossible
    (J : TaylorGerms.TaylorCalculus) (P : ParametricTaylorCalculus J)
    (frames : NormalFrameExistence)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (A : NormalAtlas D U r₁ r₂ n) (B : NormalAtlas D U r₁ r₃ m)
    (C : NormalAtlas D U r₂ r₃ k)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hk : 2 ≤ k) (hg : D.curve.Hyperbolic) : False := by
  obtain ⟨N, T, ⟨F⟩⟩ := frames X D
  exact impossible_with_common_frames J P theory invariance A B C F hn hm hk hg

end Paper27.Geometry.ThreePairNormalObstruction
