import Paper27.Geometry.EmbeddedCurve
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Actual differentials in adapted frames along an embedded curve

Raw frames below trivialize the actual ambient tangent space along an actual
embedded curve. The tangent coordinates are the actual differentials of its
complex charts. Frame changes are defined as `frame_j⁻¹ ∘ frame_i`; their
tangent and normal transition laws identify the supplied honest line cocycles
with the tangent line and normal quotient. No splitting is assumed.

For an arbitrary actual holomorphic map whose restriction to the curve is
unramified, the normalized covector is defined by
`ci_i ∘ d(u|D)⁻¹ ∘ du ∘ frame_i`. Its tangent identity and overlap law are proved
by the actual chain rule and cancellation of the actual frame equivalences.
Only holomorphicity of the coefficient functions is an explicit universal
classical bundle-frame calculus input. In particular neither existence of
`NormalizedCovectors`, a normal correction section, nor its vanishing is an
external input. The quotient-section argument then proves actual kernel
equality and containment in the actual paired ramification set.

Constructing such raw holomorphic adapted frames for a given embedding is
the usual local exact-sequence/frame theorem, not proved in this file. Raw
frames are displayed data in every result below. The universal coefficient
calculus is likewise left as a precise parameter, not asserted as an axiom.
-/

noncomputable section

open scoped Manifold Topology

namespace Paper27.Geometry.EmbeddedFrames

variable {X : CompactComplexSurface}

/-- The actual differential of the chart `i`, made total by using the identity
outside its domain. All geometric claims use points in that chart domain. -/
def tangentCoordinate (C : Curve) (i p : C) : ℂ ≃L[ℂ] ℂ := by
  classical
  exact if hp : p ∈ C.chartDomain i then
    (mdifferentiable_chart (I := 𝓘(ℂ, ℂ)) i).mfderiv hp
  else ContinuousLinearEquiv.refl ℂ ℂ

theorem tangentCoordinate_eq_chart (C : Curve) (i p : C)
    (hp : p ∈ C.chartDomain i) :
    (tangentCoordinate C i p).toContinuousLinearMap =
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ i) p := by
  classical
  simp only [tangentCoordinate, dif_pos hp]
  rfl

/-- Honest raw adapted frame data for the actual ambient tangent bundle.
`tangent_transition` refers to actual chart derivatives, and `normal` to the
quotient coordinate of the actual frame change. -/
structure RawEmbeddedFrames (D : EmbeddedCurve X)
    (N T : HolomorphicLineCocycle D.curve) where
  frame : D.curve → D.curve → (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ)
  /-- The frames are holomorphic in the actual ambient tangent
  trivializations. Holomorphic frame changes alone would not ensure this. -/
  holomorphic_in_ambient_charts : ∀ (i : D.curve) (a : X) (v : ℂ × ℂ),
    MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ)
      (fun p => mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (chartAt (ℂ × ℂ) a)
        (D.inclusion p) (frame i p v))
      (D.curve.chartDomain i ∩ D.inclusion ⁻¹' (chartAt (ℂ × ℂ) a).source)
  tangent_adapted : ∀ i p, p ∈ D.curve.chartDomain i → ∀ z : ℂ,
    frame i p (z, 0) = mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p
      ((tangentCoordinate D.curve i p).symm z)
  tangent_transition : ∀ i j p, p ∈ D.curve.chartDomain i →
    p ∈ D.curve.chartDomain j → ∀ w : ℂ,
      tangentCoordinate D.curve j p w =
        T.transition i j p * tangentCoordinate D.curve i p w
  normal : ∀ i j p, p ∈ D.curve.chartDomain i →
    p ∈ D.curve.chartDomain j → ∀ v : ℂ × ℂ,
      ((frame j p).symm (frame i p v)).2 = N.transition i j p * v.2
  holomorphic_change : ∀ i j (v : ℂ × ℂ),
    MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ)
      (fun p => (frame j p).symm (frame i p v))
      (D.curve.chartDomain i ∩ D.curve.chartDomain j)

namespace RawEmbeddedFrames

variable {D : EmbeddedCurve X} {N T : HolomorphicLineCocycle D.curve}

/-- Change of actual ambient frames, rather than a separate cocycle label. -/
def change (A : RawEmbeddedFrames D N T) (i j p : D.curve) :
    (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := (A.frame i p).trans (A.frame j p).symm

@[simp] theorem change_apply (A : RawEmbeddedFrames D N T)
    (i j p : D.curve) (v : ℂ × ℂ) :
    A.change i j p v = (A.frame j p).symm (A.frame i p v) := rfl

theorem change_tangent (A : RawEmbeddedFrames D N T) (i j p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) (z : ℂ) :
    A.change i j p (z, 0) = (T.transition i j p * z, 0) := by
  apply (A.frame j p).injective
  simp only [change_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [A.tangent_adapted i p hi, A.tangent_adapted j p hj]
  congr 1
  apply (tangentCoordinate D.curve j p).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, A.tangent_transition i j p hi hj,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The cocycle identities and tangent action are constructed from actual
frames; they are not separately assumed. -/
def toAdaptedFrameCocycle (A : RawEmbeddedFrames D N T) :
    NormalQuotient.AdaptedFrameCocycle D.curve N T where
  change := A.change
  holomorphic := A.holomorphic_change
  self := by
    intro i p _
    apply ContinuousLinearEquiv.ext
    funext v
    exact (A.frame i p).symm_apply_apply v
  compose := by
    intro i j k p _ _ _ v
    simp only [change_apply, ContinuousLinearEquiv.apply_symm_apply]
  tangent := A.change_tangent
  normal := A.normal

/-- A single raw frame is an actual tangent frame in the embedded-curve API. -/
def tangentFrame (A : RawEmbeddedFrames D N T) (i p : D.curve)
    (hp : p ∈ D.curve.chartDomain i) : D.TangentFrame p where
  ambient := A.frame i p
  tangent := (tangentCoordinate D.curve i p).symm
  adapted := A.tangent_adapted i p hp

end RawEmbeddedFrames

/-- Restriction of an arbitrary actual holomorphic map to the embedded curve. -/
def restrictionMap (D : EmbeddedCurve X) {B : Curve} (u : HolomorphicMap X B) :
    HolomorphicMap D.curve B :=
  ⟨fun p => u (D.inclusion p), u.holomorphic.comp D.inclusion.holomorphic⟩

/-- Unramifiedness is actual bijectivity of the restricted differential. -/
def UnramifiedRestriction (D : EmbeddedCurve X) {B : Curve} (u : HolomorphicMap X B) : Prop :=
  ∀ p : D.curve, Function.Bijective
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (restrictionMap D u) p)

theorem restrictionMap_mfderiv_apply (D : EmbeddedCurve X) {B : Curve}
    (u : HolomorphicMap X B) (p : D.curve) (w : ℂ) :
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (restrictionMap D u) p w =
      mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) u (D.inclusion p)
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p w) := by
  rw [show mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (restrictionMap D u) p =
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) u (D.inclusion p)).comp
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p) from
    mfderiv_comp p (u.holomorphic _) (D.inclusion.holomorphic p)]
  rfl

/-- The inverse used to normalize the target is the inverse of the actual
restricted differential; finite-dimensionality supplies its continuity. -/
def restrictionDifferentialEquiv (D : EmbeddedCurve X) {B : Curve}
    (u : HolomorphicMap X B) (hu : UnramifiedRestriction D u) (p : D.curve) :
    ℂ ≃L[ℂ] ℂ := by
  let L : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (restrictionMap D u) p
  exact (LinearEquiv.ofBijective L.toLinearMap (hu p)).toContinuousLinearEquiv

@[simp] theorem restrictionDifferentialEquiv_apply (D : EmbeddedCurve X) {B : Curve}
    (u : HolomorphicMap X B) (hu : UnramifiedRestriction D u) (p : D.curve) (w : ℂ) :
    restrictionDifferentialEquiv D u hu p w =
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (restrictionMap D u) p w := rfl

/-- The actual target normalization `ci_i ∘ d(u|D)⁻¹`. -/
def targetNormalizer (D : EmbeddedCurve X) {B : Curve} (u : HolomorphicMap X B)
    (hu : UnramifiedRestriction D u) (i p : D.curve) : ℂ ≃L[ℂ] ℂ :=
  (restrictionDifferentialEquiv D u hu p).symm.trans (tangentCoordinate D.curve i p)

/-- The actual covector `ci_i ∘ d(u|D)⁻¹ ∘ du ∘ frame_i`. -/
def normalizedCovector {D : EmbeddedCurve X} {N T : HolomorphicLineCocycle D.curve}
    (A : RawEmbeddedFrames D N T) {B : Curve} (u : HolomorphicMap X B)
    (hu : UnramifiedRestriction D u) (i p : D.curve) : (ℂ × ℂ) →L[ℂ] ℂ :=
  (targetNormalizer D u hu i p).toContinuousLinearMap.comp
    ((mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) u (D.inclusion p)).comp
      (A.frame i p).toContinuousLinearMap)

@[simp] theorem normalizedCovector_apply {D : EmbeddedCurve X}
    {N T : HolomorphicLineCocycle D.curve} (A : RawEmbeddedFrames D N T)
    {B : Curve} (u : HolomorphicMap X B) (hu : UnramifiedRestriction D u)
    (i p : D.curve) (v : ℂ × ℂ) :
    normalizedCovector A u hu i p v = tangentCoordinate D.curve i p
      ((restrictionDifferentialEquiv D u hu p).symm
        (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) u (D.inclusion p) (A.frame i p v))) := rfl

theorem normalizedCovector_tangent {D : EmbeddedCurve X}
    {N T : HolomorphicLineCocycle D.curve} (A : RawEmbeddedFrames D N T)
    {B : Curve} (u : HolomorphicMap X B) (hu : UnramifiedRestriction D u)
    (i p : D.curve) (hp : p ∈ D.curve.chartDomain i) (z : ℂ) :
    normalizedCovector A u hu i p (z, 0) = z := by
  rw [normalizedCovector_apply, A.tangent_adapted i p hp,
    ← restrictionMap_mfderiv_apply]
  change tangentCoordinate D.curve i p
    ((restrictionDifferentialEquiv D u hu p).symm
      (restrictionDifferentialEquiv D u hu p ((tangentCoordinate D.curve i p).symm z))) = z
  rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem normalizedCovector_transform {D : EmbeddedCurve X}
    {N T : HolomorphicLineCocycle D.curve} (A : RawEmbeddedFrames D N T)
    {B : Curve} (u : HolomorphicMap X B) (hu : UnramifiedRestriction D u)
    (i j p : D.curve) (hi : p ∈ D.curve.chartDomain i)
    (hj : p ∈ D.curve.chartDomain j) (v : ℂ × ℂ) :
    normalizedCovector A u hu j p (A.change i j p v) =
      T.transition i j p * normalizedCovector A u hu i p v := by
  simp only [normalizedCovector_apply, RawEmbeddedFrames.change_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  exact A.tangent_transition i j p hi hj _

/-- The sole additional analytic calculus parameter. For every actual
holomorphic map, every actual embedded curve and honest raw holomorphic
adapted frames, inverse normalization by its unramified restriction has
holomorphic coefficient functions. This is the usual holomorphic local
bundle-map calculus, including inversion of an invertible line-bundle map.
It contains none of the tangent, transition, correction, or equality claims. -/
def HolomorphicFrameCalculus : Prop :=
  ∀ (X : CompactComplexSurface) (D : EmbeddedCurve X)
    (N T : HolomorphicLineCocycle D.curve) (A : RawEmbeddedFrames D N T)
    (B : Curve) (u : HolomorphicMap X B) (hu : UnramifiedRestriction D u)
    (i : D.curve) (v : ℂ × ℂ),
    MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun p => normalizedCovector A u hu i p v) (D.curve.chartDomain i)

/-- The covectors of the actual fibrations are constructed from their actual
differentials. Their tangent and transition laws are the preceding proofs. -/
def normalizedCovectors (calculus : HolomorphicFrameCalculus)
    {D : EmbeddedCurve X} {N T : HolomorphicLineCocycle D.curve}
    (A : RawEmbeddedFrames D N T) (f h : Fibration X)
    (hf : D.Unramified f) (hh : D.Unramified h) :
    NormalQuotient.NormalizedCovectors A.toAdaptedFrameCocycle where
  l₁ := normalizedCovector A (CoordinateCalculus.fibrationMap f) hf
  l₃ := normalizedCovector A (CoordinateCalculus.fibrationMap h) hh
  holomorphic_l₁ := calculus X D N T A f.base (CoordinateCalculus.fibrationMap f) hf
  holomorphic_l₃ := calculus X D N T A h.base (CoordinateCalculus.fibrationMap h) hh
  tangent_l₁ := normalizedCovector_tangent A (CoordinateCalculus.fibrationMap f) hf
  tangent_l₃ := normalizedCovector_tangent A (CoordinateCalculus.fibrationMap h) hh
  transform_l₁ := normalizedCovector_transform A (CoordinateCalculus.fibrationMap f) hf
  transform_l₃ := normalizedCovector_transform A (CoordinateCalculus.fibrationMap h) hh

@[simp] theorem normalizedCovector_fibration {D : EmbeddedCurve X}
    {N T : HolomorphicLineCocycle D.curve} (A : RawEmbeddedFrames D N T)
    (f : Fibration X) (hf : D.Unramified f) (i p : D.curve) :
    normalizedCovector A (CoordinateCalculus.fibrationMap f) hf i p =
      NormalQuotient.normalizedFibrationDifferential f (D.inclusion p) (A.frame i p)
        (targetNormalizer D (CoordinateCalculus.fibrationMap f) hf i p) := rfl

/-- The constructed quotient section vanishes by negative Hom degree, giving
equality of the actual normalized fibration differentials. -/
theorem normalized_equal_of_negative_hom_degree (calculus : HolomorphicFrameCalculus)
    (theory : LineBundleDegreeTheory) {D : EmbeddedCurve X}
    {N T : HolomorphicLineCocycle D.curve} (A : RawEmbeddedFrames D N T)
    (f h : Fibration X) (hf : D.Unramified f) (hh : D.Unramified h)
    (hnegative : theory.degree D.curve (NormalQuotient.homCocycle N T).bundle < 0) :
    ∀ i p, p ∈ D.curve.chartDomain i →
      NormalQuotient.normalizedFibrationDifferential f (D.inclusion p) (A.frame i p)
        (targetNormalizer D (CoordinateCalculus.fibrationMap f) hf i p) =
      NormalQuotient.normalizedFibrationDifferential h (D.inclusion p) (A.frame i p)
        (targetNormalizer D (CoordinateCalculus.fibrationMap h) hh i p) := by
  exact (normalizedCovectors calculus A f h hf hh).covectors_equal_of_negative_hom_degree
    theory hnegative

/-- In particular the actual manifold differential kernels coincide along
the entire curve; no normalized-covector equality is an assumption. -/
theorem kernels_equal_of_negative_hom_degree (calculus : HolomorphicFrameCalculus)
    (theory : LineBundleDegreeTheory) {D : EmbeddedCurve X}
    {N T : HolomorphicLineCocycle D.curve} (A : RawEmbeddedFrames D N T)
    (f h : Fibration X) (hf : D.Unramified f) (hh : D.Unramified h)
    (hnegative : theory.degree D.curve (NormalQuotient.homCocycle N T).bundle < 0)
    (p : D.curve) :
    LinearMap.ker (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f (D.inclusion p)).toLinearMap =
      LinearMap.ker (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) h (D.inclusion p)).toLinearMap := by
  exact NormalQuotient.actual_kernels_equal_of_normalized_equality f h (D.inclusion p)
    (A.frame p p) _ _
    (normalized_equal_of_negative_hom_degree calculus theory A f h hf hh hnegative
      p p (mem_chart_source ℂ p))

/-- Lemma 3.1's actual tangency conclusion, conditional only on raw adapted
frames, the general coefficient calculus, unramified actual restrictions and
negative actual Hom degree. The ramification bridge uses the actual paired
manifold differential from `CoordinateCalculus`. -/
theorem tangentToPair_of_negative_hom_degree (calculus : HolomorphicFrameCalculus)
    (theory : LineBundleDegreeTheory) {D : EmbeddedCurve X}
    {N T : HolomorphicLineCocycle D.curve} (A : RawEmbeddedFrames D N T)
    (f h : Fibration X) (hf : D.Unramified f) (hh : D.Unramified h)
    (hnegative : theory.degree D.curve (NormalQuotient.homCocycle N T).bundle < 0) :
    D.TangentToPair f h := by
  rintro _ ⟨p, rfl⟩
  exact EmbeddedCurve.ramified_of_normalized_equality f h (D.inclusion p)
    (A.frame p p) _ _
    (normalized_equal_of_negative_hom_degree calculus theory A f h hf hh hnegative
      p p (mem_chart_source ℂ p))

/-- The normal tensor identity supplies the needed negative Hom degree using
the proved arithmetic, with no section or differential equality premise. -/
theorem tangentToPair_from_normal_tensor (calculus : HolomorphicFrameCalculus)
    (theory : LineBundleDegreeTheory) (homLaw : HomDegreeLaw theory)
    {D : EmbeddedCurve X} {N T : HolomorphicLineCocycle D.curve}
    (A : RawEmbeddedFrames D N T) (f h : Fibration X)
    (hf : D.Unramified f) (hh : D.Unramified h)
    (n : ℕ) (hn : 2 ≤ n) (hN : theory.degree D.curve N < 0)
    (htensor : (n : ℤ) * theory.degree D.curve N = theory.degree D.curve T) :
    D.TangentToPair f h := by
  apply tangentToPair_of_negative_hom_degree calculus theory A f h hf hh
  exact normal_hom_degree theory homLaw D.curve N T (NormalQuotient.homCocycle N T)
    n hn hN htensor

end Paper27.Geometry.EmbeddedFrames
