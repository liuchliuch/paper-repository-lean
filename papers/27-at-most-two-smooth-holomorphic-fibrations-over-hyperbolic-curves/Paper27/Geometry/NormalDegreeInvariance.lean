import Paper27.Geometry.RamificationDichotomy

/-!
# Intrinsic normal degree and the common ramification index

Two honest adapted ambient frames on the same actual embedded curve describe
the same normal quotient. Their mixed actual frame change induces the scalar
gauge constructed below. Its nonvanishing and overlap law are proved from the
actual frames, rather than asserted as an isomorphism of arbitrary labels.

Only two general classical facts are parameters: holomorphic coefficients of
mixed holomorphic frame changes, and invariance of line-bundle degree under
an explicit nowhere-zero holomorphic Cech gauge. Neither parameter mentions
ramification indices or normal tensor identities. The equality of two actual
normal degrees and then of the component indices is proved here.
-/

noncomputable section

open scoped Manifold

namespace Paper27.Geometry.NormalDegreeInvariance

variable {X : CompactComplexSurface} {D : EmbeddedCurve X}
  {N T N' T' : HolomorphicLineCocycle D.curve}

/-- The actual mixed change from the first ambient frame to the second. -/
def mixedFrame (A : EmbeddedFrames.RawEmbeddedFrames D N T)
    (B : EmbeddedFrames.RawEmbeddedFrames D N' T') (i p : D.curve) :
    (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := (A.frame i p).trans (B.frame i p).symm

@[simp] theorem mixedFrame_apply (A : EmbeddedFrames.RawEmbeddedFrames D N T)
    (B : EmbeddedFrames.RawEmbeddedFrames D N' T') (i p : D.curve) (v : ℂ × ℂ) :
    mixedFrame A B i p v = (B.frame i p).symm (A.frame i p v) := rfl

/-- Both raw frames use the very same actual chart differential on TD. Thus
the mixed change is the identity on the tangent coordinate line. -/
theorem mixedFrame_tangent (A : EmbeddedFrames.RawEmbeddedFrames D N T)
    (B : EmbeddedFrames.RawEmbeddedFrames D N' T') (i p : D.curve)
    (hp : p ∈ D.curve.chartDomain i) (z : ℂ) :
    mixedFrame A B i p (z, 0) = (z, 0) := by
  apply (B.frame i p).injective
  simp only [mixedFrame_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [A.tangent_adapted i p hp, B.tangent_adapted i p hp]

/-- The normal quotient gauge is the actual second coordinate of the image
of the first frame's normal basis vector in the second frame. -/
def normalGauge (A : EmbeddedFrames.RawEmbeddedFrames D N T)
    (B : EmbeddedFrames.RawEmbeddedFrames D N' T') (i p : D.curve) : ℂ :=
  (mixedFrame A B i p (0, 1)).2

/-- Since the mixed change fixes the tangent line, its induced quotient map
is exactly multiplication by the constructed normal gauge. -/
theorem mixedFrame_normal (A : EmbeddedFrames.RawEmbeddedFrames D N T)
    (B : EmbeddedFrames.RawEmbeddedFrames D N' T') (i p : D.curve)
    (hp : p ∈ D.curve.chartDomain i) (v : ℂ × ℂ) :
    (mixedFrame A B i p v).2 = normalGauge A B i p * v.2 := by
  have hv : v = (v.1, 0) + v.2 • (0, 1) := by ext <;> simp
  calc
    (mixedFrame A B i p v).2 =
        (mixedFrame A B i p (v.1, 0)).2 + v.2 * (mixedFrame A B i p (0, 1)).2 := by
      conv_lhs => rw [hv, map_add, map_smul]
      rfl
    _ = normalGauge A B i p * v.2 := by
      rw [mixedFrame_tangent A B i p hp]
      simp only [zero_add, normalGauge, mul_comm]

theorem normalGauge_ne_zero (A : EmbeddedFrames.RawEmbeddedFrames D N T)
    (B : EmbeddedFrames.RawEmbeddedFrames D N' T') (i p : D.curve)
    (hp : p ∈ D.curve.chartDomain i) : normalGauge A B i p ≠ 0 := by
  intro hzero
  let v : ℂ × ℂ := mixedFrame A B i p (0, 1)
  have hv : v.2 = 0 := hzero
  have hpair : mixedFrame A B i p (0, 1) = (v.1, 0) := Prod.ext rfl hv
  have hinj : ((0, 1) : ℂ × ℂ) = (v.1, 0) := (mixedFrame A B i p).injective
    (hpair.trans (mixedFrame_tangent A B i p hp v.1).symm)
  exact one_ne_zero (congrArg Prod.snd hinj)

/-- The overlap law for the actual quotient gauge. Both descriptions of the
same actual normal vector give c_j N_ij = N'_ij c_i. -/
theorem normalGauge_compatible (A : EmbeddedFrames.RawEmbeddedFrames D N T)
    (B : EmbeddedFrames.RawEmbeddedFrames D N' T') (i j p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    normalGauge A B j p * N.transition i j p =
      N'.transition i j p * normalGauge A B i p := by
  let v : ℂ × ℂ := A.frame i p (0, 1)
  let w : ℂ × ℂ := (A.frame j p).symm v
  have hw : w.2 = N.transition i j p := by
    simpa only [mul_one] using A.normal i j p hi hj (0, 1)
  calc
    normalGauge A B j p * N.transition i j p = (mixedFrame A B j p w).2 := by
      rw [mixedFrame_normal A B j p hj, hw]
    _ = ((B.frame j p).symm v).2 := by
      simp only [mixedFrame_apply, w, ContinuousLinearEquiv.apply_symm_apply]
    _ = N'.transition i j p * normalGauge A B i p := by
      have hnormal := B.normal i j p hi hj ((B.frame i p).symm v)
      simpa only [ContinuousLinearEquiv.apply_symm_apply, normalGauge,
        mixedFrame_apply, v] using hnormal

/-- Standard bundle-frame calculus, stated only for actual holomorphic raw
frames: the coefficients of their mixed inverse/composition are holomorphic.
Only analyticity is an input; the quotient gauge, nonvanishing, and its
transition compatibility are constructed and proved in this file. -/
def HolomorphicMixedFrameCalculus : Prop :=
  ∀ (X : CompactComplexSurface) (D : EmbeddedCurve X)
    (N T N' T' : HolomorphicLineCocycle D.curve)
    (A : EmbeddedFrames.RawEmbeddedFrames D N T)
    (B : EmbeddedFrames.RawEmbeddedFrames D N' T') (i : D.curve) (v : ℂ × ℂ),
    MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun p => (mixedFrame A B i p v).2) (D.curve.chartDomain i)

/-- An explicit actual Cech line-bundle isomorphism by scalar coefficients.
The convention is that coordinates change by the given transition functions. -/
structure HolomorphicLineGauge {C : Curve} (L K : HolomorphicLineCocycle C) where
  coefficient : C → C → ℂ
  holomorphic : ∀ i, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
    (coefficient i) (C.chartDomain i)
  nonzero : ∀ i p, p ∈ C.chartDomain i → coefficient i p ≠ 0
  compatible : ∀ i j p, p ∈ C.chartDomain i → p ∈ C.chartDomain j →
    coefficient j p * L.transition i j p = K.transition i j p * coefficient i p

/-- Degree is invariant under an explicit nowhere-zero holomorphic gauge.
This general classical law quantifies all actual curves, line cocycles and
gauges, and mentions no embedding, fibration, exponent, or degree sign. -/
def LineBundleDegreeGaugeInvariance (theory : LineBundleDegreeTheory) : Prop :=
  ∀ (C : Curve) (L K : HolomorphicLineCocycle C), HolomorphicLineGauge L K →
    theory.degree C L = theory.degree C K

/-- The line-bundle isomorphism is built from the actual ambient frames. -/
def normalLineGauge (calculus : HolomorphicMixedFrameCalculus)
    (A : EmbeddedFrames.RawEmbeddedFrames D N T)
    (B : EmbeddedFrames.RawEmbeddedFrames D N' T') : HolomorphicLineGauge N N' where
  coefficient := normalGauge A B
  holomorphic := fun i => calculus X D N T N' T' A B i (0, 1)
  nonzero := normalGauge_ne_zero A B
  compatible := normalGauge_compatible A B

/-- Normal degree is intrinsic to the actual embedding, independently of the
actual holomorphic adapted frames used to describe its quotient. -/
theorem normal_degree_eq (calculus : HolomorphicMixedFrameCalculus)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (A : EmbeddedFrames.RawEmbeddedFrames D N T)
    (B : EmbeddedFrames.RawEmbeddedFrames D N' T') :
    theory.degree D.curve N = theory.degree D.curve N' :=
  invariance D.curve N N' (normalLineGauge calculus A B)

/-- The common-index assertion of Lemma 3.1. Each component's tensor/degree
facts come from its own raw normal jets. The actual normal gauges identify
their normal degrees; negativity permits cancellation of that common degree.
The index equality itself is proved, never used as an external premise. -/
theorem component_exponents_equal (calculus : HolomorphicMixedFrameCalculus)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (A B : ComponentNormalData D) (hD : D.curve.Hyperbolic) :
    A.exponent = B.exponent := by
  have hnormal := normal_degree_eq calculus theory invariance A.frames B.frames
  obtain ⟨ha, hnegative⟩ := A.degree_facts theory hD
  obtain ⟨hb, _⟩ := B.degree_facts theory hD
  rw [← hnormal] at hb
  rw [theory.tangent_degree D.curve A.tangent] at ha
  rw [theory.tangent_degree D.curve B.tangent] at hb
  have hindex : (A.exponent : ℤ) = (B.exponent : ℤ) :=
    mul_right_cancel₀ (ne_of_lt hnegative) (ha.trans hb.symm)
  exact_mod_cast hindex

theorem three_component_exponents_equal (calculus : HolomorphicMixedFrameCalculus)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (A B C : ComponentNormalData D) (hD : D.curve.Hyperbolic) :
    A.exponent = B.exponent ∧ A.exponent = C.exponent :=
  ⟨component_exponents_equal calculus theory invariance A B hD,
    component_exponents_equal calculus theory invariance A C hD⟩

end Paper27.Geometry.NormalDegreeInvariance
