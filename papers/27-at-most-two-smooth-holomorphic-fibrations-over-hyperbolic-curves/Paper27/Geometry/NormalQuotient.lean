import Paper27.Geometry.NormalCorrection
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Constructing the normal correction section in Lemma 3.1

The curve and its line cocycles are actual geometric objects. Rank-two adapted
frames are represented by a holomorphic cocycle of actual complex continuous
linear equivalences of `ℂ × ℂ`. Its first line has transition `T`, and its
quotient by that line has transition `N`.

Two holomorphic local covectors are normalized to be the identity on the first
line. Their difference therefore factors through the second coordinate. This
file constructs its coefficient, proves its holomorphicity and the transition
law `β_j = (T_ij / N_ij) β_i`, and hence constructs the global holomorphic
section of `Hom(N,T)`. Neither that section, its factorization, nor its
vanishing is assumed. The universal negative-degree theorem then forces the
two covectors to coincide.

For the surface application, the frames must still be constructed from
`TX|D`, its tangent line and normal quotient, and the covectors from the
actual fibration differentials normalized by their unramified restrictions.
`normalizedFibrationDifferential` gives the actual composition used for that
purpose; no claim is made here that such frames and normalizing equivalences
have been constructed for arbitrary three fibrations.
-/

noncomputable section

open scoped Manifold

namespace Paper27.Geometry.NormalQuotient

/-- The actual normalized differential, when a source tangent frame and a
target line normalization have been supplied. This uses the fibration's
actual manifold differential and actual continuous linear equivalences. -/
def normalizedFibrationDifferential {X : CompactComplexSurface} (f : Fibration X)
    (p : X)
    (frame : (ℂ × ℂ) ≃L[ℂ] TangentSpace 𝓘(ℂ, ℂ × ℂ) p)
    (normalize : TangentSpace 𝓘(ℂ, ℂ) (f p) ≃L[ℂ] ℂ) :
    (ℂ × ℂ) →L[ℂ] ℂ :=
  normalize.toContinuousLinearMap.comp
    ((mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p).comp frame.toContinuousLinearMap)

@[simp] theorem normalizedFibrationDifferential_apply {X : CompactComplexSurface}
    (f : Fibration X) (p : X)
    (frame : (ℂ × ℂ) ≃L[ℂ] TangentSpace 𝓘(ℂ, ℂ × ℂ) p)
    (normalize : TangentSpace 𝓘(ℂ, ℂ) (f p) ≃L[ℂ] ℂ) (v : ℂ × ℂ) :
    normalizedFibrationDifferential f p frame normalize v =
      normalize (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p (frame v)) := rfl

/-- Equality after normalization and use of one actual tangent frame gives
the equality on every actual tangent vector, using the frame's inverse. -/
theorem actual_differential_equality_of_normalized_equality
    {X : CompactComplexSurface} (f g : Fibration X) (p : X)
    (frame : (ℂ × ℂ) ≃L[ℂ] TangentSpace 𝓘(ℂ, ℂ × ℂ) p)
    (nf : TangentSpace 𝓘(ℂ, ℂ) (f p) ≃L[ℂ] ℂ)
    (ng : TangentSpace 𝓘(ℂ, ℂ) (g p) ≃L[ℂ] ℂ)
    (heq : normalizedFibrationDifferential f p frame nf =
      normalizedFibrationDifferential g p frame ng) :
    ∀ v : TangentSpace 𝓘(ℂ, ℂ × ℂ) p,
      nf (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p v) =
        ng (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) g p v) := by
  intro v
  have hv := congrArg (fun l : (ℂ × ℂ) →L[ℂ] ℂ => l (frame.symm v)) heq
  simpa only [normalizedFibrationDifferential_apply, frame.apply_symm_apply] using hv

/-- Thus the equality constructed from the quotient-section argument really
implies equality of the actual differential kernels whenever the local
covectors have been identified with these normalized differentials. -/
theorem actual_kernels_equal_of_normalized_equality
    {X : CompactComplexSurface} (f g : Fibration X) (p : X)
    (frame : (ℂ × ℂ) ≃L[ℂ] TangentSpace 𝓘(ℂ, ℂ × ℂ) p)
    (nf : TangentSpace 𝓘(ℂ, ℂ) (f p) ≃L[ℂ] ℂ)
    (ng : TangentSpace 𝓘(ℂ, ℂ) (g p) ≃L[ℂ] ℂ)
    (heq : normalizedFibrationDifferential f p frame nf =
      normalizedFibrationDifferential g p frame ng) :
    LinearMap.ker (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p).toLinearMap =
      LinearMap.ker (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) g p).toLinearMap := by
  ext v
  change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p v = 0 ↔
    mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) g p v = 0
  have hv := actual_differential_equality_of_normalized_equality f g p frame nf ng heq v
  constructor
  · intro hf
    apply ng.injective
    rw [← hv, hf]
    simp
  · intro hg
    apply nf.injective
    rw [hv, hg]
    simp

/-- The Hom line cocycle is constructed by dividing the actual transition
functions. Its holomorphicity and all cocycle identities are proved here. -/
def homCocycle {D : Curve} (N T : HolomorphicLineCocycle D) : HomLineCocycle N T where
  bundle :=
    { transition := fun i j p => T.transition i j p / N.transition i j p
      holomorphic := by
        intro i j p hp
        have hinv : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) Inv.inv
            (N.transition i j p) :=
          (differentiableAt_inv (𝕜 := ℂ) (N.nonzero i j p hp.1 hp.2)).mdifferentiableAt
        simpa only [div_eq_mul_inv] using
          (T.holomorphic i j p hp).mul
            (hinv.comp_mdifferentiableWithinAt p (N.holomorphic i j p hp))
      nonzero := fun i j p hi hj =>
        div_ne_zero (T.nonzero i j p hi hj) (N.nonzero i j p hi hj)
      self := by
        intro i p hp
        rw [T.self i p hp, N.self i p hp, one_div_one]
      compose := by
        intro i j k p hi hj hk
        rw [div_mul_div_comm, T.compose i j k p hi hj hk, N.compose i j k p hi hj hk] }
  transition_eq := fun _ _ _ _ _ => rfl

/-- A genuine holomorphic rank-two frame cocycle adapted to a line and its
normal quotient. The second-coordinate identity permits a nonzero upper
right matrix entry; no splitting of the extension is assumed. -/
structure AdaptedFrameCocycle (D : Curve) (N T : HolomorphicLineCocycle D) where
  change : D → D → D → (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ)
  holomorphic : ∀ i j (v : ℂ × ℂ),
    MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) (fun p => change i j p v)
      (D.chartDomain i ∩ D.chartDomain j)
  self : ∀ i p, p ∈ D.chartDomain i →
    change i i p = ContinuousLinearEquiv.refl ℂ (ℂ × ℂ)
  compose : ∀ i j k p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
    p ∈ D.chartDomain k → ∀ v, change j k p (change i j p v) = change i k p v
  tangent : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j → ∀ z : ℂ,
    change i j p (z, 0) = (T.transition i j p * z, 0)
  normal : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j → ∀ v,
    (change i j p v).2 = N.transition i j p * v.2

/-- The local covectors have holomorphic coefficients, restrict to the
identity on the tangent line, and transform as maps into the line `T`.
There is no normal correction coefficient or section among these fields. -/
structure NormalizedCovectors {D : Curve} {N T : HolomorphicLineCocycle D}
    (frames : AdaptedFrameCocycle D N T) where
  l₁ : D → D → (ℂ × ℂ) →L[ℂ] ℂ
  l₃ : D → D → (ℂ × ℂ) →L[ℂ] ℂ
  holomorphic_l₁ : ∀ i (v : ℂ × ℂ),
    MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun p => l₁ i p v) (D.chartDomain i)
  holomorphic_l₃ : ∀ i (v : ℂ × ℂ),
    MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun p => l₃ i p v) (D.chartDomain i)
  tangent_l₁ : ∀ i p, p ∈ D.chartDomain i → ∀ z : ℂ, l₁ i p (z, 0) = z
  tangent_l₃ : ∀ i p, p ∈ D.chartDomain i → ∀ z : ℂ, l₃ i p (z, 0) = z
  transform_l₁ : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j → ∀ v,
    l₁ j p (frames.change i j p v) = T.transition i j p * l₁ i p v
  transform_l₃ : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j → ∀ v,
    l₃ j p (frames.change i j p v) = T.transition i j p * l₃ i p v

namespace NormalizedCovectors

variable {D : Curve} {N T : HolomorphicLineCocycle D}
  {frames : AdaptedFrameCocycle D N T}

/-- The normal coefficient is defined by evaluating the difference on the
second coordinate vector. -/
def correctionCoefficient (data : NormalizedCovectors frames) (i p : D) : ℂ :=
  data.l₃ i p (0, 1) - data.l₁ i p (0, 1)

/-- The difference annihilates the tangent line by the two actual
restriction identities, rather than by a supplied factorization. -/
theorem annihilates_tangent (data : NormalizedCovectors frames) (i p : D)
    (hp : p ∈ D.chartDomain i) (z : ℂ) :
    (data.l₃ i p - data.l₁ i p) (z, 0) = 0 := by
  simp only [ContinuousLinearMap.sub_apply, data.tangent_l₃ i p hp,
    data.tangent_l₁ i p hp, sub_self]

/-- The honest quotient factorization, proved by decomposing an arbitrary
vector into a tangent vector and a multiple of the normal basis vector. -/
theorem factorization (data : NormalizedCovectors frames) (i p : D)
    (hp : p ∈ D.chartDomain i) (v : ℂ × ℂ) :
    data.l₃ i p v - data.l₁ i p v = data.correctionCoefficient i p * v.2 := by
  let δ : (ℂ × ℂ) →L[ℂ] ℂ := data.l₃ i p - data.l₁ i p
  have hdecomp : v = (v.1, 0) + v.2 • (0, 1) := by
    ext
    · simp
    · simp
  change δ v = data.correctionCoefficient i p * v.2
  calc
    δ v = δ ((v.1, 0) + v.2 • (0, 1)) := congrArg δ hdecomp
    _ = δ (v.1, 0) + v.2 • δ (0, 1) := by rw [map_add, map_smul]
    _ = data.correctionCoefficient i p * v.2 := by
      rw [data.annihilates_tangent i p hp]
      simp only [zero_add, smul_eq_mul, δ, ContinuousLinearMap.sub_apply,
        correctionCoefficient, mul_comm]

theorem coefficient_holomorphic (data : NormalizedCovectors frames) (i : D) :
    MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (data.correctionCoefficient i) (D.chartDomain i) := by
  simpa only [correctionCoefficient, sub_eq_add_neg] using
    (data.holomorphic_l₃ i (0, 1)).add (data.holomorphic_l₁ i (0, 1)).neg

/-- The covector transformation and the quotient part of the actual frame
change produce the Hom transition law for the constructed coefficient. -/
theorem coefficient_transition (data : NormalizedCovectors frames) (i j p : D)
    (hi : p ∈ D.chartDomain i) (hj : p ∈ D.chartDomain j) :
    data.correctionCoefficient j p =
      (T.transition i j p / N.transition i j p) * data.correctionCoefficient i p := by
  have hnormal : (frames.change i j p (0, 1)).2 = N.transition i j p := by
    simpa only [mul_one] using frames.normal i j p hi hj (0, 1)
  have hcross : data.correctionCoefficient j p * N.transition i j p =
      T.transition i j p * data.correctionCoefficient i p := by
    calc
      data.correctionCoefficient j p * N.transition i j p =
          data.l₃ j p (frames.change i j p (0, 1)) -
            data.l₁ j p (frames.change i j p (0, 1)) := by
        rw [data.factorization j p hj, hnormal]
      _ = T.transition i j p * data.correctionCoefficient i p := by
        rw [data.transform_l₃ i j p hi hj, data.transform_l₁ i j p hi hj]
        simp only [correctionCoefficient, mul_sub]
  have hN := N.nonzero i j p hi hj
  apply mul_right_cancel₀ hN
  rw [hcross]
  field_simp

/-- The section of the constructed Hom cocycle is constructed from the
covectors, with holomorphicity and compatibility proved above. -/
def normalQuotientSection (data : NormalizedCovectors frames) :
    (homCocycle N T).bundle.HolomorphicSection where
  coefficient := data.correctionCoefficient
  holomorphic := data.coefficient_holomorphic
  compatible := by
    intro i j p hi hj
    exact data.coefficient_transition i j p hi hj

@[simp] theorem normalQuotientSection_coefficient (data : NormalizedCovectors frames)
    (i p : D) : data.normalQuotientSection.coefficient i p =
      data.correctionCoefficient i p := rfl

/-- The universal negative-degree theorem applies to the constructed section;
no vanishing proposition is supplied as an input. -/
theorem correction_zero_of_negative_hom_degree (theory : LineBundleDegreeTheory)
    (data : NormalizedCovectors frames)
    (hnegative : theory.degree D (homCocycle N T).bundle < 0) :
    ∀ i p, p ∈ D.chartDomain i → data.correctionCoefficient i p = 0 := by
  exact theory.negative_degree_no_section D _ hnegative data.normalQuotientSection

theorem covectors_equal_of_negative_hom_degree (theory : LineBundleDegreeTheory)
    (data : NormalizedCovectors frames)
    (hnegative : theory.degree D (homCocycle N T).bundle < 0) :
    ∀ i p, p ∈ D.chartDomain i → data.l₁ i p = data.l₃ i p := by
  have hzero := data.correction_zero_of_negative_hom_degree theory hnegative
  intro i p hp
  apply ContinuousLinearMap.ext
  intro v
  have hfactor := data.factorization i p hp v
  rw [hzero i p hp, zero_mul] at hfactor
  exact (sub_eq_zero.mp hfactor).symm

/-- The normal tensor degree identity gives the negative Hom degree by the
previously proved arithmetic. Applying it to the newly constructed section
gives precisely the normalized covector equality needed in Lemma 3.1. -/
theorem covectors_equal_from_normal_tensor (theory : LineBundleDegreeTheory)
    (homLaw : HomDegreeLaw theory) (data : NormalizedCovectors frames)
    (n : ℕ) (hn : 2 ≤ n) (hN : theory.degree D N < 0)
    (htensor : (n : ℤ) * theory.degree D N = theory.degree D T) :
    ∀ i p, p ∈ D.chartDomain i → data.l₁ i p = data.l₃ i p := by
  apply data.covectors_equal_of_negative_hom_degree theory
  exact normal_hom_degree theory homLaw D N T (homCocycle N T) n hn hN htensor

end NormalizedCovectors

end Paper27.Geometry.NormalQuotient
