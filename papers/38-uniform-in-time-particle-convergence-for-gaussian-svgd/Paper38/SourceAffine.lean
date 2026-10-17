import Paper38.SourceFlowMeasurability
import Paper38.TransportParticleAffine
import Paper38.AffineLifting

/-!
# Complete source contracts for Lemmas 6.1 and 6.3

These statements use the literal projected particle equation, actual empirical
moments, the physical right-time derivative convention, actual transport
couplings, and the extremal eigenvalues of the empirical covariance itself.
The only ordinary external proof parameters are the named standard Baselines.
-/

noncomputable section
open MeasureTheory Set
open scoped Matrix MatrixOrder Matrix.Norms.Frobenius ENNReal NNReal Topology

namespace Paper38.SourceAffine
open Paper38.Model Paper38.Specification

variable {d N : ℕ} {V : E d → ℝ} {α β : ℝ}
set_option maxHeartbeats 800000

/-- The empirical moments of an actual particle path, with no independent
moment evolution inserted into the definition. -/
def empiricalMomentPath (X : ParticlePath d N) : MomentPath d :=
  ⟨fun t => empiricalMean (X t), fun t => empiricalCovariance (X t)⟩

/-- Source (6.1), including the principal initial value. -/
def IsFundamental (C : ℝ → Mat d) (L : ℝ → Mat d) : Prop :=
  L 0 = 1 ∧ ∀ t, 0 ≤ t → HasDerivWithinAt L (C t * L t) (Ici 0) t

/-- Exactly the two affine identities (6.2)--(6.3), at every physical time. -/
def AffineIdentities (X : ParticlePath d N) (L : ℝ → Mat d) : Prop :=
  ∀ t, 0 ≤ t →
    (∀ i, X t i = empiricalMean (X t) + matVec (L t) (X 0 i - empiricalMean (X 0))) ∧
    empiricalCovariance (X t) = L t * empiricalCovariance (X 0) * (L t).transpose

/-- Positive empirical covariance itself forces a nonempty cloud at positive
dimension, so the source contract needs no extra sample-size premise. -/
theorem sampleSize_pos_of_covariance_posDef (hd : 1 ≤ d)
    (x : Fin N → E d) (hx : (empiricalCovariance x).PosDef) : 0 < N := by
  letI : NeZero d := ⟨by omega⟩
  by_contra hN
  have hz : N = 0 := Nat.eq_zero_of_not_pos hN
  subst N
  have hunit : IsUnit (0 : Mat d) := by simpa [empiricalCovariance] using hx.isUnit
  exact not_isUnit_zero hunit

/-- The source sample-size endpoint follows from full rank as well. -/
theorem sampleSize_lower_of_covariance_posDef (hd : 1 ≤ d)
    (x : Fin N → E d) (hx : (empiricalCovariance x).PosDef) : d + 1 ≤ N :=
  ModelBridges.dimension_add_one_le_of_empiricalCovariance_posDef
    (sampleSize_pos_of_covariance_posDef hd x hx) x hx

/-- Closed moments with their original initial state and positive covariance. -/
theorem empirical_moments_solve (hV : AdmissiblePotential V α β)
    (x : Fin N → E d) (hx : (empiricalCovariance x).PosDef)
    (X : ParticlePath d N) (hX : IsParticlePathFrom V x X) :
    IsMomentPathFrom V (empiricalMean x) (empiricalCovariance x) (empiricalMomentPath X) := by
  have hN := sampleSize_pos_of_covariance_posDef hV.dimension x hx
  refine ⟨ModelBridges.particleSolution_momentSolution V hV.regularity hN X hX.1, ?_, ?_⟩
  · change empiricalMean (X 0) = _
    rw [hX.2]
  · change empiricalCovariance (X 0) = _
    rw [hX.2]

/-- Actual particle coefficients are continuous along any actual solution. -/
theorem particleCoefficient_continuousOn_path
    (extern : ExternalAnalyticInputs.Baselines d) (hV : AdmissiblePotential V α β)
    (x : Fin N → E d) (hx : (empiricalCovariance x).PosDef)
    (X : ParticlePath d N) (hX : IsParticlePathFrom V x X) :
    ContinuousOn (fun t => particleCoefficient V (X t)) (Ici 0) :=
  SourceFlowMeasurability.momentCoefficient_continuousOn_path extern.stein extern.sqrt hV
    (empiricalMomentPath X) (empirical_moments_solve hV x hx X hX).1

/-- Existence of a global invertible principal fundamental matrix and the
universal affine reconstruction for every solution of its linear ODE. -/
theorem fundamental_and_affine
    (extern : ExternalAnalyticInputs.Baselines d) (hV : AdmissiblePotential V α β)
    (x : Fin N → E d) (hx : (empiricalCovariance x).PosDef)
    (X : ParticlePath d N) (hX : IsParticlePathFrom V x X) :
    (∃ L : ℝ → Mat d, IsFundamental (fun t => particleCoefficient V (X t)) L ∧
      (∀ t, 0 ≤ t → IsUnit (L t))) ∧
    (∀ L : ℝ → Mat d, IsFundamental (fun t => particleCoefficient V (X t)) L →
      AffineIdentities X L) := by
  have hN := sampleSize_pos_of_covariance_posDef hV.dimension x hx
  have hC := particleCoefficient_continuousOn_path extern hV x hx X hX
  constructor
  · obtain ⟨L, hL0, hL, hunit⟩ := extern.fundamental (fun t => particleCoefficient V (X t)) hC
    exact ⟨L, ⟨hL0, hL⟩, hunit⟩
  · intro L hL t ht
    exact ⟨fun i => TransportParticleAffine.particle_affine_representation hN V X hX.1 hC L
        hL.1 hL.2 t ht i,
      TransportParticleAffine.particle_affine_covariance hN V X hX.1 hC L hL.1 hL.2 t ht⟩

/-- Full literal Lemma 6.1: a full-rank cloud has unique global actual particle
dynamics; every actual solution has exactly the closed moments and (6.2)--(6.3),
with a global invertible fundamental matrix. Representations hold for every L
solving (6.1), not just for a selected fundamental matrix. -/
def Lemma61 : Prop :=
  ∀ (d : ℕ) (V : E d → ℝ) (α β : ℝ), AdmissiblePotential V α β →
  ∀ (N : ℕ) (x : Fin N → E d), (empiricalCovariance x).PosDef →
    ParticleWellPosed V x ∧
    ∀ (X : ParticlePath d N), IsParticlePathFrom V x X →
      IsMomentPathFrom V (empiricalMean x) (empiricalCovariance x) (empiricalMomentPath X) ∧
      (∀ t, 0 ≤ t → (empiricalCovariance (X t)).PosDef) ∧
      (∃ L : ℝ → Mat d, IsFundamental (fun t => particleCoefficient V (X t)) L ∧
        (∀ t, 0 ≤ t → IsUnit (L t))) ∧
      (∀ L : ℝ → Mat d, IsFundamental (fun t => particleCoefficient V (X t)) L →
        AffineIdentities X L)

theorem lemma61 (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d) : Lemma61 := by
  intro d V α β hV N x hx
  have hN := sampleSize_pos_of_covariance_posDef hV.dimension x hx
  refine ⟨SourceFlowMeasurability.particleWellPosed (extern d) hV hN x hx, ?_⟩
  intro X hX
  have ha := fundamental_and_affine (extern d) hV x hx X hX
  exact ⟨empirical_moments_solve hV x hx X hX, hX.1.1, ha.1, ha.2⟩

section Spectral
variable [NeZero d]

/-- The actual minimum eigenvalue of S, represented as a nonnegative scalar. -/
def covarianceEigenMin (S : Mat d) (hS : S.PosDef) : ℝ≥0 :=
  ⟨AffineLifting.eigenMin S hS.isHermitian,
    AffineLifting.eigenMin_nonneg S hS.posSemidef⟩

/-- The actual maximum eigenvalue of S, represented as a nonnegative scalar. -/
def covarianceEigenMax (S : Mat d) (hS : S.PosDef) : ℝ≥0 :=
  ⟨AffineLifting.eigenMax S hS.isHermitian,
    AffineLifting.eigenMax_nonneg S hS.posSemidef⟩

lemma covarianceMin_eq (B S : Mat d) (hS : S.PosDef) (hcov : B * B.transpose = S) :
    AffineLifting.covarianceMin B = covarianceEigenMin S hS := by
  subst S
  rfl

lemma covarianceMax_eq (B S : Mat d) (hS : S.PosDef) (hcov : B * B.transpose = S) :
    AffineLifting.covarianceMax B = covarianceEigenMax S hS := by
  subst S
  rfl

/-- All contents of the source affine lifting at one time, including the two
actual pushforward laws and the actual spectral constants in (6.12). -/
def AffineLiftAt (x : Fin N → E d) (X : ParticlePath d N) (W B : Mat d)
    (t : ℝ) (hS : (empiricalCovariance (X t)).PosDef) : Prop :=
  IsUnit B ∧ B * B.transpose = empiricalCovariance (X t) ∧
  (∀ i, X t i = empiricalMean (X t) + matVec B (standardizedCloud x W i)) ∧
  empiricalLaw (X t) = (empiricalLaw (standardizedCloud x W)).map
    (fun z => empiricalMean (X t) + matVec B z) ∧
  gaussianLaw (empiricalMean (X t)) (covarianceRoot (empiricalCovariance (X t))) =
    (standardGaussian d).map (fun z => empiricalMean (X t) + matVec B z) ∧
  ((covarianceEigenMin (empiricalCovariance (X t)) hS : ℝ≥0∞) *
      Transport.w2sq (empiricalLaw (standardizedCloud x W)) (standardGaussian d) ≤
    Transport.w2sq (empiricalLaw (X t))
      (gaussianLaw (empiricalMean (X t)) (covarianceRoot (empiricalCovariance (X t))))) ∧
  (Transport.w2sq (empiricalLaw (X t))
      (gaussianLaw (empiricalMean (X t)) (covarianceRoot (empiricalCovariance (X t)))) ≤
    (covarianceEigenMax (empiricalCovariance (X t)) hS : ℝ≥0∞) *
      Transport.w2sq (empiricalLaw (standardizedCloud x W)) (standardGaussian d))

/-- The source affine identities and actual matrix spectral lifting together
prove the full two-sided lifting, for any source whitening coordinates. -/
theorem affineLiftAt_of_fundamental
    (hV : AdmissiblePotential V α β) (x : Fin N → E d)
    (hx : (empiricalCovariance x).PosDef) (X : ParticlePath d N)
    (hX : IsParticlePathFrom V x X) (L : ℝ → Mat d)
    (haff : AffineIdentities X L) (hunit : ∀ t, 0 ≤ t → IsUnit (L t))
    (W : Mat d) (hW : IsWhitening x W) (t : ℝ) (ht : 0 ≤ t) :
    AffineLiftAt x X W (L t * W⁻¹) t (hX.1.1 t ht) := by
  have hN := sampleSize_pos_of_covariance_posDef hV.dimension x hx
  let B := L t * W⁻¹
  let m := empiricalMean (X t)
  let z := standardizedCloud x W
  have hB : IsUnit B := (hunit t ht).mul
    (Matrix.isUnit_nonsing_inv_iff.mpr (TransportParticleAffine.whitening_isUnit x W hW))
  have ha := haff t ht
  rw [hX.2] at ha
  have hs := TransportParticleAffine.standardized_affine_lift x W (L t) hW m
  have hcov : B * B.transpose = empiricalCovariance (X t) := hs.2.trans ha.2.symm
  have heach (i : Fin N) : X t i = m + matVec B (z i) := (ha.1 i).trans (hs.1 i)
  have heq : X t = fun i => m + matVec B (z i) := funext heach
  have hmap : empiricalLaw (X t) = (empiricalLaw z).map (fun u => m + matVec B u) := by
    have h := AffineLifting.empiricalLaw_map hN z (fun u => m + matVec B u)
      (continuous_const.add (GaussianCoupling.continuous_matVec B)).measurable
    rw [← heq] at h
    exact h.symm
  have hgauss : gaussianLaw m (covarianceRoot (empiricalCovariance (X t))) =
      (standardGaussian d).map (fun u => m + matVec B u) := by
    change gaussianLaw m (covarianceRoot (empiricalCovariance (X t))) = gaussianLaw m B
    rw [GaussianAffine.gaussianLaw_eq_covarianceRoot m B, hcov]
  have hb := AffineLifting.empirical_affine_two_sided hN z m B hB
  rw [← heq, hcov,
    covarianceMin_eq B (empiricalCovariance (X t)) (hX.1.1 t ht) hcov,
    covarianceMax_eq B (empiricalCovariance (X t)) (hX.1.1 t ht) hcov] at hb
  exact ⟨hB, hcov, heach, hmap, hgauss, hb.1, hb.2⟩

end Spectral

/-- A canonical whitening exists for every full-rank cloud; arbitrary other
whitenings are retained in the source lifting contract below. -/
theorem principal_whitening (x : Fin N → E d) (hx : (empiricalCovariance x).PosDef) :
    IsWhitening x (covarianceRoot (empiricalCovariance x))⁻¹ := by
  let H := covarianceRoot (empiricalCovariance x)
  have hH : H.PosDef := hx.posDef_sqrt
  have hsym : H.transpose = H := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hH.isHermitian.eq
  have hd := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hs : H * H = empiricalCovariance x :=
    CFC.sqrt_mul_sqrt_self _ hx.posSemidef.nonneg
  change H⁻¹ * empiricalCovariance x * (H⁻¹).transpose = 1
  calc
    H⁻¹ * empiricalCovariance x * (H⁻¹).transpose = H⁻¹ * (H * H) * H⁻¹ := by
      rw [hs, Matrix.transpose_nonsing_inv, hsym]
    _ = (H⁻¹ * H) * (H * H⁻¹) := by noncomm_ring
    _ = 1 := by rw [Matrix.nonsing_inv_mul H hd, Matrix.mul_nonsing_inv H hd, Matrix.one_mul]

/-- Complete source Lemma 6.3. The dimension proof is exactly d≥1; all constants
are the genuine current covariance eigenvalues, with no supplied spectral or
transport bounds. Whitenings are arbitrary and independent of physical time. -/
def Lemma63 : Prop :=
  ∀ (d : ℕ) (V : E d → ℝ) (α β : ℝ) (hV : AdmissiblePotential V α β),
  letI : NeZero d := ⟨by have := hV.dimension; omega⟩
  ∀ (N : ℕ) (x : Fin N → E d), (empiricalCovariance x).PosDef →
    (∃ W : Mat d, IsWhitening x W) ∧
    ∀ (X : ParticlePath d N) (hX : IsParticlePathFrom V x X) (W : Mat d), IsWhitening x W →
      (empiricalMean (standardizedCloud x W) = 0 ∧
        empiricalCovariance (standardizedCloud x W) = 1) ∧
      ∃ B : ℝ → Mat d, ∀ t, ∀ ht : 0 ≤ t,
        AffineLiftAt x X W (B t) t (hX.1.1 t ht)

theorem lemma63 (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d) : Lemma63 := by
  intro d V α β hV
  letI : NeZero d := ⟨by have := hV.dimension; omega⟩
  intro N x hx
  have hN := sampleSize_pos_of_covariance_posDef hV.dimension x hx
  refine ⟨⟨_, principal_whitening x hx⟩, ?_⟩
  intro X hX W hW
  obtain ⟨⟨L, hL, hunit⟩, haff⟩ := fundamental_and_affine (extern d) hV x hx X hX
  refine ⟨ModelBridges.standardizedCloud_moments hN x W hW, ?_⟩
  refine ⟨fun t => L t * W⁻¹, fun t ht => ?_⟩
  exact affineLiftAt_of_fundamental hV x hx X hX L (haff L hL) hunit W hW t ht


end Paper38.SourceAffine
