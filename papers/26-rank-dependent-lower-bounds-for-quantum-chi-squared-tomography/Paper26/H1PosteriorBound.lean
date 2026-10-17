import Paper26.FisherVolume
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Weak H¹ roots and the posterior success bound

`WeakH1Root` uses actual L² functions on Euclidean Lebesgue space and actual
weak derivatives, characterized by integration by parts against every C∞
compactly supported scalar test function in each orthonormal coordinate.

Two known external analytic inputs are explicit, separate propositions:
* `TalentiH1SharpInput` is the sharp Sobolev inequality of Talenti (1976),
  extended from smooth functions to H¹ by Meyers–Serrin (1964) and the standard
  whole-space cutoff argument.
* `TalentiCoarseInput` is the independent scalar specialization `S_p ≤ 4/p`.
  This coarse inequality is not presented as the literal statement in Talenti.
Neither proposition is installed as an axiom or proved here.

The concentration argument (Lemma 3.1) and arbitrary-outcome averaging argument
(Corollary 3.3) are proved from those analytic inputs. The general posterior
information identity of Lemma 3.2 is an explicitly named separate premise. It
is not claimed to be an external theorem already verified for these objects.
-/

noncomputable section
open scoped ENNReal NNReal
open MeasureTheory Set

namespace Paper26.H1PosteriorBound

abbrev ParameterSpace (p : ℕ) := EuclideanSpace ℝ (Fin p)

/-- A compactly supported weak H¹ real root. The integration-by-parts field
includes integrability of both test products, so the equality cannot hold only
because a Bochner integral of a nonintegrable function was totalized to zero.
The derivative is a field of real continuous linear functionals; in Euclidean
space its operator norm is the Euclidean weak-gradient norm. -/
structure WeakH1Root (p : ℕ) where
  root : ParameterSpace p → ℝ
  weakDerivative : ParameterSpace p → (ParameterSpace p →L[ℝ] ℝ)
  root_memLp : MemLp root 2 volume
  weakDerivative_memLp : MemLp weakDerivative 2 volume
  compact_support : HasCompactSupport root
  test_integration_by_parts :
    ∀ (φ : ParameterSpace p → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∀ i : Fin p,
        Integrable (fun x => root x *
          fderiv ℝ φ x (EuclideanSpace.basisFun (Fin p) ℝ i)) volume ∧
        Integrable (fun x => weakDerivative x (EuclideanSpace.basisFun (Fin p) ℝ i) *
          φ x) volume ∧
        (∫ x, root x * fderiv ℝ φ x (EuclideanSpace.basisFun (Fin p) ℝ i)) =
          -(∫ x, weakDerivative x (EuclideanSpace.basisFun (Fin p) ℝ i) * φ x)

namespace WeakH1Root
variable {p : ℕ}

/-- The actual nonnegative density represented by the root. -/
def density (h : WeakH1Root p) (x : ParameterSpace p) : ℝ := h.root x ^ (2 : ℕ)

/-- Actual Lebesgue mass of the squared-root density. -/
def mass (h : WeakH1Root p) (s : Set (ParameterSpace p)) : ℝ≥0∞ :=
  ∫⁻ x in s, ENNReal.ofReal (h.root x ^ (2 : ℕ))

/-- Squared L² energy of the actual weak derivative. -/
def energy (h : WeakH1Root p) : ℝ≥0∞ :=
  ∫⁻ x, ‖h.weakDerivative x‖ₑ ^ (2 : ℕ)

/-- The root-gradient definition of Fisher information from Section 3.1. -/
def fisher (h : WeakH1Root p) : ℝ≥0∞ := 4 * h.energy

theorem root_aestronglyMeasurable (h : WeakH1Root p) :
    AEStronglyMeasurable h.root volume := h.root_memLp.aestronglyMeasurable

theorem derivative_aestronglyMeasurable (h : WeakH1Root p) :
    AEStronglyMeasurable h.weakDerivative volume :=
  h.weakDerivative_memLp.aestronglyMeasurable

theorem mass_eq_rootMass (h : WeakH1Root p) (s : Set (ParameterSpace p)) :
    h.mass s = FisherVolume.rootMass volume h.root s :=
  (FisherVolume.rootMass_eq_lintegral_sq volume h.root s).symm

theorem mass_mono (h : WeakH1Root p) {s t : Set (ParameterSpace p)} (hst : s ⊆ t) :
    h.mass s ≤ h.mass t := lintegral_mono_set hst

theorem energy_ne_top (h : WeakH1Root p) : h.energy ≠ ∞ := by
  have he : h.energy = eLpNorm h.weakDerivative 2 volume ^ (2 : ℕ) := by
    unfold energy
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using
      (eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := h.weakDerivative)
        (p := (2 : ℝ≥0)) (by norm_num)).symm
  rw [he]
  exact ENNReal.pow_ne_top h.weakDerivative_memLp.eLpNorm_lt_top.ne

end WeakH1Root

/-- Squared sharp p=2 Sobolev constant in real dimension p ≥ 3:
`[π p (p-2)]⁻¹ [Γ(p)/Γ(p/2)]^(2/p)`.

Talenti, *Best constant in Sobolev inequality*, Ann. Mat. Pura Appl. 110
(1976), 353–372, main theorem (1)–(3), pp. 353–354,
DOI 10.1007/BF02418013. -/
def talentiSquaredConstant (p : ℕ) : ℝ :=
  (Real.pi * (p : ℝ) * ((p : ℝ) - 2))⁻¹ *
    (Real.Gamma (p : ℝ) / Real.Gamma ((p : ℝ) / 2)) ^ (2 / (p : ℝ))

/-- Explicit known external sharp Sobolev input for the actual weak H¹ objects.
The H¹ extension invokes Meyers–Serrin, *H = W*, PNAS 51(6) (1964), 1055–1056,
DOI 10.1073/pnas.51.6.1055, with a whole-space cutoff argument. This proposition
is a parameter of the subsequent theorems, never a new Lean axiom. -/
def TalentiH1SharpInput (p : ℕ) : Prop :=
  ∀ h : WeakH1Root p,
    eLpNorm h.root (FisherVolume.criticalExponent p) volume ^ (2 : ℕ) ≤
      ENNReal.ofReal (talentiSquaredConstant p) * h.energy

/-- Separate, explicitly unformalized scalar consequence of the sharp constant.
It is not the concentration or posterior-success conclusion. -/
def TalentiCoarseInput (p : ℕ) : Prop :=
  ENNReal.ofReal (talentiSquaredConstant p) ≤ (4 : ℝ≥0∞) / (p : ℝ≥0∞)

/-- A consequence of the two disclosed external analytic inputs. -/
theorem critical_norm_sq_le_coarse_energy {p : ℕ}
    (hs : TalentiH1SharpInput p) (hc : TalentiCoarseInput p) (h : WeakH1Root p) :
    eLpNorm h.root (FisherVolume.criticalExponent p) volume ^ (2 : ℕ) ≤
      ((4 : ℝ≥0∞) / (p : ℝ≥0∞)) * h.energy :=
  (hs h).trans (mul_le_mul_right' hc h.energy)

/-- Lemma 3.1: actual Lebesgue density mass versus volume and weak Fisher
energy. Only the two precisely disclosed classical analytic inputs are assumed;
the Hölder/concentration conversion is proved. -/
theorem fisher_volume_bound {p : ℕ} (hp : 3 ≤ p)
    (hs : TalentiH1SharpInput p) (hc : TalentiCoarseInput p)
    (h : WeakH1Root p) (s : Set (ParameterSpace p)) :
    h.mass s ≤ volume s ^ (2 / (p : ℝ)) / (p : ℝ≥0∞) * h.fisher := by
  have hexp : 1 - 2 / (FisherVolume.criticalExponent p : ℝ) = 2 / (p : ℝ) := by
    rw [div_eq_mul_inv, FisherVolume.criticalExponent_inv hp]
    ring
  calc
    h.mass s ≤ volume s ^ (2 / (p : ℝ)) *
        eLpNorm h.root (FisherVolume.criticalExponent p) volume ^ (2 : ℕ) := by
      rw [h.mass_eq_rootMass]
      simpa only [hexp] using
        (FisherVolume.rootMass_le_measure_mul_eLpNorm_sq volume
          h.root_aestronglyMeasurable s (FisherVolume.two_le_criticalExponent hp))
    _ ≤ volume s ^ (2 / (p : ℝ)) *
        (((4 : ℝ≥0∞) / (p : ℝ≥0∞)) * h.energy) :=
      mul_le_mul_left' (critical_norm_sq_le_coarse_energy hs hc h) _
    _ = volume s ^ (2 / (p : ℝ)) / (p : ℝ≥0∞) * h.fisher := by
      unfold WeakH1Root.fisher
      simp only [div_eq_mul_inv]
      ac_rfl

/-- A volume budget may replace the actual volume of the concentration set. -/
theorem fisher_volume_bound_of_volume_le {p : ℕ} (hp : 3 ≤ p)
    (hs : TalentiH1SharpInput p) (hc : TalentiCoarseInput p)
    (h : WeakH1Root p) (s : Set (ParameterSpace p)) {v : ℝ≥0∞}
    (hv : volume s ≤ v) :
    h.mass s ≤ v ^ (2 / (p : ℝ)) / (p : ℝ≥0∞) * h.fisher := by
  refine (fisher_volume_bound hp hs hc h s).trans ?_
  have hpow := ENNReal.rpow_le_rpow hv
    (show 0 ≤ 2 / (p : ℝ) by positivity)
  simpa only [div_eq_mul_inv] using
    mul_le_mul_right' (mul_le_mul_right' hpow (p : ℝ≥0∞)⁻¹) h.fisher

section Posterior
variable {p : ℕ} {Y : Type*} [MeasurableSpace Y]

/-- Prior-average success as an actual outcome integral of the marginal times
the posterior density's mass on the output's successful parameter set. -/
def posteriorSuccess (ν : Measure Y) (m : Y → ℝ≥0∞)
    (posterior : Y → WeakH1Root p) (s : Y → Set (ParameterSpace p)) : ℝ≥0∞ :=
  ∫⁻ y, m y * (posterior y).mass (s y) ∂ν

/-- Actual marginal-weighted expected posterior Fisher information. -/
def expectedPosteriorFisher (ν : Measure Y) (m : Y → ℝ≥0∞)
    (posterior : Y → WeakH1Root p) : ℝ≥0∞ :=
  ∫⁻ y, m y * (posterior y).fisher ∂ν

/-- The general Lemma 3.2 identity, explicitly left as a preceding obligation.
This is not asserted here for arbitrary weak likelihoods or continuous POVMs;
only the averaging implication below is proved. -/
def GeneralPosteriorInformationIdentity (ν : Measure Y) (m : Y → ℝ≥0∞)
    (posterior : Y → WeakH1Root p) (priorI dataI : ℝ≥0∞) : Prop :=
  expectedPosteriorFisher ν m posterior = priorI + dataI

/-- Corollary 3.3's genuine posterior-averaging step for an arbitrary outcome
measure. Weighted Fisher measurability is the exact condition used to pull the
possibly infinite ENNReal coefficient through the integral. No finiteness
assumption is hidden: this extended-integral inequality also holds with an
infinite right-hand side. The general information identity remains a named
Lemma 3.2 premise. -/
theorem posterior_success_bound_of_identity
    (hp : 3 ≤ p) (hs : TalentiH1SharpInput p) (hc : TalentiCoarseInput p)
    (ν : Measure Y) (m : Y → ℝ≥0∞) (posterior : Y → WeakH1Root p)
    (s : Y → Set (ParameterSpace p)) {v priorI dataI : ℝ≥0∞}
    (hv : ∀ᵐ y ∂ν, volume (s y) ≤ v)
    (hF : AEMeasurable (fun y => m y * (posterior y).fisher) ν)
    (hidentity : GeneralPosteriorInformationIdentity ν m posterior priorI dataI) :
    posteriorSuccess ν m posterior s ≤
      v ^ (2 / (p : ℝ)) / (p : ℝ≥0∞) * (priorI + dataI) := by
  let c : ℝ≥0∞ := v ^ (2 / (p : ℝ)) / (p : ℝ≥0∞)
  have hpoint : ∀ᵐ y ∂ν,
      m y * (posterior y).mass (s y) ≤ c * (m y * (posterior y).fisher) := by
    filter_upwards [hv] with y hy
    calc
      m y * (posterior y).mass (s y) ≤ m y * (c * (posterior y).fisher) :=
        mul_le_mul_left' (fisher_volume_bound_of_volume_le hp hs hc _ _ hy) _
      _ = c * (m y * (posterior y).fisher) := by ac_rfl
  calc
    posteriorSuccess ν m posterior s ≤
        ∫⁻ y, c * (m y * (posterior y).fisher) ∂ν := lintegral_mono_ae hpoint
    _ = c * expectedPosteriorFisher ν m posterior := lintegral_const_mul'' c hF
    _ = c * (priorI + dataI) := by rw [hidentity]

/-- When the marginal and the nonzero-marginal posteriors are normalized, the
same integral really is bounded by one, as a success probability must be. -/
theorem posteriorSuccess_le_one_of_normalized
    (ν : Measure Y) (m : Y → ℝ≥0∞) (posterior : Y → WeakH1Root p)
    (s : Y → Set (ParameterSpace p))
    (hm : (∫⁻ y, m y ∂ν) = 1)
    (hpost : ∀ᵐ y ∂ν, m y ≠ 0 → (posterior y).mass univ = 1) :
    posteriorSuccess ν m posterior s ≤ 1 := by
  have hpoint : ∀ᵐ y ∂ν, m y * (posterior y).mass (s y) ≤ m y := by
    filter_upwards [hpost] with y hy
    by_cases hz : m y = 0
    · simp [hz]
    have hmass : (posterior y).mass (s y) ≤ 1 := by
      calc
        (posterior y).mass (s y) ≤ (posterior y).mass univ :=
          (posterior y).mass_mono (subset_univ _)
        _ = 1 := hy hz
    simpa only [mul_one] using mul_le_mul_left' hmass (m y)
  exact (lintegral_mono_ae hpoint).trans_eq hm

end Posterior
end Paper26.H1PosteriorBound
