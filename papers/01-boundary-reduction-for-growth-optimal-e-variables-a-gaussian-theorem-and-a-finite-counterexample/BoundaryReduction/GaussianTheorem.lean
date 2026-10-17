import BoundaryReduction.GaussianCovariance
import BoundaryReduction.GaussianApproximation

open Real Set MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ}

/-- All assertions of Theorem 4.1, including finite-mixture information,
maximin growth over all nonnegative e-variables, and attainment. -/
def BoundaryConclusion (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) (B : Set (Space d)) : Prop :=
  ∃ (W : ProbabilityMeasure (frontier B)) (c : ℝ),
    0 < c ∧ klDiv (mixtureMeasure K Z W) Z ≠ ∞ ∧
    c = (klDiv (mixtureMeasure K Z W) Z).toReal ∧
    (∀ V : ProbabilityMeasure (frontier B), klDiv (mixtureMeasure K Z W) Z ≤ klDiv (mixtureMeasure K Z V) Z) ∧
    (∀ V : ProbabilityMeasure (frontier B),
      (∀ U : ProbabilityMeasure (frontier B), klDiv (mixtureMeasure K Z V) Z ≤ klDiv (mixtureMeasure K Z U) Z) → V = W) ∧
    gaussianGrowth Z Bᶜ = (↑c : EReal) ∧
    finiteInformation K Z Bᶜ = ENNReal.ofReal c ∧
    finiteInformation K Z (frontier B) = ENNReal.ofReal c ∧
    (∀ μ : Space d, μ ∉ B → c ≤ expectedLog K (W : Measure (frontier B)) Z μ) ∧
    (∀ r ∈ (W : Measure (frontier B)).support, expectedLog K (W : Measure (frontier B)) Z (r : Space d) = c) ∧
    (∀ F : FinitePrior Bᶜ,
      klDiv (F.finiteMixture K Z) Z ≠ ∞ ∧
      klDiv (F.finiteMixture K Z) (mixtureMeasure K Z W) ≠ ∞ ∧
      (klDiv (F.finiteMixture K Z) (mixtureMeasure K Z W)).toReal+c ≤
        (klDiv (F.finiteMixture K Z) Z).toReal) ∧
    ∃ S : MeasureEVar Z, (∀ x, S.value x = likelihood K (W : Measure (frontier B)) x) ∧
      (∫ x, S.value x ∂Z) = 1 ∧
      (⨅ μ : ↥(Bᶜ), MeasureGrow.logExpectation (locationLaw Z (μ : Space d)) S.value) = (↑c : EReal)

/-- Theorem 4.1 in centered Gaussian precision coordinates. -/
theorem theorem_4_1
    (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
    (hcenter : (∫ x, x ∂Z) = 0)
    (hvariance : ∀ v : Space d, variance (precisionForm K v) Z = inner ℝ v (K v))
    (hsym : ∀ u v : Space d, inner ℝ u (K v) = inner ℝ v (K u))
    (hsurj : Function.Surjective K)
    (B : Set (Space d)) (hd : 1 ≤ d) (hB : IsOpen B) (h0 : (0 : Space d) ∈ B)
    (hbounded : Bornology.IsBounded B) : BoundaryConclusion K Z B := by
  obtain ⟨W,c,hc,hpos,hfin,hmin,huniq,hglob,heq,hnorm⟩ :=
    theorem_4_1_optimizer K Z hcenter hvariance hsym hsurj B hd hB h0 hbounded
  have hcompact := compact_nonempty_boundary hd hB h0 hbounded
  letI : CompactSpace (frontier B) := isCompact_iff_compactSpace.mp hcompact.1
  obtain ⟨R,hRpos,hR⟩ := hcompact.1.isBounded.exists_pos_norm_le
  let Rn : ℝ≥0 := ⟨R,hRpos.le⟩
  have hRn : ∀ r : frontier B, ‖(r : Space d)‖ ≤ Rn := fun r => hR r r.2
  have hcov := precision_covariance_identity K Z hvariance hsym hsurj
  have hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v) := fun v => by
    rw [← hvariance]; exact variance_nonneg _ _
  have hminF := (entropy_min_iff_kl_min K Z hcenter hcov W Rn hRn hK).mpr hmin
  have hcF : c = mixtureEntropy K Z W := by
    rw [hc,mixture_klDiv K Z hcenter hvariance W Rn hRn hK,
      ENNReal.toReal_ofReal (mixtureEntropy_nonneg K Z hcenter hvariance W Rn hRn hK)]
  have hinfo := theorem_4_1_information K Z hcenter hcov hB h0 hcompact.2 W Rn hRn hK hminF
  have hgrow := theorem_4_1_growth K Z hcenter hcov hB h0 hcompact.2 W Rn hRn hK hminF
  refine ⟨W,c,hpos,hfin,hc,hmin,huniq,?_,?_,?_,hglob,heq,?_,?_⟩
  · simpa only [hcF] using hgrow.1
  · simpa only [hcF] using hinfo.1
  · simpa only [hcF] using hinfo.2
  · intro F
    have hpy := finite_pythagorean K Z hcenter hcov W hK F
    exact ⟨hpy.1,hpy.2.1,by
      rw [hcF]
      exact theorem_4_1_pythagorean K Z hcenter hcov hB h0 W Rn hRn hminF F⟩
  · refine ⟨mixtureEVar K Z hcenter hcov W Rn hRn,fun _ => rfl,hnorm,?_⟩
    simpa only [hcF] using hgrow.2

/-- Theorem 4.1 for N(0,SigmaOp), with SigmaOp symmetric positive definite. Its inverse K
is constructed, and the location laws are the genuine translated Gaussian laws. -/
theorem theorem_4_1_covariance
    (SigmaOp : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
    (hcenter : (∫ x, x ∂Z) = 0)
    (hsymSigmaOp : ∀ u v : Space d, inner ℝ u (SigmaOp v) = inner ℝ v (SigmaOp u))
    (hposSigmaOp : ∀ v : Space d, v ≠ 0 → 0 < inner ℝ v (SigmaOp v))
    (hcovSigmaOp : ∀ u v : Space d, covariance (innerSL ℝ u) (innerSL ℝ v) Z = inner ℝ u (SigmaOp v))
    (B : Set (Space d)) (hd : 1 ≤ d) (hB : IsOpen B) (h0 : (0 : Space d) ∈ B)
    (hbounded : Bornology.IsBounded B) :
    ∃ K : Space d →L[ℝ] Space d, (∀ v, SigmaOp (K v) = v) ∧ (∀ v, K (SigmaOp v) = v) ∧ BoundaryConclusion K Z B := by
  obtain ⟨K,hSigmaOpK,hKSigmaOp,hsym,hsurj,hvar⟩ := exists_precision_of_covariance SigmaOp Z hsymSigmaOp hposSigmaOp hcovSigmaOp
  exact ⟨K,hSigmaOpK,hKSigmaOp,theorem_4_1 K Z hcenter hvar hsym hsurj B hd hB h0 hbounded⟩

end BoundaryReduction.Gaussian
