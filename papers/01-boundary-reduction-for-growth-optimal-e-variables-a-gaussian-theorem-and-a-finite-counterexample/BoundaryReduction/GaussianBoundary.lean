import BoundaryReduction.GaussianMeasure
import BoundaryReduction.FinitePriorApprox

open Real Set MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ}

/-- The optimizer and expected-log assertions of Theorem 4.1, in the centered
Gaussian precision model. Finite-information/GROW equalities are separate claims. -/
theorem theorem_4_1_optimizer
    (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
    (hcenter : (∫ x, x ∂Z) = 0)
    (hvariance : ∀ v : Space d, variance (precisionForm K v) Z = inner ℝ v (K v))
    (hsym : ∀ u v : Space d, inner ℝ u (K v) = inner ℝ v (K u))
    (hsurj : Function.Surjective K)
    (B : Set (Space d)) (hd : 1 ≤ d) (hB : IsOpen B) (h0 : (0 : Space d) ∈ B)
    (hbounded : Bornology.IsBounded B) :
    ∃ (W : ProbabilityMeasure (frontier B)) (c : ℝ),
      c = (klDiv (mixtureMeasure K Z W) Z).toReal ∧ 0 < c ∧
      klDiv (mixtureMeasure K Z W) Z ≠ ∞ ∧
      (∀ V : ProbabilityMeasure (frontier B), klDiv (mixtureMeasure K Z W) Z ≤ klDiv (mixtureMeasure K Z V) Z) ∧
      (∀ V : ProbabilityMeasure (frontier B),
        (∀ U : ProbabilityMeasure (frontier B), klDiv (mixtureMeasure K Z V) Z ≤ klDiv (mixtureMeasure K Z U) Z) → V = W) ∧
      (∀ μ : Space d, μ ∉ B → c ≤ expectedLog K (W : Measure (frontier B)) Z μ) ∧
      (∀ r ∈ (W : Measure (frontier B)).support, expectedLog K (W : Measure (frontier B)) Z (r : Space d) = c) ∧
      (∫ x, likelihood K (W : Measure (frontier B)) x ∂Z) = 1 := by
  have hc := compact_nonempty_boundary hd hB h0 hbounded
  letI : CompactSpace (frontier B) := isCompact_iff_compactSpace.mp hc.1
  obtain ⟨R,hRpos,hR⟩ := hc.1.isBounded.exists_pos_norm_le
  let Rn : ℝ≥0 := ⟨R,hRpos.le⟩
  have hRn : ∀ r : frontier B, ‖(r : Space d)‖ ≤ Rn := fun r => hR r r.2
  have hcov := precision_covariance_identity K Z hvariance hsym hsurj
  have hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v) := by
    intro v
    rw [← hvariance]
    exact variance_nonneg _ _
  obtain ⟨W,hW,huniq⟩ := exists_unique_kl_minimizer K Z hcenter hcov hc.2 Rn hRn hK
  have hmin := (entropy_min_iff_kl_min K Z hcenter hcov W Rn hRn hK).mpr hW
  have hnot : (0 : Space d) ∉ frontier B := by
    intro hr
    exact hr.2 (by simpa only [hB.interior_eq] using h0)
  have hpos := mixtureEntropy_pos K Z hcenter hcov W Rn hRn hK hnot
  refine ⟨W,mixtureEntropy K Z W,?_,hpos,
    mixture_klDiv_ne_top K Z hcenter hvariance W Rn hRn hK,hW,huniq,
    minimizer_exterior_inequality K Z hcenter hcov hB h0 W Rn hRn hmin,
    minimizer_support_equalization K Z hcenter hcov W Rn hRn hK hmin,
    integral_likelihood K Z hcenter hvariance (W : Measure (frontier B))⟩
  rw [mixture_klDiv K Z hcenter hvariance W Rn hRn hK, ENNReal.toReal_ofReal hpos.le]

end BoundaryReduction.Gaussian
