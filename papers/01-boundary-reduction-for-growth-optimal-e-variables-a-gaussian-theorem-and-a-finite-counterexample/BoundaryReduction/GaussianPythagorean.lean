import BoundaryReduction.GaussianRelativeKL

open Real Set MeasureTheory ProbabilityTheory InformationTheory BigOperators
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
include hcenter hcov

/-- The actual KL chain rule for an arbitrary finite Gaussian mixture and a compact Borel mixture. -/
theorem finite_pythagorean (W : ProbabilityMeasure Γ)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) {C : Set (Space d)} (F : FinitePrior C) :
    klDiv (F.finiteMixture K Z) Z ≠ ∞ ∧
    klDiv (F.finiteMixture K Z) (mixtureMeasure K Z W) ≠ ∞ ∧
    (klDiv (F.finiteMixture K Z) Z).toReal =
      (klDiv (F.finiteMixture K Z) (mixtureMeasure K Z W)).toReal+
        ∑ i, F.weights.w i*expectedLog K (W : Measure Γ) Z (F.mean i) := by
  let D := Γ ∪ Set.range F.mean
  have hD : IsCompact D := (isCompact_iff_compactSpace.mpr inferInstance).union (Set.finite_range F.mean).isCompact
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
  have hΓD : Γ ⊆ D := Set.subset_union_left
  have hFD : ∀ i, F.mean i ∈ D := fun i => Or.inr ⟨i,rfl⟩
  let W' := liftPrior hΓD W
  let F' := F.asPrior hFD
  obtain ⟨S,hSpos,hS⟩ := hD.isBounded.exists_pos_norm_le
  let Sn : ℝ≥0 := ⟨S,hSpos.le⟩
  have hSn : ∀ r : D, ‖(r : Space d)‖ ≤ Sn := fun r => hS r r.2
  have hvar := precision_variance_of_covariance K Z hcenter hcov
  have hFQ : mixtureMeasure K Z F' = F.finiteMixture K Z := F.mixture_asPrior K Z hFD
  have hWQ : mixtureMeasure K Z W' = mixtureMeasure K Z W := mixture_lift K Z hΓD W
  have hn := mixture_klDiv_ne_top K Z hcenter hvar F' Sn hSn hK
  have hr := relative_klDiv K Z hcenter hcov F' W' Sn hSn hK
  have hrfin : klDiv (mixtureMeasure K Z F') (mixtureMeasure K Z W') ≠ ∞ := by rw [hr]; exact ENNReal.ofReal_ne_top
  rw [hFQ] at hn
  rw [hFQ,hWQ] at hrfin
  refine ⟨hn,hrfin,?_⟩
  have hp := mixture_pythagorean K Z hcenter hcov F' W' Sn hSn hK
  have hleft : (klDiv (mixtureMeasure K Z F') Z).toReal = mixtureEntropy K Z F' := by
    rw [mixture_klDiv K Z hcenter hvar F' Sn hSn hK,
      ENNReal.toReal_ofReal (mixtureEntropy_nonneg K Z hcenter hvar F' Sn hSn hK)]
  rw [← hleft,hFQ,hWQ] at hp
  have heq : (∫ r : D, expectedLog K (W' : Measure D) Z (r : Space d) ∂(F' : Measure D)) =
      ∑ i, F.weights.w i*expectedLog K (W : Measure Γ) Z (F.mean i) := by
    dsimp [F']
    rw [FinitePrior.integral_asPrior F hFD (fun r : D => expectedLog K (W' : Measure D) Z (r : Space d))
      ((lipschitz_expectedLog K Z W' Sn hSn).continuous.comp continuous_subtype_val)]
    apply Finset.sum_congr rfl
    intro i _
    rw [show expectedLog K (W' : Measure D) Z (F.mean i) =
      expectedLog K (W : Measure Γ) Z (F.mean i) from expectedLog_lift K Z hΓD W _]
  rwa [heq] at hp

/-- Theorem 4.1, Pythagorean inequality (4.5) for every genuine finite exterior mixture. -/
theorem theorem_4_1_pythagorean {B : Set (Space d)} [CompactSpace (frontier B)]
    (hB : IsOpen B) (h0 : (0 : Space d) ∈ B) (W : ProbabilityMeasure (frontier B))
    (R : ℝ≥0) (hR : ∀ r : frontier B, ‖(r : Space d)‖ ≤ R)
    (hmin : ∀ V : ProbabilityMeasure (frontier B), mixtureEntropy K Z W ≤ mixtureEntropy K Z V)
    (F : FinitePrior Bᶜ) :
    (klDiv (F.finiteMixture K Z) (mixtureMeasure K Z W)).toReal+mixtureEntropy K Z W ≤
      (klDiv (F.finiteMixture K Z) Z).toReal := by
  have hvar := precision_variance_of_covariance K Z hcenter hcov
  have hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v) := by
    intro v
    rw [← hvar]
    exact variance_nonneg _ _
  have hp := (finite_pythagorean K Z hcenter hcov W hK F).2.2
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left
      (minimizer_exterior_inequality K Z hcenter hcov hB h0 W R hR hmin (F.mean i) (F.admissible i))
      (F.weights.nonneg i))
  rw [← Finset.sum_mul, F.weights.sum_eq_one, one_mul] at hsum
  linarith

end BoundaryReduction.Gaussian
