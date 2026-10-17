import BoundaryReduction.GaussianFinite

open Real Set MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
include hcenter hcov

/-- The compact Borel optimum equals the paper's infimum over genuine finite Gaussian mixtures. -/
theorem finiteInformation_eq_minimum (hΓ : Γ.Nonempty) (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hmin : ∀ V : ProbabilityMeasure Γ, mixtureEntropy K Z W ≤ mixtureEntropy K Z V) :
    finiteInformation K Z Γ = ENNReal.ofReal (mixtureEntropy K Z W) := by
  have hvar := precision_variance_of_covariance K Z hcenter hcov
  have hminKL := (entropy_min_iff_kl_min K Z hcenter hcov W R hR hK).mp hmin
  apply le_antisymm
  · have hX : Nonempty Γ := by obtain ⟨r,hr⟩ := hΓ; exact ⟨⟨r,hr⟩⟩
    obtain ⟨V,hfin,hlim⟩ := CompactPrior.exists_finite_priors_tendsto hX W
    have ht : Filter.Tendsto (fun n => ENNReal.ofReal (mixtureEntropy K Z (V n))) Filter.atTop
        (nhds (ENNReal.ofReal (mixtureEntropy K Z W))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_mixtureEntropy K Z R hR hK)).continuousAt.tendsto).comp hlim
    apply ge_of_tendsto ht
    apply Filter.Eventually.of_forall
    intro n
    obtain ⟨F,hF⟩ := exists_finite_representation K (V n) (hfin n)
    have hQ : F.finiteMixture K Z = mixtureMeasure K Z (V n) := by
      unfold FinitePrior.finiteMixture mixtureMeasure
      congr 1
      ext x
      rw [hF x]
    rw [← mixture_klDiv K Z hcenter hvar (V n) R hR hK, ← hQ]
    exact sInf_le ⟨F,rfl⟩
  · apply le_sInf
    rintro x ⟨F,rfl⟩
    rw [← F.mixture_asPrior K Z F.admissible,
      ← mixture_klDiv K Z hcenter hvar W R hR hK]
    exact hminKL (F.asPrior F.admissible)

omit hcenter hcov

/-- Monotonicity of information under enlarging the component-mean set. -/
lemma finiteInformation_antitone {C D : Set (Space d)} (hCD : C ⊆ D) :
    finiteInformation K Z D ≤ finiteInformation K Z C := by
  apply le_sInf
  rintro x ⟨V,rfl⟩
  exact sInf_le ⟨V.weaken hCD,rfl⟩

end BoundaryReduction.Gaussian
