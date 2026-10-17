import BoundaryReduction.GaussianInformation

open Real Set MeasureTheory ProbabilityTheory InformationTheory BigOperators
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ Δ : Set (Space d)}

noncomputable def liftPrior (h : Γ ⊆ Δ) (W : ProbabilityMeasure Γ) : ProbabilityMeasure Δ :=
  ⟨(W : Measure Γ).map (fun r : Γ => (⟨(r : Space d),h r.2⟩ : Δ)),
    Measure.isProbabilityMeasure_map (by fun_prop)⟩

lemma likelihood_lift [CompactSpace Γ] [CompactSpace Δ]
    (K : Space d →L[ℝ] Space d) (h : Γ ⊆ Δ) (W : ProbabilityMeasure Γ) (x : Space d) :
    likelihood K (liftPrior h W : Measure Δ) x = likelihood K (W : Measure Γ) x := by
  unfold likelihood liftPrior
  simp only [ProbabilityMeasure.coe_mk]
  have hm : AEStronglyMeasurable (fun r : Δ => exp (exponent K r x))
      ((W : Measure Γ).map (fun r : Γ => (⟨(r : Space d),h r.2⟩ : Δ))) :=
    (Real.continuous_exp.comp (continuous_exponent K x)).aestronglyMeasurable
  rw [integral_map (by fun_prop) hm]
  rfl

lemma mixture_lift [CompactSpace Γ] [CompactSpace Δ]
    (K : Space d →L[ℝ] Space d) (Z : Measure (Space d))
    (h : Γ ⊆ Δ) (W : ProbabilityMeasure Γ) :
    mixtureMeasure K Z (liftPrior h W) = mixtureMeasure K Z W := by
  unfold mixtureMeasure
  congr 1
  ext x
  rw [likelihood_lift]

lemma expectedLog_lift [CompactSpace Γ] [CompactSpace Δ]
    (K : Space d →L[ℝ] Space d) (Z : Measure (Space d))
    (h : Γ ⊆ Δ) (W : ProbabilityMeasure Γ) (μ : Space d) :
    expectedLog K (liftPrior h W : Measure Δ) Z μ = expectedLog K (W : Measure Γ) Z μ := by
  simp only [expectedLog, phi, likelihood_lift]

variable [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
include hcenter hcov

/-- Any actual finite Gaussian mixture inherits the expected-log bound on its component means. -/
theorem finite_kl_lower_of_expectedLog (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    {C : Set (Space d)} {c : ℝ}
    (hglobal : ∀ μ ∈ C, c ≤ expectedLog K (W : Measure Γ) Z μ) (F : FinitePrior C) :
    ENNReal.ofReal c ≤ klDiv (F.finiteMixture K Z) Z := by
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
  have hc := cross_le_entropy K Z hcenter hcov F' W' Sn hSn hK
  rw [← cross_as_prior_average K Z hcenter hcov F' W' Sn hSn hK] at hc
  have heq : (∫ r : D, expectedLog K (W' : Measure D) Z (r : Space d) ∂(F' : Measure D)) =
      ∑ i, F.weights.w i*expectedLog K (W : Measure Γ) Z (F.mean i) := by
    dsimp [F']
    rw [FinitePrior.integral_asPrior F hFD (fun r : D => expectedLog K (W' : Measure D) Z (r : Space d))
      ((lipschitz_expectedLog K Z W' Sn hSn).continuous.comp continuous_subtype_val)]
    apply Finset.sum_congr rfl
    intro i _
    rw [show expectedLog K (W' : Measure D) Z (F.mean i) =
      expectedLog K (W : Measure Γ) Z (F.mean i) from expectedLog_lift K Z hΓD W _]
  rw [heq] at hc
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hglobal _ (F.admissible i)) (F.weights.nonneg i))
  rw [← Finset.sum_mul, F.weights.sum_eq_one, one_mul] at hsum
  have hlow : c ≤ mixtureEntropy K Z F' := hsum.trans hc
  have hvar := precision_variance_of_covariance K Z hcenter hcov
  rw [← F.mixture_asPrior K Z hFD, mixture_klDiv K Z hcenter hvar F' Sn hSn hK]
  exact ENNReal.ofReal_le_ofReal hlow

/-- Information lower bound over exactly the finite mixtures in the paper's definition. -/
theorem finiteInformation_lower_of_expectedLog (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    {C : Set (Space d)} {c : ℝ}
    (hglobal : ∀ μ ∈ C, c ≤ expectedLog K (W : Measure Γ) Z μ) :
    ENNReal.ofReal c ≤ finiteInformation K Z C := by
  apply le_sInf
  rintro x ⟨F,rfl⟩
  exact finite_kl_lower_of_expectedLog K Z hcenter hcov W R hR hK hglobal F

/-- The Gaussian finite-mixture information equality in (4.2). -/
theorem theorem_4_1_information {B : Set (Space d)} [CompactSpace (frontier B)]
    (hB : IsOpen B) (h0 : (0 : Space d) ∈ B) (hΓ : (frontier B).Nonempty)
    (W : ProbabilityMeasure (frontier B))
    (R : ℝ≥0) (hR : ∀ r : frontier B, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hmin : ∀ V : ProbabilityMeasure (frontier B), mixtureEntropy K Z W ≤ mixtureEntropy K Z V) :
    finiteInformation K Z Bᶜ = ENNReal.ofReal (mixtureEntropy K Z W) ∧
      finiteInformation K Z (frontier B) = ENNReal.ofReal (mixtureEntropy K Z W) := by
  have hb := finiteInformation_eq_minimum K Z hcenter hcov hΓ W R hR hK hmin
  refine ⟨le_antisymm ?_ ?_, hb⟩
  · have hsub : frontier B ⊆ Bᶜ := by
      intro x hx hxin
      exact hx.2 (by simpa only [hB.interior_eq] using hxin)
    have h := finiteInformation_antitone K Z hsub
    rwa [hb] at h
  · exact finiteInformation_lower_of_expectedLog K Z hcenter hcov W R hR hK
      (fun μ hμ => minimizer_exterior_inequality K Z hcenter hcov hB h0 W R hR hmin μ hμ)

end BoundaryReduction.Gaussian
