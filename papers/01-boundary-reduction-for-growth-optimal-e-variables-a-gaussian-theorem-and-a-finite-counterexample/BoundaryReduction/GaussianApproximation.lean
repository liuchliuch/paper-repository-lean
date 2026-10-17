import BoundaryReduction.GaussianCoupling
import BoundaryReduction.SupportApprox

open Real Set MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
include hcenter hcov

lemma prior_average_self (W : ProbabilityMeasure Γ) (R : ℝ≥0)
    (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    (∫ r : Γ, expectedLog K (W : Measure Γ) Z (r : Space d) ∂(W : Measure Γ)) = mixtureEntropy K Z W :=
  cross_as_prior_average K Z hcenter hcov W W R hR hK

lemma mapPrior_cross_difference_le (W : ProbabilityMeasure Γ) (T : Γ → Γ) (hT : Measurable T)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    {δ : ℝ} (happrox : ∀ᵐ r ∂(W : Measure Γ), ‖(T r : Space d)-(r : Space d)‖ ≤ δ) :
    (∫ r : Γ, expectedLog K (W : Measure Γ) Z (r : Space d)
      ∂(CompactPrior.mapPrior W T hT : Measure Γ))-mixtureEntropy K Z W ≤ (R:ℝ)*‖K‖*δ := by
  let V := CompactPrior.mapPrior W T hT
  have hf := integrable_expectedLog_prior K Z hcenter hcov W W R hR hK
  have hfT : Integrable (fun r : Γ => expectedLog K (W : Measure Γ) Z (T r : Space d)) (W : Measure Γ) :=
    (integrable_expectedLog_prior K Z hcenter hcov V W R hR hK).comp_measurable hT
  have heq : (∫ r : Γ, expectedLog K (W : Measure Γ) Z (r : Space d) ∂(V : Measure Γ)) =
      ∫ r : Γ, expectedLog K (W : Measure Γ) Z (T r : Space d) ∂(W : Measure Γ) := by
    exact integral_map hT.aemeasurable
      ((lipschitz_expectedLog K Z W R hR).continuous.comp continuous_subtype_val).aestronglyMeasurable
  have hb : (∫ r : Γ, expectedLog K (W : Measure Γ) Z (T r : Space d)-
      expectedLog K (W : Measure Γ) Z (r : Space d) ∂(W : Measure Γ)) ≤ (R:ℝ)*‖K‖*δ := by
    apply le_trans (integral_mono_ae (hfT.sub hf) (integrable_const ((R:ℝ)*‖K‖*δ)) ?_) (by simp)
    filter_upwards [happrox] with r hr
    exact (expectedLog_sub_le K Z W R hR (T r : Space d) (r : Space d)).trans
      (mul_le_mul_of_nonneg_left hr (by positivity))
  have hs := integral_sub hfT hf
  simp only [Pi.sub_apply] at hs
  rw [hs,prior_average_self K Z hcenter hcov W R hR hK] at hb
  rwa [heq]

/-- Corollary 4.4, equation (4.20), for every finite Borel quantization map. -/
theorem corollary_4_4_map (W : ProbabilityMeasure Γ) (T : Γ → Γ) (hT : Measurable T)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hsym : ∀ u v : Space d, inner ℝ u (K v) = inner ℝ v (K u))
    (hmin : ∀ V : ProbabilityMeasure Γ, mixtureEntropy K Z W ≤ mixtureEntropy K Z V)
    {δ : ℝ} (hδ : 0 ≤ δ) (happrox : ∀ r : Γ, ‖(T r : Space d)-(r : Space d)‖ ≤ δ) :
    0 ≤ mixtureEntropy K Z (CompactPrior.mapPrior W T hT)-mixtureEntropy K Z W ∧
    mixtureEntropy K Z (CompactPrior.mapPrior W T hT)-mixtureEntropy K Z W ≤
      ‖K‖*δ^2/2+(R:ℝ)*‖K‖*δ := by
  have hae : ∀ᵐ r ∂(W : Measure Γ), ‖(T r : Space d)-(r : Space d)‖ ≤ δ := Filter.Eventually.of_forall happrox
  have hkl := mapPrior_relative_kl_le_ae K Z hcenter hcov W T hT R hR hK hsym hδ hae
  have hc := mapPrior_cross_difference_le K Z hcenter hcov W T hT R hR hK hae
  have hp := mixture_pythagorean K Z hcenter hcov (CompactPrior.mapPrior W T hT) W R hR hK
  exact ⟨sub_nonneg.mpr (hmin _), by linarith⟩

/-- A map into the optimal support eliminates the linear error term. -/
theorem corollary_4_4_support_map (W : ProbabilityMeasure Γ) (T : Γ → Γ) (hT : Measurable T)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hsym : ∀ u v : Space d, inner ℝ u (K v) = inner ℝ v (K u))
    (hmin : ∀ V : ProbabilityMeasure Γ, mixtureEntropy K Z W ≤ mixtureEntropy K Z V)
    (hsupport : ∀ r, T r ∈ (W : Measure Γ).support)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (happrox : ∀ᵐ r ∂(W : Measure Γ), ‖(T r : Space d)-(r : Space d)‖ ≤ δ) :
    0 ≤ mixtureEntropy K Z (CompactPrior.mapPrior W T hT)-mixtureEntropy K Z W ∧
    mixtureEntropy K Z (CompactPrior.mapPrior W T hT)-mixtureEntropy K Z W =
      (klDiv (mixtureMeasure K Z (CompactPrior.mapPrior W T hT)) (mixtureMeasure K Z W)).toReal ∧
    (klDiv (mixtureMeasure K Z (CompactPrior.mapPrior W T hT)) (mixtureMeasure K Z W)).toReal ≤ ‖K‖*δ^2/2 := by
  have heq : (∫ r : Γ, expectedLog K (W : Measure Γ) Z (r : Space d)
      ∂(CompactPrior.mapPrior W T hT : Measure Γ)) = mixtureEntropy K Z W := by
    change (∫ r : Γ, expectedLog K (W : Measure Γ) Z (r : Space d) ∂(W : Measure Γ).map T) = _
    have hm : AEStronglyMeasurable (fun r : Γ => expectedLog K (W : Measure Γ) Z (r : Space d))
        ((W : Measure Γ).map T) :=
      ((lipschitz_expectedLog K Z W R hR).continuous.comp continuous_subtype_val).aestronglyMeasurable
    rw [integral_map hT.aemeasurable hm]
    simp_rw [minimizer_support_equalization K Z hcenter hcov W R hR hK hmin _ (hsupport _)]
    simp
  have hp := mixture_pythagorean K Z hcenter hcov (CompactPrior.mapPrior W T hT) W R hR hK
  rw [heq] at hp
  exact ⟨sub_nonneg.mpr (hmin _), by linarith,
    mapPrior_relative_kl_le_ae K Z hcenter hcov W T hT R hR hK hsym hδ happrox⟩

/-- Corollary 4.4, existence and exact KL identity in (4.21). -/
theorem corollary_4_4_finite (W : ProbabilityMeasure Γ) (R : ℝ≥0)
    (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hsym : ∀ u v : Space d, inner ℝ u (K v) = inner ℝ v (K u))
    (hmin : ∀ V : ProbabilityMeasure Γ, mixtureEntropy K Z W ≤ mixtureEntropy K Z V)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ V : ProbabilityMeasure Γ, (V : Measure Γ).support.Finite ∧
      (V : Measure Γ).support ⊆ (W : Measure Γ).support ∧
      0 ≤ mixtureEntropy K Z V-mixtureEntropy K Z W ∧
      mixtureEntropy K Z V-mixtureEntropy K Z W =
        (klDiv (mixtureMeasure K Z V) (mixtureMeasure K Z W)).toReal ∧
      (klDiv (mixtureMeasure K Z V) (mixtureMeasure K Z W)).toReal ≤ ‖K‖*δ^2/2 := by
  obtain ⟨T,hT,hfin,hsupp,happrox⟩ := CompactPrior.exists_finite_support_approx W hδ
  let V := CompactPrior.mapPrior W T hT
  have hae : ∀ᵐ r ∂(W : Measure Γ), ‖(T r : Space d)-(r : Space d)‖ ≤ δ := by
    filter_upwards [Measure.support_mem_ae (μ := (W : Measure Γ))] with r hr
    simpa only [Subtype.dist_eq,dist_eq_norm] using happrox r hr
  refine ⟨V,CompactPrior.mapPrior_finite_support W T hT hfin,?_,
    corollary_4_4_support_map K Z hcenter hcov W T hT R hR hK hsym hmin hsupp hδ.le hae⟩
  apply Measure.support_subset_of_isClosed Measure.isClosed_support
  change (∀ᵐ r ∂(W : Measure Γ).map T, r ∈ (W : Measure Γ).support)
  apply (ae_map_iff hT.aemeasurable (p := fun r => r ∈ (W : Measure Γ).support)
    Measure.isClosed_support.measurableSet).mpr
  exact Filter.Eventually.of_forall hsupp

/-- The sharper approximants can be selected for every positive precision and
converge weakly as δ decreases to zero, as asserted after (4.21). -/
theorem corollary_4_4_family (W : ProbabilityMeasure Γ) (R : ℝ≥0)
    (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hsym : ∀ u v : Space d, inner ℝ u (K v) = inner ℝ v (K u))
    (hmin : ∀ V : ProbabilityMeasure Γ, mixtureEntropy K Z W ≤ mixtureEntropy K Z V) :
    ∃ V : ℝ → ProbabilityMeasure Γ,
      (∀ δ > 0, (V δ : Measure Γ).support.Finite ∧
        (V δ : Measure Γ).support ⊆ (W : Measure Γ).support ∧
        0 ≤ mixtureEntropy K Z (V δ)-mixtureEntropy K Z W ∧
        mixtureEntropy K Z (V δ)-mixtureEntropy K Z W =
          (klDiv (mixtureMeasure K Z (V δ)) (mixtureMeasure K Z W)).toReal ∧
        (klDiv (mixtureMeasure K Z (V δ)) (mixtureMeasure K Z W)).toReal ≤ ‖K‖*δ^2/2) ∧
      Filter.Tendsto V (nhdsWithin 0 (Ioi 0)) (nhds W) := by
  obtain ⟨r,hr⟩ := Measure.nonempty_support (IsProbabilityMeasure.ne_zero (μ := (W : Measure Γ)))
  have hex (δ : ℝ) : ∃ T : Γ → Γ, Measurable T ∧ (Set.range T).Finite ∧
      (∀ x, T x ∈ (W : Measure Γ).support) ∧
      (0 < δ → ∀ x ∈ (W : Measure Γ).support, dist (T x) x ≤ δ) := by
    by_cases hδ : 0 < δ
    · obtain ⟨T,hT,hfin,hs,happ⟩ := CompactPrior.exists_finite_support_approx W hδ
      exact ⟨T,hT,hfin,hs,fun _ => happ⟩
    · exact ⟨fun _ => r,measurable_const,Set.finite_range_const,fun _ => hr,fun h => (hδ h).elim⟩
  choose T hT hfin hs happ using hex
  let V : ℝ → ProbabilityMeasure Γ := fun δ => CompactPrior.mapPrior W (T δ) (hT δ)
  refine ⟨V,?_,?_⟩
  · intro δ hδ
    have hae : ∀ᵐ r ∂(W : Measure Γ), ‖(T δ r : Space d)-(r : Space d)‖ ≤ δ := by
      filter_upwards [Measure.support_mem_ae (μ := (W : Measure Γ))] with x hx
      simpa only [Subtype.dist_eq,dist_eq_norm] using happ δ hδ x hx
    refine ⟨CompactPrior.mapPrior_finite_support W (T δ) (hT δ) (hfin δ),?_,
      corollary_4_4_support_map K Z hcenter hcov W (T δ) (hT δ) R hR hK hsym hmin (hs δ) hδ.le hae⟩
    apply Measure.support_subset_of_isClosed Measure.isClosed_support
    change (∀ᵐ x ∂(W : Measure Γ).map (T δ), x ∈ (W : Measure Γ).support)
    apply (ae_map_iff (hT δ).aemeasurable (p := fun x => x ∈ (W : Measure Γ).support)
      Measure.isClosed_support.measurableSet).mpr
    exact Filter.Eventually.of_forall (hs δ)
  · apply CompactPrior.tendsto_mapPrior_filter W T hT
    filter_upwards [Measure.support_mem_ae (μ := (W : Measure Γ))] with x hx
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => dist_nonneg)) ?_
      (Filter.tendsto_id.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact happ δ hδ x hx

end BoundaryReduction.Gaussian
