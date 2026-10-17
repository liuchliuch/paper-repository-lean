import BoundaryReduction.GaussianOptimality

open Real Set MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ}

lemma raywise_of_convex {f : Space d → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    BoundaryReduction.RaywiseConvex f := by
  intro u
  refine ⟨convex_Ici (0:ℝ), ?_⟩
  intro s _ t _ a b ha hb hab
  have h := hf.2 (Set.mem_univ (s • u)) (Set.mem_univ (t • u)) ha hb hab
  rw [smul_smul, smul_smul, ← add_smul] at h
  exact h

variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
include hcenter hcov

/-- The global exterior inequality (4.3) for the actual minimizing boundary mixture. -/
theorem minimizer_exterior_inequality {B : Set (Space d)} [CompactSpace (frontier B)]
    (hB : IsOpen B) (h0 : (0 : Space d) ∈ B)
    (W : ProbabilityMeasure (frontier B))
    (R : ℝ≥0) (hR : ∀ r : frontier B, ‖(r : Space d)‖ ≤ R)
    (hmin : ∀ V : ProbabilityMeasure (frontier B), mixtureEntropy K Z W ≤ mixtureEntropy K Z V) :
    ∀ μ : Space d, μ ∉ B → mixtureEntropy K Z W ≤ expectedLog K (W : Measure (frontier B)) Z μ := by
  have hvar := precision_variance_of_covariance K Z hcenter hcov
  have hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v) := by
    intro v
    rw [← hvar]
    exact variance_nonneg _ _
  have hf := convex_expectedLog K (W : Measure (frontier B)) Z R hR
  have hf0 := expectedLog_zero_nonpos K Z hcenter hvar (W : Measure (frontier B)) R hR
  have hc := mixtureEntropy_nonneg K Z hcenter hvar W R hR hK
  have hb := boundary_condition_of_minimizer K Z hcenter hcov W R hR hK hmin
  intro μ hμ
  exact BoundaryReduction.first_exit_propagation hB h0 (raywise_of_convex hf)
    (hf0.trans hc) (fun r hr => hb ⟨r,hr⟩) hμ

/-- Construction of an actual Borel boundary minimizer with the full exterior expected-log inequality. -/
theorem exists_global_boundary_mixture {B : Set (Space d)}
    (hd : 1 ≤ d) (hB : IsOpen B) (h0 : (0 : Space d) ∈ B) (hbounded : Bornology.IsBounded B) :
    ∃ W : ProbabilityMeasure (frontier B),
      (∀ V : ProbabilityMeasure (frontier B), mixtureEntropy K Z W ≤ mixtureEntropy K Z V) ∧
      (∀ μ : Space d, μ ∉ B → mixtureEntropy K Z W ≤ expectedLog K (W : Measure (frontier B)) Z μ) ∧
      (∀ r ∈ (W : Measure (frontier B)).support,
        expectedLog K (W : Measure (frontier B)) Z (r : Space d) = mixtureEntropy K Z W) := by
  have hc := compact_nonempty_boundary hd hB h0 hbounded
  letI : CompactSpace (frontier B) := isCompact_iff_compactSpace.mp hc.1
  obtain ⟨R,hRpos,hR⟩ := hc.1.isBounded.exists_pos_norm_le
  let Rn : ℝ≥0 := ⟨R,hRpos.le⟩
  have hRn : ∀ r : frontier B, ‖(r : Space d)‖ ≤ Rn := fun r => hR r r.2
  have hvar := precision_variance_of_covariance K Z hcenter hcov
  have hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v) := by
    intro v
    rw [← hvar]
    exact variance_nonneg _ _
  obtain ⟨W,hW⟩ := exists_entropy_minimizer K Z hc.2 Rn hRn hK
  exact ⟨W,hW,minimizer_exterior_inequality K Z hcenter hcov hB h0 W Rn hRn hW,
    minimizer_support_equalization K Z hcenter hcov W Rn hRn hK hW⟩

omit hcov

/-- The same construction from the quadratic precision description, with no cross-covariance premise. -/
theorem exists_global_boundary_mixture_of_variance
    (hvariance : ∀ v : Space d, variance (precisionForm K v) Z = inner ℝ v (K v))
    (hsym : ∀ u v : Space d, inner ℝ u (K v) = inner ℝ v (K u))
    (hsurj : Function.Surjective K)
    {B : Set (Space d)} (hd : 1 ≤ d) (hB : IsOpen B) (h0 : (0 : Space d) ∈ B)
    (hbounded : Bornology.IsBounded B) :
    ∃ W : ProbabilityMeasure (frontier B),
      (∀ V : ProbabilityMeasure (frontier B), mixtureEntropy K Z W ≤ mixtureEntropy K Z V) ∧
      (∀ μ : Space d, μ ∉ B → mixtureEntropy K Z W ≤ expectedLog K (W : Measure (frontier B)) Z μ) ∧
      (∀ r ∈ (W : Measure (frontier B)).support,
        expectedLog K (W : Measure (frontier B)) Z (r : Space d) = mixtureEntropy K Z W) := by
  have hcov' := precision_covariance_identity K Z hvariance hsym hsurj
  exact exists_global_boundary_mixture K Z hcenter hcov' hd hB h0 hbounded

end BoundaryReduction.Gaussian
