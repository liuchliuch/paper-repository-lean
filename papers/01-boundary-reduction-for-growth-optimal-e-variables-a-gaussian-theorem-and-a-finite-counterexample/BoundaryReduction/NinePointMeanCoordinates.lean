import BoundaryReduction.NinePointMeanImage
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open Real Set BigOperators MeasureTheory
open scoped Classical
namespace BoundaryReduction.NinePoint

noncomputable def meanImage : Set MeanSpace := Set.range (fun θ : ℝ × ℝ => esMean (pt θ))

noncomputable def naturalParameter (μ : meanImage) : ℝ × ℝ :=
  Set.rangeSplitting (fun θ : ℝ × ℝ => esMean (pt θ)) μ

lemma mean_naturalParameter (μ : meanImage) : esMean (pt (naturalParameter μ)) = (μ : MeanSpace) :=
  Set.apply_rangeSplitting _ μ

lemma naturalParameter_mean (θ : ℝ × ℝ) : naturalParameter ⟨esMean (pt θ),⟨θ,rfl⟩⟩ = θ :=
  mean_injective (mean_naturalParameter _)

lemma measurable_naturalParameter : Measurable naturalParameter :=
  mean_measurableEmbedding.measurable_rangeSplitting

noncomputable def meanLaw (μ : meanImage) : FinProb (Fin 9) := tiltProb (naturalParameter μ)

lemma boundary_subset_meanImage : boundary ⊆ meanImage := by
  intro μ hμ
  apply closedBall_subset_mean_range
  change ‖μ‖ = r₀ at hμ
  simpa only [Metric.mem_closedBall,dist_zero_right] using hμ.le

noncomputable def boundaryParameter (r : boundary) : ℝ × ℝ :=
  naturalParameter ⟨(r : MeanSpace),boundary_subset_meanImage r.2⟩

lemma measurable_boundaryParameter : Measurable boundaryParameter :=
  measurable_naturalParameter.comp measurable_subtype_coe.subtype_mk

lemma mean_boundaryParameter (r : boundary) : esMean (pt (boundaryParameter r)) = (r : MeanSpace) :=
  mean_naturalParameter _

noncomputable def boundaryNaturalPrior (W : ProbabilityMeasure boundary) : Measure (ℝ × ℝ) :=
  (W : Measure boundary).map boundaryParameter

instance (W : ProbabilityMeasure boundary) : IsProbabilityMeasure (boundaryNaturalPrior W) :=
  Measure.isProbabilityMeasure_map measurable_boundaryParameter.aemeasurable

/-- Actual mixture under a countably additive Borel prior on the mean circle. -/
noncomputable def meanBoundaryMixture (W : ProbabilityMeasure boundary) : FinProb (Fin 9) :=
  borelProb (boundaryNaturalPrior W)

lemma meanBoundaryMixture_mass (W : ProbabilityMeasure boundary) (y : Fin 9) :
    (meanBoundaryMixture W).w y =
      ∫ r : boundary, (meanLaw ⟨(r : MeanSpace),boundary_subset_meanImage r.2⟩).w y ∂(W : Measure boundary) := by
  change (∫ θ, pt θ y ∂(W : Measure boundary).map boundaryParameter) = _
  exact integral_map measurable_boundaryParameter.aemeasurable (continuous_pt y).aestronglyMeasurable

/-- The obstruction in (2.7), now quantified over all Borel priors on Γ in
mean coordinates, rather than priors on natural parameters. -/
theorem no_mean_borel_boundary_global (W : ProbabilityMeasure boundary) :
    ¬ (∀ μ : meanImage, r₀ ≤ ‖(μ : MeanSpace)‖ →
      FinProb.klPos (meanBoundaryMixture W) baseProb ≤
        FinProb.expect (meanLaw μ) (fun y => log ((meanBoundaryMixture W).w y/p0 y))) := by
  have hs : ∀ᵐ θ ∂boundaryNaturalPrior W, ‖esMean (pt θ)‖ = r₀ := by
    apply (ae_map_iff measurable_boundaryParameter.aemeasurable
      (p := fun θ : ℝ × ℝ => ‖esMean (pt θ)‖ = r₀)
      (isClosed_eq continuous_mean.norm continuous_const).measurableSet).mpr
    exact Filter.Eventually.of_forall (fun r => by rw [mean_boundaryParameter]; exact r.2)
  intro hglobal
  apply no_borel_boundary_global (boundaryNaturalPrior W) hs
  intro θ hθ
  have hh := hglobal ⟨esMean (pt θ),⟨θ,rfl⟩⟩ hθ
  simpa only [meanLaw,naturalParameter_mean,meanBoundaryMixture] using hh

/-- The actual excluded ball has compact closure inside the mean space. -/
theorem excluded_ball_geometry :
    IsOpen (Metric.ball (0 : MeanSpace) r₀) ∧ (0 : MeanSpace) ∈ Metric.ball 0 r₀ ∧
    IsCompact (closure (Metric.ball (0 : MeanSpace) r₀)) ∧
    closure (Metric.ball (0 : MeanSpace) r₀) ⊆ meanImage ∧
    frontier (Metric.ball (0 : MeanSpace) r₀) = boundary := by
  rw [closure_ball _ r₀_pos.ne',frontier_ball _ r₀_pos.ne']
  exact ⟨Metric.isOpen_ball,by simpa using r₀_pos,isCompact_closedBall _ _,closedBall_subset_mean_range,by ext x; simp [Metric.mem_sphere,dist_zero_right,boundary]⟩

/-- No proper affine hyperplane contains the alphabet: the finite NEF is minimal. -/
theorem alphabet_minimal (a : MeanSpace) (b : ℝ)
    (h : ∀ y : Fin 9, inner ℝ a (esTarget y) = b) : a = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h3 := h 3
  norm_num [esTarget,toES,coord,PiLp.inner_apply,Fin.sum_univ_succ,Fin.succ] at h0 h1 h3
  ext i
  fin_cases i <;> simp_all

end BoundaryReduction.NinePoint
