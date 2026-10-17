import BoundaryReduction.CompactPrior
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Set MeasureTheory Filter
open scoped Classical BoundedContinuousFunction
namespace BoundaryReduction.CompactPrior

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A finite-valued Borel map approximating the identity uniformly on a compact metric space. -/
theorem exists_finite_borel_approx (hX : Nonempty X) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : X → X, Measurable T ∧ (Set.range T).Finite ∧ ∀ x, dist (T x) x ≤ δ := by
  letI : Zero X := ⟨Classical.choice hX⟩
  obtain ⟨g,hg⟩ := (HasCompactSupport.of_compactSpace (fun p : X × Unit => p.1)).exists_simpleFunc_approx_of_prod
    continuous_fst hδ
  refine ⟨fun x => g (x,()), g.measurable.comp (measurable_id.prodMk measurable_const), ?_, ?_⟩
  · exact g.finite_range.subset (by rintro y ⟨x,rfl⟩; exact ⟨(x,()),rfl⟩)
  · intro x
    simpa only [dist_comm] using (hg (x,())).le

noncomputable def mapPrior (W : ProbabilityMeasure X) (T : X → X) (hT : Measurable T) :
    ProbabilityMeasure X := ⟨(W : Measure X).map T, Measure.isProbabilityMeasure_map hT.aemeasurable⟩

lemma mapPrior_finite_support (W : ProbabilityMeasure X) (T : X → X) (hT : Measurable T)
    (hfin : (Set.range T).Finite) : ((mapPrior W T hT : Measure X).support).Finite := by
  apply hfin.subset
  apply Measure.support_subset_of_isClosed hfin.isClosed
  change (W : Measure X).map T ((Set.range T)ᶜ) = 0
  rw [Measure.map_apply hT hfin.isClosed.measurableSet.compl]
  have he : T ⁻¹' ((Set.range T)ᶜ) = ∅ := by ext x; simp
  rw [he, measure_empty]

/-- Pointwise convergence of Borel maps gives weak convergence of their push-forward priors. -/
lemma tendsto_mapPrior (W : ProbabilityMeasure X) (T : ℕ → X → X) (hT : ∀ n, Measurable (T n))
    (hlim : ∀ x, Tendsto (fun n => T n x) atTop (nhds x)) :
    Tendsto (fun n => mapPrior W (T n) (hT n)) atTop (nhds W) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have he : (fun n => ∫ x, f x ∂(mapPrior W (T n) (hT n) : Measure X)) =
      fun n => ∫ x, f (T n x) ∂(W : Measure X) := by
    ext n
    change (∫ x, f x ∂(W : Measure X).map (T n)) = _
    rw [integral_map (hT n).aemeasurable f.continuous.aestronglyMeasurable]
  rw [he]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro n
    exact (f.continuous.measurable.comp (hT n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall (fun x => f.norm_coe_le_norm (T n x))
  · exact Eventually.of_forall (fun x => f.continuous.continuousAt.tendsto.comp (hlim x))

/-- Every compact Borel prior is a weak limit of actual finite priors. -/
theorem exists_finite_priors_tendsto (hX : Nonempty X) (W : ProbabilityMeasure X) :
    ∃ V : ℕ → ProbabilityMeasure X,
      (∀ n, ((V n : Measure X).support).Finite) ∧ Tendsto V atTop (nhds W) := by
  let δ : ℕ → ℝ := fun n => (1/2 : ℝ)^n
  have hδ : ∀ n, 0 < δ n := fun n => pow_pos (by norm_num) n
  have hδlim : Tendsto δ atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  choose T hmeas hfin happ using fun n => exists_finite_borel_approx hX (hδ n)
  refine ⟨fun n => mapPrior W (T n) (hmeas n), ?_, ?_⟩
  · exact fun n => mapPrior_finite_support W (T n) (hmeas n) (hfin n)
  · apply tendsto_mapPrior W T hmeas
    intro x
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun n => dist_nonneg) (fun n => happ n x) hδlim

end BoundaryReduction.CompactPrior
