import BoundaryReduction.FinitePriorApprox

open Set MeasureTheory
open scoped Classical
namespace BoundaryReduction.CompactPrior

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A finite Borel approximation whose values stay on the original prior's support. -/
theorem exists_finite_support_approx (W : ProbabilityMeasure X) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : X → X, Measurable T ∧ (Set.range T).Finite ∧
      (∀ x, T x ∈ (W : Measure X).support) ∧
      (∀ x ∈ (W : Measure X).support, dist (T x) x ≤ δ) := by
  let S := (W : Measure X).support
  have hs : IsClosed S := Measure.isClosed_support
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hs.isCompact
  obtain ⟨r,hr⟩ := Measure.nonempty_support (IsProbabilityMeasure.ne_zero (μ := (W : Measure X)))
  have hS : Nonempty S := ⟨⟨r,hr⟩⟩
  obtain ⟨U,hU,hfin,happrox⟩ := exists_finite_borel_approx hS hδ
  let T : X → X := fun x => if hx : x ∈ S then (U ⟨x,hx⟩ : X) else r
  have hT : Measurable T := Measurable.dite (measurable_subtype_coe.comp hU) measurable_const hs.measurableSet
  refine ⟨T,hT,?_,?_,?_⟩
  · apply ((hfin.image (Subtype.val : S → X)).union (finite_singleton r)).subset
    rintro y ⟨x,rfl⟩
    by_cases hx : x ∈ S
    · left
      exact ⟨U ⟨x,hx⟩,⟨⟨x,hx⟩,rfl⟩,by simp [T,hx]⟩
    · right
      simp [T,hx]
  · intro x
    dsimp [T]
    split_ifs with hx
    · exact (U ⟨x,hx⟩).2
    · exact hr
  · intro x hx
    change x ∈ S at hx
    simpa only [T,dif_pos hx,Subtype.dist_eq] using happrox ⟨x,hx⟩

/-- Dominated convergence for weak convergence of mapped compact priors. -/
lemma tendsto_mapPrior_filter {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (W : ProbabilityMeasure X) (T : ι → X → X) (hT : ∀ n, Measurable (T n))
    (hlim : ∀ᵐ x ∂(W : Measure X), Filter.Tendsto (fun n => T n x) l (nhds x)) :
    Filter.Tendsto (fun n => mapPrior W (T n) (hT n)) l (nhds W) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have heq (n : ι) : (∫ x, f x ∂(mapPrior W (T n) (hT n) : Measure X)) =
      ∫ x, f (T n x) ∂(W : Measure X) :=
    integral_map (hT n).aemeasurable f.continuous.aestronglyMeasurable
  simp_rw [heq]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => ‖f‖)
  · exact Filter.Eventually.of_forall (fun n =>
      (f.continuous.measurable.comp (hT n)).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun n =>
      Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm (T n x)))
  · exact integrable_const _
  · filter_upwards [hlim] with x hx
    exact f.continuous.continuousAt.tendsto.comp hx

end BoundaryReduction.CompactPrior
