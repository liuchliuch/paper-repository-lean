import Paper26.WeakPosteriorIdentity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Bases

/-!
# A common s-finite support for continuous normalized likelihoods

An arbitrary reference measure need not be s-finite. A separable parameter
space and almost-everywhere continuous likelihood roots nevertheless put every
nonzero likelihood on one common measurable s-finite restriction. This is a
native countable-dense-set reduction, not an assumed reference-measure theorem.
-/
noncomputable section
open scoped ENNReal
open MeasureTheory Set TopologicalSpace

namespace Paper26.LikelihoodSupport
variable {Y E : Type*} [MeasurableSpace Y] [TopologicalSpace E]
  [SeparableSpace E] [Nonempty E] {ν : Measure Y}

/-- Countably many integrable real functions have a common measurable
s-finite restriction containing their nonzero supports almost everywhere. -/
theorem countable_integrable_support (f : ℕ → Y → ℝ)
    (hi : ∀ n, Integrable (f n) ν) :
    ∃ S : Set Y, MeasurableSet S ∧ SFinite (ν.restrict S) ∧
      (∀ᵐ y ∂ν, y ∉ S → ∀ n, f n y = 0) := by
  let a : ℕ → Y → ℝ := fun n => (hi n).aestronglyMeasurable.mk (f n)
  have ha (n : ℕ) : Measurable (a n) := (hi n).aestronglyMeasurable.measurable_mk
  have hae (n : ℕ) : f n =ᵐ[ν] a n := (hi n).aestronglyMeasurable.ae_eq_mk
  have hai (n : ℕ) : Integrable (a n) ν := (hi n).congr (hae n)
  let T : ℕ → Set Y := fun k =>
    {y | 1 / ((Nat.unpair k).2 + 1 : ℝ) ≤ |a (Nat.unpair k).1 y|}
  have hT (k : ℕ) : MeasurableSet (T k) := by
    have hn : Measurable (fun y => |a (Nat.unpair k).1 y|) := by
      simpa only [Real.norm_eq_abs] using (ha (Nat.unpair k).1).norm
    exact measurableSet_le measurable_const hn
  have hfin (k : ℕ) : ν (T k) < ∞ := by
    let c : ℝ := 1 / ((Nat.unpair k).2 + 1 : ℝ)
    have hc : 0 < c := by dsimp [c]; positivity
    have hscaled : Integrable (fun y => |a (Nat.unpair k).1 y| / c) ν := (hai _).abs.div_const c
    have hm := hscaled.measure_le_integral
      (Filter.Eventually.of_forall fun y => div_nonneg (abs_nonneg _) hc.le)
      (s := T k) (by intro y hy; exact (le_div_iff₀ hc).2 (by simpa [T, c] using hy))
    exact lt_of_le_of_lt hm ENNReal.ofReal_lt_top
  let S := ⋃ k, T k
  have hS : MeasurableSet S := MeasurableSet.iUnion hT
  have hdis (k : ℕ) : IsFiniteMeasure (ν.restrict (disjointed T k)) := by
    apply isFiniteMeasure_restrict.2
    exact ne_of_lt ((measure_mono (disjointed_subset T k)).trans_lt (hfin k))
  have hsf : SFinite (ν.restrict S) := by
    have he : ν.restrict S = Measure.sum (fun k => ν.restrict (disjointed T k)) := by
      dsimp only [S]
      rw [← iUnion_disjointed]
      exact Measure.restrict_iUnion (disjoint_disjointed T)
        (fun k => MeasurableSet.disjointed hT k)
    rw [he]
    letI (k : ℕ) : IsFiniteMeasure (ν.restrict (disjointed T k)) := hdis k
    infer_instance
  refine ⟨S, hS, hsf, ?_⟩
  filter_upwards [ae_all_iff.2 hae] with y hy hnot n
  rw [hy n]
  by_contra hn
  have hpos : 0 < |a n y| := abs_pos.2 hn
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
  have ht : y ∈ T (Nat.pair n m) := by
    simpa only [T, Nat.unpair_pair] using hm.le
  exact hnot (mem_iUnion.2 ⟨Nat.pair n m, ht⟩)

/-- All continuous likelihood roots vanish identically off one measurable
s-finite support, with one common outcome-null exceptional set. -/
theorem continuous_likelihood_support (g : Y → E → ℝ)
    (hcont : ∀ᵐ y ∂ν, Continuous (g y))
    (hi : ∀ x, Integrable (fun y => g y x ^ 2) ν) :
    ∃ S : Set Y, MeasurableSet S ∧ SFinite (ν.restrict S) ∧
      (∀ᵐ y ∂ν, y ∉ S → g y = 0) := by
  obtain ⟨S, hS, hsf, hz⟩ := countable_integrable_support
    (fun n y => g y (denseSeq E n) ^ 2) (fun n => hi _)
  refine ⟨S, hS, hsf, ?_⟩
  filter_upwards [hcont, hz] with y hcy hzy hnot
  apply Continuous.ext_on (denseRange_denseSeq E) hcy continuous_const
  rintro x ⟨n, rfl⟩
  exact (sq_eq_zero_iff).1 (hzy hnot n)

/-- In Euclidean parameter space, the same common restriction carries all
Fréchet derivatives as well as all likelihoods. -/
theorem differentiable_likelihood_support {p : ℕ}
    (g : Y → H1PosteriorBound.ParameterSpace p → ℝ)
    (hcont : ∀ᵐ y ∂ν, Continuous (g y))
    (hi : ∀ x, Integrable (fun y => g y x ^ 2) ν) :
    ∃ S : Set Y, MeasurableSet S ∧ SFinite (ν.restrict S) ∧
      (∀ᵐ y ∂ν, y ∉ S → ∀ x, g y x = 0 ∧ fderiv ℝ (g y) x = 0) := by
  obtain ⟨S, hS, hsf, hz⟩ := continuous_likelihood_support g hcont hi
  refine ⟨S, hS, hsf, hz.mono ?_⟩
  intro y hy hnot x
  have he := hy hnot
  rw [he]
  simp

end Paper26.LikelihoodSupport
