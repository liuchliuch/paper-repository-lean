/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in Paper14/Background/LICENSE.
Authors: Sébastien Gouëzel
Adapted to pinned Lean 4.24 / mathlib by the P14 formalization.
Source: mathlib4 79d0395a1825a6264ad5d269e35e60537518955e,
Mathlib/MeasureTheory/Measure/Prokhorov.lean, compact-space portion.
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
open scoped CompactlySupported
open Metric ENNReal NNReal Filter Set Topology TopologicalSpace MeasureTheory BoundedContinuousFunction
open MeasureTheory.FiniteMeasure
namespace Paper14.Background
variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [T2Space E] [BorelSpace E]
variable (E) in
/-- In a compact space, the set of finite measures with mass at most `C` is compact. -/
theorem isCompact_setOf_finiteMeasure_le_of_compactSpace [CompactSpace E] (C : ℝ≥0) :
    IsCompact {μ : FiniteMeasure E | μ.mass ≤ C} := by
  /- To prove the compactness, we will show that any sequence has a converging subsequence, in
  ultrafilters terms as things are not second countable. The integral against any bounded continuous
  function has a limit along the ultrafilter, by compactness of real intervals and the mass control.
  The limit is a monotone linear form. By the Riesz-Markov-Kakutani theorem, it comes from a
  measure. This measure is finite, of mass at most `C`. It provides the desired limit
  for the ultrafilter. -/
  apply isCompact_iff_ultrafilter_le_nhds'.2 (fun f hf ↦ ?_)
  have L (g : C_c(E, ℝ)) :
      ∃ x ∈ Icc (-C * ‖(BoundedContinuousFunction.mkOfCompact g.toContinuousMap)‖) (C * ‖(BoundedContinuousFunction.mkOfCompact g.toContinuousMap)‖),
      Tendsto (fun (μ : FiniteMeasure E) ↦ ∫ x, g x ∂μ) f (𝓝 x) := by
    simp only [Tendsto, ← Ultrafilter.coe_map]
    apply IsCompact.ultrafilter_le_nhds' isCompact_Icc
    simp only [neg_mul, Ultrafilter.mem_map]
    filter_upwards [hf] with μ hμ
    simp only [mem_preimage, mem_Icc]
    refine ⟨?_, ?_⟩
    · calc - (C * ‖(BoundedContinuousFunction.mkOfCompact g.toContinuousMap)‖)
      _ ≤ ∫ (x : E), - ‖(BoundedContinuousFunction.mkOfCompact g.toContinuousMap)‖ ∂μ := by
        simp only [integral_const, smul_eq_mul, mul_neg, neg_le_neg_iff]
        gcongr
        exact hμ
      _ ≤ ∫ x, g x ∂μ := by
        gcongr
        · simp
        · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
        · intro x
          apply neg_le_of_abs_le
          exact (BoundedContinuousFunction.mkOfCompact g.toContinuousMap).norm_coe_le_norm x
    · calc ∫ x, g x ∂μ
      _ ≤ ∫ (x : E), ‖(BoundedContinuousFunction.mkOfCompact g.toContinuousMap)‖ ∂μ := by
        gcongr
        · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
        · simp
        · intro x
          apply le_of_abs_le
          exact (BoundedContinuousFunction.mkOfCompact g.toContinuousMap).norm_coe_le_norm x
      _ ≤ C * ‖(BoundedContinuousFunction.mkOfCompact g.toContinuousMap)‖ := by
        simp only [integral_const, smul_eq_mul]
        gcongr
        exact hμ
  choose Λ h₀Λ hΛ using L
  let Λ' : C_c(E, ℝ) →ₚ[ℝ] ℝ :=
  { toFun := Λ
    map_add' g g' := by
      have : Tendsto (fun (μ : FiniteMeasure E) ↦ ∫ x, g x + g' x ∂μ) f (𝓝 (Λ g + Λ g')) := by
        convert (hΛ g).add (hΛ g')
        rw [integral_add]
        · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
        · exact g'.continuous.integrable_of_hasCompactSupport g'.hasCompactSupport
      exact tendsto_nhds_unique (hΛ (g + g')) this
    map_smul' c g := by
      have : Tendsto (fun (μ : FiniteMeasure E) ↦ ∫ x, c • g x ∂μ) f (𝓝 (c • Λ g)) := by
        convert (hΛ g).const_smul c
        rw [integral_smul]
      exact tendsto_nhds_unique (hΛ (c • g)) this
    monotone' g g' hgg' := by
      apply le_of_tendsto_of_tendsto' (hΛ g) (hΛ g') (fun μ ↦ ?_)
      apply integral_mono _ _ hgg'
      · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
      · exact g'.continuous.integrable_of_hasCompactSupport g'.hasCompactSupport }
  let μlim := RealRMK.rieszMeasure Λ'
  have μlim_le : μlim univ ≤ ENNReal.ofReal C := by
    let o : C_c(E, ℝ) :=
    { toFun := 1
      hasCompactSupport' := HasCompactSupport.of_compactSpace 1 }
    have : μlim univ ≤ ENNReal.ofReal (Λ' o) := RealRMK.rieszMeasure_le_of_eq_one Λ'
      (fun x ↦ by simp [o]) isCompact_univ (fun x ↦ by simp [o])
    apply this.trans
    gcongr
    apply le_of_tendsto (hΛ o)
    filter_upwards [hf] with μ hμ using by simpa [o] using hμ
  let μlim' : FiniteMeasure E := ⟨μlim, ⟨μlim_le.trans_lt (by simp)⟩⟩
  refine ⟨μlim', ?_, ?_⟩
  · simp only [mem_setOf_eq, FiniteMeasure.mk_apply, μlim', FiniteMeasure.mass]
    rw [show C = (ENNReal.ofReal ↑C).toNNReal by simp]
    exact ENNReal.toNNReal_mono (by simp) μlim_le
  change Tendsto id f (𝓝 μlim')
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto (fun g ↦ ?_)
  let g' : C_c(E, ℝ) :=
  { toFun := g
    hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
  convert hΛ g'
  change ∫ (x : E), g' x ∂μlim' = Λ g'
  change (∫ x, g' x ∂RealRMK.rieszMeasure Λ') = Λ g'
  rw [RealRMK.integral_rieszMeasure]
  rfl

variable (E) in
/-- In a compact space, the set of finite measures with mass `C` is compact. -/
lemma isCompact_setOf_finiteMeasure_eq_of_compactSpace [CompactSpace E] (C : ℝ≥0) :
    IsCompact {μ : FiniteMeasure E | μ.mass = C} := by
  have : {μ : FiniteMeasure E | μ.mass = C} = {μ | μ.mass ≤ C} ∩ {μ | μ.mass = C} := by grind
  rw [this]
  apply IsCompact.inter_right (isCompact_setOf_finiteMeasure_le_of_compactSpace E C)
  exact isClosed_eq FiniteMeasure.continuous_mass continuous_const

/-- In a compact space, the space of probability measures is also compact. -/
instance [CompactSpace E] : CompactSpace (ProbabilityMeasure E) := by
  constructor
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding E).isCompact_iff.2
  have hrange : Set.range (ProbabilityMeasure.toFiniteMeasure : ProbabilityMeasure E → FiniteMeasure E) =
      {μ : FiniteMeasure E | μ.mass = 1} := by
    ext μ
    constructor
    · rintro ⟨ν,rfl⟩
      exact ProbabilityMeasure.mass_toFiniteMeasure ν
    · intro hμ
      have hmass : (μ : Measure E) univ = 1 := by
        rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, show μ univ = 1 from hμ]
        norm_num
      let ν : ProbabilityMeasure E := ⟨(μ : Measure E),⟨hmass⟩⟩
      exact ⟨ν,by apply FiniteMeasure.toMeasure_injective; rfl⟩
  rw [Set.image_univ, hrange]
  exact isCompact_setOf_finiteMeasure_eq_of_compactSpace E 1


end Paper14.Background
