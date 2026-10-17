import Paper14.ReturnCombinatorics
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Measure estimates (7) and (8), with explicit measure-preservation inputs. -/
open MeasureTheory Measure Filter Set Function
open scoped symmDiff ENNReal
namespace Paper14

/-- Markov's inequality at the integer threshold `J+1`; this is the actual
measure estimate used in (7), rather than a positivity surrogate. -/
theorem nat_tail_measure_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (d : α → ℕ) {C : ℝ} (J : ℕ)
    (hd : Integrable (fun x => (d x : ℝ)) μ)
    (hmean : (∫ x, (d x : ℝ) ∂μ) ≤ C) :
    μ {x | J < d x} ≤ ENNReal.ofReal (C / (J + 1)) := by
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun x => (d x : ℝ)) (Eventually.of_forall (fun x => Nat.cast_nonneg _))
    hd ((J : ℝ) + 1)
  have hset : {x | (J : ℝ) + 1 ≤ (d x : ℝ)} = {x | J < d x} := by
    ext x
    simp only [mem_setOf_eq]
    exact_mod_cast (Nat.succ_le_iff : J + 1 ≤ d x ↔ J < d x)
  rw [hset] at hmark
  have hpos : (0 : ℝ) < J + 1 := by positivity
  have hbound : (μ {x | J < d x}).toReal ≤ C / (J + 1) := by
    apply (le_div_iff₀ hpos).mpr
    simpa only [measureReal_def, mul_comm] using hmark.trans hmean
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {x | J < d x})]
  exact ENNReal.ofReal_le_ofReal hbound

/-- Almost invariance (8). The only dynamical inputs are preservation by `T`
and preservation of the restricted measure by the induced map. -/
theorem excessLevel_almost_invariant {α : Type*} [MeasurableSpace α]
    {T : α → α} {μ : Measure α} {Y : Set α}
    (hT : MeasurePreserving T μ μ) (hY : MeasurableSet Y)
    (hTY : MeasurePreserving (inducedMap T Y) (μ.restrict Y) (μ.restrict Y))
    (n j : ℕ) :
    μ (excessLevel T Y n j ∆ (T ⁻¹' excessLevel T Y n j)) ≤ 3 * μ Yᶜ := by
  have hpre : MeasurableSet (T ⁻¹' Yᶜ) := hT.measurable hY.compl
  have hpremeasure : μ (T ⁻¹' Yᶜ) = μ Yᶜ := hT.measure_preimage hY.compl.nullMeasurableSet
  have hlast : μ (Y ∩ ((inducedMap T Y)^[n]) ⁻¹' (T ⁻¹' Yᶜ)) ≤ μ Yᶜ := by
    calc
      _ = (μ.restrict Y) (((inducedMap T Y)^[n]) ⁻¹' (T ⁻¹' Yᶜ)) := by
        rw [Measure.restrict_apply ((hTY.iterate n).measurable hpre), inter_comm]
      _ = (μ.restrict Y) (T ⁻¹' Yᶜ) :=
        (hTY.iterate n).measure_preimage hpre.nullMeasurableSet
      _ ≤ μ (T ⁻¹' Yᶜ) := Measure.restrict_apply_le _ _
      _ = μ Yᶜ := hpremeasure
  calc
    _ ≤ μ (Yᶜ ∪ T ⁻¹' Yᶜ ∪ (Y ∩ ((inducedMap T Y)^[n]) ⁻¹' (T ⁻¹' Yᶜ))) :=
      measure_mono (excessLevel_symmDiff_subset T Y n j)
    _ ≤ μ Yᶜ + μ (T ⁻¹' Yᶜ) + μ (Y ∩ ((inducedMap T Y)^[n]) ⁻¹' (T ⁻¹' Yᶜ)) :=
      (measure_union_le _ _).trans (add_le_add_right (measure_union_le _ _) _)
    _ ≤ μ Yᶜ + μ Yᶜ + μ Yᶜ := by rw [hpremeasure]; exact add_le_add_left hlast _
    _ = 3 * μ Yᶜ := by ring

end Paper14
