import Paper14.ReturnMeasure

/-! The second-moment to lower-tail implication used in (18). -/
open MeasureTheory Measure Filter Set
open scoped ENNReal
namespace Paper14

/-- A centered second moment at most `β` bounds the lower tail by `4/β`.
For (18), apply this under the auxiliary torus measure, then use density domination. -/
theorem chebyshev_lower_tail {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (G : α → ℝ) {β : ℝ} (hβ : 0 < β)
    (hG : Integrable (fun x => (G x - β)^2) μ)
    (hvar : (∫ x, (G x - β)^2 ∂μ) ≤ β) :
    μ {x | G x < β / 2} ≤ ENNReal.ofReal (4 / β) := by
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun x => (G x - β)^2)
    (Eventually.of_forall (fun x => sq_nonneg _)) hG (β^2 / 4)
  have hsub : {x | G x < β / 2} ⊆ {x | β^2 / 4 ≤ (G x - β)^2} := by
    intro x hx
    simp only [mem_setOf_eq] at hx ⊢
    nlinarith [sq_nonneg (G x), sq_nonneg (G x - β / 2)]
  have hm : μ.real {x | G x < β / 2} ≤ μ.real {x | β^2 / 4 ≤ (G x - β)^2} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hkey : β^2 / 4 * μ.real {x | G x < β / 2} ≤ β :=
    (mul_le_mul_of_nonneg_left hm (by positivity)).trans (hmark.trans hvar)
  have hbound : μ.real {x | G x < β / 2} ≤ 4 / β := by
    apply (le_div_iff₀ hβ).mpr
    nlinarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {x | G x < β / 2})]
  exact ENNReal.ofReal_le_ofReal hbound

end Paper14
