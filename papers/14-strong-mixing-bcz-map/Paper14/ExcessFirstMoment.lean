import Paper14.ReturnMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Paper (6): the first-moment calculation from Kac's formula.
Kac's theorem and preservation by the induced map remain explicit inputs;
this module does not assert that these inputs have been established. -/
open MeasureTheory Measure Filter Set Function
namespace Paper14

/-- Integration of the return-time sum against an invariant measure. -/
theorem integral_Rn {α : Type*} [MeasurableSpace α] {T : α → α} {Y : Set α}
    {ν : Measure α}
    (hTY : MeasurePreserving (inducedMap T Y) ν ν)
    (hr : Integrable (fun y => (firstReturnTime T Y y : ℝ)) ν) (n : ℕ) :
    (∫ y, (Rn T Y n y : ℝ) ∂ν) = n * ∫ y, (firstReturnTime T Y y : ℝ) ∂ν := by
  have hcomp (i : ℕ) : Integrable
      (fun y => (firstReturnTime T Y ((inducedMap T Y)^[i] y) : ℝ)) ν :=
    (hTY.iterate i).integrable_comp_of_integrable hr
  simp only [Rn, Nat.cast_sum]
  rw [integral_finset_sum _ (fun i _ => hcomp i)]
  have hterm (i : ℕ) :
      (∫ y, (firstReturnTime T Y ((inducedMap T Y)^[i] y) : ℝ) ∂ν) =
        ∫ y, (firstReturnTime T Y y : ℝ) ∂ν := by
    have hmap := integral_map (μ := ν) (hTY.iterate i).measurable.aemeasurable
      (f := fun y => (firstReturnTime T Y y : ℝ))
    rw [(hTY.iterate i).map_eq] at hmap
    exact (hmap hr.aestronglyMeasurable).symm
  simp_rw [hterm]
  simp

/-- Paper (6), after normalization of Kac's return-time identity. -/
theorem integral_excess_of_return_mean {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {ν : Measure α} [IsProbabilityMeasure ν]
    (hTY : MeasurePreserving (inducedMap T Y) ν ν)
    (hr : Integrable (fun y => (firstReturnTime T Y y : ℝ)) ν)
    (hrec : ∀ᵐ y ∂ν, ∀ i : ℕ, 0 < firstReturnTime T Y ((inducedMap T Y)^[i] y))
    {ρ : ℝ} (hmean : (∫ y, (firstReturnTime T Y y : ℝ) ∂ν) = ρ⁻¹) (n : ℕ) :
    (∫ y, (excessDn T Y n y : ℝ) ∂ν) = n * (ρ⁻¹ - 1) := by
  have hRint : Integrable (fun y => (Rn T Y n y : ℝ)) ν := by
    simpa only [Rn, Nat.cast_sum] using
      integrable_finset_sum (Finset.range n)
        (fun i _ => (hTY.iterate i).integrable_comp_of_integrable hr)
  have hcast : (fun y => (excessDn T Y n y : ℝ)) =ᵐ[ν]
      (fun y => (Rn T Y n y : ℝ) - n) := by
    filter_upwards [hrec] with y hy
    have hle : n ≤ Rn T Y n y := by
      calc
        n = ∑ _i ∈ Finset.range n, 1 := by simp
        _ ≤ ∑ i ∈ Finset.range n, firstReturnTime T Y ((inducedMap T Y)^[i] y) :=
          Finset.sum_le_sum (fun i _ => hy i)
    exact Nat.cast_sub hle
  rw [integral_congr_ae hcast, integral_sub hRint (integrable_const _),
    integral_Rn hTY hr n, hmean]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]
  ring

end Paper14
