import Paper14.InvariantMarginals
import Paper14.MeasureLimits
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

/-- The positive-excess classification gives the product domination in
(11), including the case of zero intermediate mass. -/
theorem product_lower_of_components {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {ν : Measure (E × E)} [IsProbabilityMeasure ν]
    (η : ℕ → Measure (E × E)) (hsum : Measure.sum η = ν)
    (hpos : ∀ j, 0 < j → η j = η j univ • μ.prod μ) :
    (1-η 0 univ) • μ.prod μ ≤ ν := by
  let R : Measure (E × E) := Measure.sum (fun j => η (j+1))
  have hsplit : η 0 + R = ν := by
    rw [← hsum]
    ext A hA
    change η 0 A+Measure.sum (fun j => η (j+1)) A = Measure.sum η A
    rw [Measure.sum_apply _ hA,Measure.sum_apply _ hA]
    exact (tsum_eq_zero_add' (f := fun j : ℕ => η j A) ENNReal.summable).symm
  have hzero : η 0 univ ≤ 1 := by
    have hh := Measure.le_sum η 0 univ
    simpa only [hsum,measure_univ] using hh
  have hp0 : η 0 univ ≠ ⊤ := (hzero.trans_lt ENNReal.one_lt_top).ne
  have hmass : η 0 univ+R univ = 1 := by
    have hh := congrArg (fun κ : Measure (E × E) => κ univ) hsplit
    simpa only [Measure.add_apply,measure_univ] using hh
  have hRmass : R univ = 1-η 0 univ :=
    (ENNReal.sub_eq_of_eq_add_rev hp0 hmass.symm).symm
  have hRprod : R = R univ • μ.prod μ := by
    ext A hA
    rw [Measure.smul_apply,smul_eq_mul]
    change Measure.sum (fun j => η (j+1)) A = Measure.sum (fun j => η (j+1)) univ*μ.prod μ A
    rw [Measure.sum_apply _ hA,Measure.sum_apply _ MeasurableSet.univ,← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro j
    have hh := congrArg (fun κ : Measure (E × E) => κ A) (hpos (j+1) (Nat.succ_pos j))
    simpa only [Measure.smul_apply,smul_eq_mul] using hh
  rw [← hRmass,← hRprod,← hsplit]
  apply Measure.le_iff.mpr
  intro A hA
  exact le_add_of_nonneg_left (zero_le _)

/-- The final alpha-to-infinity order argument: approximate product
lower bounds determine a probability measure exactly. -/
theorem probability_eq_of_approx_product_dom {E : Type*} [MeasurableSpace E]
    (prodμ ν : Measure E) [IsProbabilityMeasure prodμ] [IsProbabilityMeasure ν]
    (hdom : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal (1-ε) • prodμ ≤ ν) : ν = prodμ := by
  have hle : prodμ ≤ ν := by
    apply Measure.le_iff.mpr
    intro A hA
    have heps : Tendsto (fun n : ℕ => 1/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    have hscalar : Tendsto (fun n : ℕ => ENNReal.ofReal (1-1/((n+1 : ℕ) : ℝ))) atTop (𝓝 1) := by
      simpa using ENNReal.tendsto_ofReal
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub heps)
    have hh := ENNReal.Tendsto.mul_const (b := prodμ A) hscalar (Or.inl one_ne_zero)
    apply le_of_tendsto (by simpa only [one_mul] using hh)
    exact Eventually.of_forall (fun n => (hdom (1/((n+1 : ℕ) : ℝ)) (by positivity)) A)
  exact (Measure.eq_of_le_of_measure_univ_eq hle (by simp)).symm

end
end Paper14
