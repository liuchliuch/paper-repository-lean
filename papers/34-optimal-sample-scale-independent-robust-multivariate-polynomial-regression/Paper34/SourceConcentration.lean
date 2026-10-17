import Paper34.StandardConcentration

/-! Source Lemma 6.1 with both concentration contracts supplied by the checked
pinned-library producers. There are no external probability theorem inputs. -/
namespace Paper34
open Set MeasureTheory
noncomputable section

theorem source_lemma_6_1
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m M : ℕ} {rho δ pmin : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law)
    (hm : 0 < m) (hMpos : 0 < M) (hrho0 : 0 ≤ rho) (hrho : rho < 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hpmin : 0 < pmin)
    (hcell : ∀ j : CellIndex n m, pmin ≤ law.real (closedCell j))
    (hM : gridConcentrationConstant rho * pmin⁻¹ *
      Real.log (2 * ((m ^ n : ℕ) : ℝ) / δ) ≤ M) :
    1 - δ ≤ P.real (goodGridEvent (m := m) S) := by
  exact lemma_6_1_good_product_grid S
    (StandardConcentration.bernoulliLowerHalfInput P _)
    (StandardConcentration.bernoulliSubsetHoeffdingInput P _)
    hm hMpos hrho0 hrho hδ0 hδ1 hpmin hcell hM

end
end Paper34
