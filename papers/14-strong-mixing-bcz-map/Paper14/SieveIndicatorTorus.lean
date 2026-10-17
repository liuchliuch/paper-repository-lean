import Paper14.SieveCounts
import Paper14.SieveTorus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open MeasureTheory Function ProbabilityTheory Set
namespace Paper14
noncomputable section

/-- The actual periodic band indicator, lifted to the period-M circle. -/
def sieveCircleSingle (M : ℕ) (q : ℤ) (ε : ℝ) : AddCircle (M : ℝ) → ℕ :=
  (sieveSingle_periods M q ε).1.lift

@[simp] lemma sieveCircleSingle_coe (M : ℕ) (q : ℤ) (ε u : ℝ) :
    sieveCircleSingle M q ε (u : AddCircle (M : ℝ)) = sieveSingle M q ε u := rfl

lemma measurable_sieveCircleSingle (M : ℕ) [Fact (0 < (M : ℝ))] (q : ℤ) (ε : ℝ) :
    Measurable (sieveCircleSingle M q ε) := by
  have heq : sieveCircleSingle M q ε = fun x : AddCircle (M : ℝ) =>
      sieveSingle M q ε ((AddCircle.measurableEquivIco (T := (M : ℝ)) 0 x : Ico 0 (0+(M : ℝ))) : ℝ) := by
    funext x
    have hx : ((((AddCircle.equivIco (M : ℝ) 0) x : Ico 0 (0+(M : ℝ))) : ℝ) : AddCircle (M : ℝ)) = x :=
      (AddCircle.equivIco (M : ℝ) 0).symm_apply_apply x
    exact (congrArg (sieveCircleSingle M q ε) hx).symm
  rw [heq]
  exact (measurable_sieveSingle M q ε).comp
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIco (T := (M : ℝ)) 0).measurable)

/-- Pairwise independence of the actual single-q sieve indicators under
Haar probability on the period-M torus. -/
theorem sieve_indicators_independent (M : ℕ) [Fact (0 < (M : ℝ))]
    (μ : Measure (AddCircle (M : ℝ))) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    {q q' : ℤ} (hqq : q ≠ q') (ε : ℝ) :
    IndepFun (fun z : AddCircle (M : ℝ) × AddCircle (M : ℝ) =>
      sieveCircleSingle M q ε (q • z.1-z.2))
      (fun z => sieveCircleSingle M q' ε (q' • z.1-z.2)) (μ.prod μ) :=
  sieveTorus_functions_independent μ hqq _ _
    (measurable_sieveCircleSingle M q ε) (measurable_sieveCircleSingle M q' ε)

/-- The torus indicator has exactly the original band-count value on real
representatives of theta and c. -/
lemma sieve_indicator_real_representatives (M : ℕ) (q : ℤ) (ε θ c : ℝ) :
    sieveCircleSingle M q ε (q • (θ : AddCircle (M : ℝ))-(c : AddCircle (M : ℝ))) =
      sieveSingle M q ε ((q : ℝ)*θ-c) := by
  rw [← AddCircle.coe_zsmul,← AddCircle.coe_sub,sieveCircleSingle_coe,zsmul_eq_mul]

end
end Paper14
