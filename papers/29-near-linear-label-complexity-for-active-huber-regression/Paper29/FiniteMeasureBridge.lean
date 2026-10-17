import Paper29.QueryModel
import Paper29.EventTools
import Mathlib.Probability.ProbabilityMassFunction.Constructions

noncomputable section
open scoped BigOperators ENNReal Classical
open MeasureTheory
namespace Paper29.ProcessTools

/-- The explicit finite mass is a genuine PMF, not a probability oracle. -/
def finitePMF {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1) : PMF Ω :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (p ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => hp ω), hs, ENNReal.ofReal_one])

def finiteMeasure {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1) : Measure Ω := (finitePMF p hp hs).toMeasure

instance finiteMeasure_probability {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1) :
    IsProbabilityMeasure (finiteMeasure p hp hs) := by unfold finiteMeasure; infer_instance

theorem finiteMeasure_finset {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1) (E : Finset Ω) :
    finiteMeasure p hp hs E = ENNReal.ofReal (Sampling.eventMass p E) := by
  rw [finiteMeasure, PMF.toMeasure_apply_finset]
  simp only [finitePMF, PMF.ofFintype_apply]
  exact (ENNReal.ofReal_sum_of_nonneg (fun ω _ => hp ω)).symm

theorem finiteMeasure_event {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1) (E : Ω → Prop)
    [DecidablePred E] :
    finiteMeasure p hp hs {ω | E ω} =
      ENNReal.ofReal (Sampling.eventMass p (Finset.univ.filter E)) := by
  have he : {ω | E ω} = (↑(Finset.univ.filter E) : Set Ω) := by ext ω; simp
  rw [he]
  exact finiteMeasure_finset p hp hs _

/-- Converts actual finite event probabilities to the official measurable
nonadaptive correctness predicate. No Borel-in-labels selector is assumed. -/
theorem nonadaptiveCorrect_of_finite_probability {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {n d : ℕ}
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1)
    (alg : QueryModel.NonadaptiveProcedure Ω n d) (A : Matrix (Fin n) (Fin d) ℝ) (ε : ℝ)
    (hgood : ∀ b, (99/100:ℝ) ≤ Sampling.eventMass p (Finset.univ.filter (fun ω =>
      ∀ x, Real.sqrt (objective A b (alg.answer ω b)) ≤ (1+ε)*Real.sqrt (objective A b x)))) :
    QueryModel.NonadaptiveCorrect (finiteMeasure p hp hs) alg A ε := by
  refine ⟨(fun i => (Set.toFinite _).measurableSet), (fun b => measurable_of_countable _), ?_⟩
  intro b
  refine ⟨(Set.toFinite _).measurableSet, ?_⟩
  rw [finiteMeasure_event]
  have hh := ENNReal.ofReal_le_ofReal (hgood b)
  norm_num only [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_ofNat] at hh
  exact hh

end Paper29.ProcessTools
