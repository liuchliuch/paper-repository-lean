import Paper29.FiniteMeasureBridge
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

noncomputable section
open scoped BigOperators ENNReal Classical
open MeasureTheory
namespace Paper29.ProcessTools

/-- Probability mass of a finite observable of an arbitrary private seed. -/
def seedCodeMass {Ω E : Type} [MeasurableSpace Ω] (μ : Measure Ω) (code : Ω → E) (e : E) : ℝ :=
  μ.real {ω | code ω=e}

theorem seedCodeMass_nonneg {Ω E : Type} [MeasurableSpace Ω] (μ : Measure Ω) (code : Ω → E) (e : E) :
    0 ≤ seedCodeMass μ code e := ENNReal.toReal_nonneg

theorem seedCodeMass_total {Ω E : Type} [MeasurableSpace Ω] [Fintype E] [MeasurableSpace E]
    [MeasurableSingletonClass E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (code : Ω → E) (hc : Measurable code) : (∑ e,seedCodeMass μ code e) = 1 := by
  have hh := sum_measureReal_preimage_singleton (μ:=μ) (Finset.univ : Finset E)
    (fun e _ => hc (measurableSet_singleton e))
  simpa only [seedCodeMass,Finset.coe_univ,Set.preimage_univ,measureReal_univ_eq_one] using hh

theorem seedCodeMass_event {Ω E : Type} [MeasurableSpace Ω] [Fintype E] [MeasurableSpace E]
    [MeasurableSingletonClass E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (code : Ω → E) (hc : Measurable code) (F : Finset E) :
    Sampling.eventMass (seedCodeMass μ code) F = μ.real (code ⁻¹' F) :=
  sum_measureReal_preimage_singleton (μ:=μ) F (fun e _ => hc (measurableSet_singleton e))

/-- Positive compressed mass always has a real representative seed. -/
theorem seedCodeMass_positive_fiber {Ω E : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (code : Ω → E) {e : E} (he : 0 < seedCodeMass μ code e) :
    ∃ ω,code ω=e := by
  by_contra hn
  have hempty : {ω | code ω=e} = ∅ := by ext ω; simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]; exact fun h => hn ⟨ω,h⟩
  simp [seedCodeMass,hempty] at he

/-- An actual success event can be pushed to a finite code event without
requiring the representative seed itself to be successful. -/
theorem seedCodeMass_success {Ω E : Type} [MeasurableSpace Ω] [Fintype E] [MeasurableSpace E]
    [MeasurableSingletonClass E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (code : Ω → E) (hc : Measurable code) (Success : Ω → Prop)
    (F : Finset E) (hF : ∀ ω,Success ω → code ω∈F) :
    μ.real {ω | Success ω} ≤ Sampling.eventMass (seedCodeMass μ code) F := by
  rw [seedCodeMass_event μ code hc]
  exact measureReal_mono (by intro ω hω; exact hF ω hω)

/-- Exact expectation transfer to a finite decision code, including infinite
query cost. No finite/private-seed assumption is imposed on the original μ. -/
theorem seedCodeMass_lintegral {Ω E : Type} [MeasurableSpace Ω] [Fintype E] [MeasurableSpace E]
    [MeasurableSingletonClass E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (code : Ω → E) (hc : Measurable code) (F : E → ℝ≥0∞) :
    (∑ e,ENNReal.ofReal (seedCodeMass μ code e)*F e) = ∫⁻ ω,F (code ω) ∂μ := by
  rw [← lintegral_map (measurable_of_countable F) hc,lintegral_fintype]
  apply Finset.sum_congr rfl
  intro e _
  rw [Measure.map_apply hc (measurableSet_singleton e)]
  rw [seedCodeMass,Measure.real,ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact mul_comm _ _

def seedRepresentative {Ω E : Type} [Nonempty Ω] (code : Ω → E) (e : E) : Ω :=
  if h : ∃ ω,code ω=e then Classical.choose h else Classical.choice inferInstance

theorem seedRepresentative_spec {Ω E : Type} [Nonempty Ω] (code : Ω → E) {e : E}
    (he : ∃ ω,code ω=e) : code (seedRepresentative code e) = e := by
  simp only [seedRepresentative,dif_pos he]
  exact Classical.choose_spec he

theorem seedRepresentative_observed {Ω E : Type} [Nonempty Ω] (code : Ω → E) (ω : Ω) :
    code (seedRepresentative code (code ω)) = code ω := seedRepresentative_spec code ⟨ω,rfl⟩

end Paper29.ProcessTools
