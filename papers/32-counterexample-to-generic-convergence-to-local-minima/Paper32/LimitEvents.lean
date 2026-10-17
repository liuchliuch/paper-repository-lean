import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.LocalExtr
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace Paper32
open Set Filter Topology MeasureTheory

variable {E Ω : Type*} [NormedAddCommGroup E] [MeasurableSpace Ω]

/-- The bounded-orbit event of equation (2.3). -/
def boundedOrbitEvent (z : ℕ → Ω → E) : Set Ω :=
  {ω | ∃ C : ℝ, ∀ k, ‖z k ω‖ ≤ C}

/-- The local-minimum-limit event of equation (2.3), with actual local minima. -/
def localMinLimitEvent (h : E → ℝ) (z : ℕ → Ω → E) : Set Ω :=
  {ω | ∃ p, IsLocalMin h p ∧ Tendsto (fun k => z k ω) atTop (𝓝 p)}

lemma bounded_of_converges {u : ℕ → E} {p : E} (hu : Tendsto u atTop (𝓝 p)) :
    ∃ C : ℝ, ∀ k, ‖u k‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto u hu).exists_norm_le
  exact ⟨C, fun k => hC (u k) (mem_range_self k)⟩

/-- A convergent path to a nonminimum belongs to the precise bad-limit event. -/
theorem converges_nonminimum_mem_bad {h : E → ℝ} {z : ℕ → Ω → E} {ω : Ω} {p : E}
    (hp : ¬ IsLocalMin h p) (hz : Tendsto (fun k => z k ω) atTop (𝓝 p)) :
    ω ∈ boundedOrbitEvent z \ localMinLimitEvent h z := by
  refine ⟨bounded_of_converges hz, ?_⟩
  rintro ⟨q, hq, hzq⟩
  have heq : p = q := tendsto_nhds_unique hz hzq
  exact hp (heq ▸ hq)

/-- The event identity used to pass from almost-sure convergence to (2.10). -/
theorem measure_bad_limit_eq_one {h : E → ℝ} {z : ℕ → Ω → E} {p : E}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hp : ¬ IsLocalMin h p)
    (hz : ∀ᵐ ω ∂μ, Tendsto (fun k => z k ω) atTop (𝓝 p)) :
    μ (boundedOrbitEvent z \ localMinLimitEvent h z) = 1 := by
  have heq : boundedOrbitEvent z \ localMinLimitEvent h z =ᵐ[μ] univ := by
    filter_upwards [hz] with ω hω
    exact propext (iff_true_intro (converges_nonminimum_mem_bad hp hω))
  rw [measure_congr heq, measure_univ]

end Paper32
