import Paper38.TransportContinuity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
namespace Paper38.Transport
open MeasureTheory Filter
open scoped ENNReal Topology

/-- The extended quadratic Wasserstein distance, as the square root of the
actual infimum over couplings used throughout this development. -/
def w2 {E : Type*} [MeasurableSpace E] [PseudoEMetricSpace E]
    (μ ν : Measure E) : ℝ≥0∞ := w2sq μ ν ^ (1 / 2 : ℝ)

/-- Continuity of the square root turns squared-cost convergence into the
literal unsquared W₂ convergence in source (2.19). -/
theorem w2_tendsto_of_w2sq_tendsto {E I : Type*} [MeasurableSpace E] [PseudoEMetricSpace E]
    {f : Filter I} (μ ν : I → Measure E) (a b : Measure E)
    (h : Tendsto (fun i => w2sq (μ i) (ν i)) f (𝓝 (w2sq a b))) :
    Tendsto (fun i => w2 (μ i) (ν i)) f (𝓝 (w2 a b)) := h.ennrpow_const _

end Paper38.Transport
