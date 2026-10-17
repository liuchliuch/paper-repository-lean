import Verification.EuclideanMetric
import Paper17.MetricEquivalence

noncomputable section
open scoped Topology
namespace P17Contract

/-- Proposition 2.5 with the exact Euclidean Hausdorff metric. -/
theorem prop_2_5_euclidean {n : ℕ} (K : EuclideanBody n) (L : ℕ → EuclideanBody n) :
    Filter.Tendsto (fun j => euclideanHausdorffDist K.body.carrier (L j).body.carrier)
      Filter.atTop (𝓝 0) ↔
    Filter.Tendsto (fun j => volSymmDiff K.body.carrier (L j).body.carrier) Filter.atTop (𝓝 0) := by
  have heq : Filter.Tendsto
      (fun j => euclideanHausdorffDist K.body.carrier (L j).body.carrier) Filter.atTop (𝓝 0) ↔
      Filter.Tendsto (fun j => Metric.hausdorffDist K.body.carrier (L j).body.carrier)
        Filter.atTop (𝓝 0) := by
    constructor
    · intro h
      exact squeeze_zero (fun _ => Metric.hausdorffDist_nonneg)
        (fun j => hausdorffDist_le_euclideanHausdorffDist K.body (L j).body) h
    · intro h
      have hm : Filter.Tendsto (fun j => (n : ℝ) *
          Metric.hausdorffDist K.body.carrier (L j).body.carrier) Filter.atTop (𝓝 0) := by
        simpa only [mul_zero] using Filter.Tendsto.mul tendsto_const_nhds h
      exact squeeze_zero (fun _ => Metric.hausdorffDist_nonneg)
        (fun j => euclideanHausdorffDist_le_dimension_mul K.body (L j).body) hm
  exact heq.trans (by
    let K' : Paper17.PosBody n := ⟨K.body.carrier, K.body.convex, K.body.isCompact, K.body.interior_nonempty⟩
    let L' : ℕ → Paper17.PosBody n := fun j =>
      ⟨(L j).body.carrier, (L j).body.convex, (L j).body.isCompact, (L j).body.interior_nonempty⟩
    have hh := Paper17.proposition_2_5 K' L'
    simpa only [K', L', volSymmDiff, vol, Paper17.symmDiffVol, Set.symmDiff_def] using hh)


end P17Contract
