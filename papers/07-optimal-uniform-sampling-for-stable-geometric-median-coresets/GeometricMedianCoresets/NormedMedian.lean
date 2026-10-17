import GeometricMedianCoresets.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-! Existence of geometric medians in proper normed spaces. -/
noncomputable section
open scoped BigOperators
namespace GeometricMedianCoresets

def normDist (X : Type*) [SeminormedAddCommGroup X] : Dist X where
  d x y := ‖x - y‖
  nonneg x y := norm_nonneg _
  symm x y := norm_sub_rev _ _
  triangle x y z := by
    simpa only [sub_add_sub_cancel] using norm_add_le (x - z) (z - y)

theorem normDist_cost_continuous {X : Type*} [SeminormedAddCommGroup X]
    {n : ℕ} (P : Dataset X n) : Continuous (normDist X |>.cost P) := by
  unfold Dist.cost normDist
  fun_prop

/-- Continuity and coercivity give an attained median for every nonempty finite dataset. -/
theorem exists_normed_geometricMedian {X : Type*} [NormedAddCommGroup X] [ProperSpace X]
    {n : ℕ} (hn : 0 < n) (P : Dataset X n) :
    ∃ μ, (normDist X).IsGeometricMedian P μ := by
  apply (normDist_cost_continuous P).exists_forall_le' 0
  have ht := (tendsto_norm_cocompact_atTop (E := X)).eventually
    (Filter.eventually_ge_atTop (2 * (normDist X).cost P 0))
  filter_upwards [ht] with z hz
  have htri := triangle_avg (normDist X) hn P z 0
  change ‖z - 0‖ ≤ _ at htri
  rw [sub_zero] at htri
  linarith

end GeometricMedianCoresets
