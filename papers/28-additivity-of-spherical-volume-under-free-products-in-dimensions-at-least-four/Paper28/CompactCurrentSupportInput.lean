import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Basic

/-! The disclosed support part of the standard compact AK integral-current
object API. Current objects are supplied by the published theory; the file
does not define currents as an abstract chain model. These generic laws do
not contain any map, deformation, mass estimate or paper-owned conclusion. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
universe u v

structure CompactIntegralCurrentSupportInput (X : Type u) (metric : MetricSpace X) where
  Current : ℕ → AddCommGrpCat.{v}
  support : {k : ℕ} → Current k → Set X
  support_compact : ∀ {k} (C : Current k),
    @IsCompact X metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace (support C)
  support_zero : ∀ k, support (0 : Current k) = ∅
  support_add_subset : ∀ {k} (C D : Current k), support (C+D) ⊆ support C ∪ support D
  support_neg_subset : ∀ {k} (C : Current k), support (-C) ⊆ support C

end Paper28
