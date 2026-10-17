import ELV.CanonicalTransducer
import Mathlib.Topology.Algebra.Module.Basic

/-! Countable Hilbert sums of separable Hilbert spaces are separable.
This supplies the explicit separable-private-space attainment clauses. -/
noncomputable section
open scoped ENNReal
namespace ELV.Query
variable {I : Type*} {E : I → Type*} [Countable I]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, TopologicalSpace.SeparableSpace (E i)]

/-- Separability follows from the countable union of the singleton-coordinate
images and the norm-convergent expansion of every lp vector. -/
theorem lp_separable : TopologicalSpace.SeparableSpace (lp E 2) := by
  classical
  let S : Set (lp E 2) := ⋃ i : I, Set.range (lp.single 2 i : E i → lp E 2)
  have hs : TopologicalSpace.IsSeparable S := by
    apply TopologicalSpace.IsSeparable.iUnion
    intro i
    exact TopologicalSpace.isSeparable_range
      (lp.singleContinuousLinearMap (𝕜 := ℂ) (E := E) 2 i).continuous
  have hd : ∀ f : lp E 2, f ∈ (Submodule.span ℂ S).topologicalClosure := by
    intro f
    apply (Submodule.isClosed_topologicalClosure (Submodule.span ℂ S)).mem_of_tendsto
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) f)
    apply Filter.Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro i _
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact Set.mem_iUnion.mpr ⟨i, ⟨f i,rfl⟩⟩
  apply TopologicalSpace.isSeparable_univ_iff.mp
  exact hs.span.closure.mono (fun f _ => hd f)

end ELV.Query
