import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Finite sums of actual Lipschitz maps and local composition with a
smooth map. These give regularity of the actual barycentric retraction. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Metric
open scoped Topology

theorem exists_lipschitz_finset_sum {X H V : Type*} [MetricSpace X]
    [NormedAddCommGroup H] (s : Finset V) (f : V → X → H)
    (hf : ∀ v, ∃ L : NNReal, LipschitzWith L (f v)) :
    ∃ L : NNReal, LipschitzWith L (fun x => ∑ v ∈ s, f v x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0,by simpa only [Finset.sum_empty] using LipschitzWith.const (0 : H)⟩
  | @insert v s hv ih =>
      obtain ⟨Lv,hvL⟩ := hf v
      obtain ⟨Ls,hsL⟩ := ih
      exact ⟨Lv+Ls,by simpa only [Finset.sum_insert hv] using hvL.add hsL⟩

theorem lipschitz_comp_contDiff_neighborhood {X E F : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : X → E) (Lg : NNReal) (hg : LipschitzWith Lg g) (φ : E → F) (x : X)
    (hφ : ContDiffAt ℝ 1 φ (g x)) :
    ∃ L : NNReal, ∃ S : Set X, S ∈ 𝓝 x ∧ LipschitzOnWith L (fun y => φ (g y)) S := by
  obtain ⟨L,V,hV,hLip⟩ := (hφ.hasStrictFDerivAt le_rfl).exists_lipschitzOnWith
  refine ⟨L*Lg,g ⁻¹' V,hg.continuous.continuousAt.preimage_mem_nhds hV,?_⟩
  exact hLip.comp hg.lipschitzOnWith (fun _ h => h)

end Paper28
