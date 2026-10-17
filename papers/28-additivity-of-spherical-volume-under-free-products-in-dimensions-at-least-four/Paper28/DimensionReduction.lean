import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Linarith

/-! The dimension estimate that explains the n >= 4 threshold in S2.p4. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

/-- A subspace of dimension at least four retains at least two dimensions
when intersected with the orthogonal complement of a space of dimension <= 2. -/
theorem orthogonal_slice_dim (E W : Submodule ℝ H)
    (hE : 4 ≤ Module.finrank ℝ E) (hW : Module.finrank ℝ W ≤ 2) :
    2 ≤ Module.finrank ℝ (E ⊓ Wᗮ : Submodule ℝ H) := by
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq E Wᗮ
  have horth := W.finrank_add_finrank_orthogonal
  have hle : Module.finrank ℝ (E ⊔ Wᗮ : Submodule ℝ H) ≤ Module.finrank ℝ H :=
    Submodule.finrank_le _
  omega

end Paper28
