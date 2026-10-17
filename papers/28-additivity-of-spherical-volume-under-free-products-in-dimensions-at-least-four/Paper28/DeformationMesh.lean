import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! The paper-owned mesh choice handles arbitrarily large boundary masses
in the localized Euclidean cycle refinement. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter
open scoped Topology

def deformationMesh (m : ℕ → ℝ) (i : ℕ) : ℝ := 1/(((i : ℝ)+1)*(1+m i))

theorem deformationMesh_pos (m : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (i : ℕ) :
    0 < deformationMesh m i := by
  have hi := hm i
  unfold deformationMesh
  positivity

theorem deformationMesh_le (m : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (i : ℕ) :
    deformationMesh m i ≤ 1/((i : ℝ)+1) := by
  unfold deformationMesh
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [hm i]

theorem deformationMesh_mul_le (m : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (i : ℕ) :
    deformationMesh m i*m i ≤ 1/((i : ℝ)+1) := by
  have hi := hm i
  unfold deformationMesh
  rw [one_div,mul_comm,← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0 < ((i : ℝ)+1)*(1+m i)) (by positivity)).mpr
  nlinarith

theorem deformationMesh_tendsto_zero (m : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) :
    Tendsto (deformationMesh m) atTop (𝓝 0) := by
  exact squeeze_zero (fun i => (deformationMesh_pos m hm i).le)
    (deformationMesh_le m hm) tendsto_one_div_add_atTop_nhds_zero_nat

theorem deformationMesh_mul_tendsto_zero (m : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) :
    Tendsto (fun i => deformationMesh m i*m i) atTop (𝓝 0) := by
  exact squeeze_zero (fun i => mul_nonneg (deformationMesh_pos m hm i).le (hm i))
    (deformationMesh_mul_le m hm) tendsto_one_div_add_atTop_nhds_zero_nat

end Paper28
