import ELV.Basic
import ELV.CostIdentities

/-!
# Reciprocal rescaling (Section 4.2) — uniform bound only

This module keeps the elementary monotonicity bound used in (4.8).
The full Fock construction, reciprocal inner products and rescaling are
proved in `ELV.FockWitness`, `ELV.BlockRescale` and the operational optimum
modules imported by `ELV`.
-/

noncomputable section

namespace ELV

namespace Rescale

/-- Uniform bound of (4.8): `1/(1-t) ≤ 1/(1-μ)` when `t ≤ μ < 1`. -/
theorem fock_bound (μ t : ℝ) (hμ : μ < 1) (ht : t ≤ μ) (ht0 : 0 ≤ t) :
    1 / (1 - t) ≤ 1 / (1 - μ) := by
  have h1 : 0 < 1 - μ := by linarith
  have h2 : 0 < 1 - t := by linarith
  have hle : 1 - μ ≤ 1 - t := by linarith
  exact one_div_le_one_div_of_le h1 hle

end Rescale

end ELV
