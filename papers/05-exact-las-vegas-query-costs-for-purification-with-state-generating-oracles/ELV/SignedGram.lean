import ELV.Basic
import ELV.CostIdentities
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Signed-Gram identity and the Cauchy–Schwarz lower bound (Proposition 4.1)
-/

noncomputable section

namespace ELV

namespace SignedGram

/-- Sum of the two query-direction contributions equals (4.2). -/
theorem contrib_sum (a b c d : ℂ) :
    a * (1 - c) + d * (c - 1) = (1 - c) * (a - d) := by
  ring

/-- Opposite labels with `⟨φx,φy⟩ = z ≠ 1`. -/
theorem opposite_label_kernel (z : ℂ) (hz : z ≠ 1) :
    (1 - z) * (1 - z)⁻¹ = 1 := by
  apply mul_inv_cancel₀
  intro hc
  apply hz
  exact (sub_eq_zero.mp hc).symm

/-- Cauchy–Schwarz product-space lower bound of §4.2. -/
theorem cs_lower {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (fm gm fp gp : K) :
    ‖inner ℂ fm fp - inner ℂ gm gp‖ ^ 2
      ≤ (‖fm‖ ^ 2 + ‖gm‖ ^ 2) * (‖fp‖ ^ 2 + ‖gp‖ ^ 2) := by
  -- u = (fm, gm), v = (fp, -gp) in PiLp 2 (fun _ => K)
  have hu2 : ‖(!₂[fm, gm] : PiLp 2 fun _ => K)‖ ^ 2 = ‖fm‖ ^ 2 + ‖gm‖ ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, Fin.sum_univ_zero]
  have hv2 : ‖(!₂[fp, -gp] : PiLp 2 fun _ => K)‖ ^ 2 = ‖fp‖ ^ 2 + ‖gp‖ ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, Fin.sum_univ_zero, norm_neg]
  have hcs : ‖inner ℂ (!₂[fm, gm] : PiLp 2 fun _ => K) (!₂[fp, -gp])‖
      ≤ ‖(!₂[fm, gm] : PiLp 2 fun _ => K)‖ * ‖(!₂[fp, -gp])‖ :=
    norm_inner_le_norm _ _
  have hexp : inner ℂ (!₂[fm, gm] : PiLp 2 fun _ => K) (!₂[fp, -gp])
      = inner ℂ fm fp - inner ℂ gm gp := by
    simp [PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
    ring
  rw [hexp] at hcs
  have hnn : 0 ≤ ‖inner ℂ fm fp - inner ℂ gm gp‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖inner ℂ fm fp - inner ℂ gm gp‖),
    mul_self_nonneg (‖(!₂[fm, gm] : PiLp 2 fun _ => K)‖ * ‖(!₂[fp, -gp])‖),
    hu2, hv2, hcs, norm_nonneg (!₂[fm, gm] : PiLp 2 fun _ => K),
    norm_nonneg (!₂[fp, -gp] : PiLp 2 fun _ => K)]

/-- Equal labels: the kernel factor vanishes. -/
theorem equal_label_cancel (a b : ℂ) :
    (1 - (1 : ℂ)) * (a - b) = 0 := by
  ring

end SignedGram

end ELV
