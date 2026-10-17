import Paper22.CapacityCompact
import Paper22.PetzEquality

/-! Compact density operators and continuity of positive matrix powers on them. -/
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace Paper22
local instance densityCompactMatrixCStarAlgebra (d : ℕ) :
    CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) where
variable {d : ℕ}

def densityOperators (d : ℕ) : Set (Matrix (Fin d) (Fin d) ℂ) := {ρ | IsDensity ρ}

theorem isClosed_densityOperators (d : ℕ) : IsClosed (densityOperators d) := by
  have h : IsClosed ({ρ : Matrix (Fin d) (Fin d) ℂ | 0 ≤ ρ} ∩ {ρ | ρ.trace=1}) :=
    (isClosed_le continuous_const continuous_id).inter (isClosed_eq (by fun_prop) continuous_const)
  convert h using 1
  ext ρ
  exact ⟨fun hρ => ⟨hρ.nonneg,hρ.trace_one⟩,fun hρ => ⟨hρ.1.posSemidef,hρ.2⟩⟩

theorem isCompact_densityOperators (d : ℕ) : IsCompact (densityOperators d) := by
  apply (isCompact_effects (d := d)).of_isClosed_subset (isClosed_densityOperators d)
  intro ρ hρ
  refine ⟨hρ.nonneg,?_⟩
  exact CFC.le_one (fun x hx => (hρ.spectrum_real_subset_Icc hx).2) hρ.isHermitian

theorem density_matrix_rpow_eq_real_cfc {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : IsDensity ρ) (p : ℝ) : CFC.rpow ρ p=cfc (fun t : ℝ => t^p) ρ := by
  rw [CFC.rpow,cfc_nnreal_eq_real (fun t => t^p) ρ hρ.nonneg]
  apply cfc_congr
  intro t ht
  simp only [NNReal.coe_rpow,Real.coe_toNNReal _ (hρ.spectrum_real_subset_Icc ht).1]

theorem continuousOn_density_rpow {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (fun ρ : Matrix (Fin d) (Fin d) ℂ => CFC.rpow ρ p) (densityOperators d) := by
  have h : ContinuousOn (fun ρ : Matrix (Fin d) (Fin d) ℂ => cfc (fun t : ℝ => t^p) ρ)
      (densityOperators d) := continuousOn_id.cfc isCompact_Icc (fun t : ℝ => t^p)
    (fun ρ hρ => hρ.spectrum_real_subset_Icc) (fun ρ hρ => hρ.isHermitian)
    ((Real.continuous_rpow_const hp).continuousOn)
  apply h.congr
  intro ρ hρ
  exact density_matrix_rpow_eq_real_cfc hρ p

theorem continuous_density_testing_trace (A : Matrix (Fin d) (Fin d) ℂ)
    {p : ℝ} (hp : 0 ≤ p) :
    Continuous (fun σ : {σ // IsDensity (σ : Matrix (Fin d) (Fin d) ℂ)} =>
      (A*CFC.rpow σ.val p).trace.re) := by
  have hr : Continuous (fun σ : {σ // IsDensity (σ : Matrix (Fin d) (Fin d) ℂ)} => CFC.rpow σ.val p) :=
    continuousOn_iff_continuous_restrict.mp (continuousOn_density_rpow hp)
  exact Complex.continuous_re.comp (continuous_const.mul hr).matrix_trace

end Paper22
end
