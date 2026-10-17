import Paper25.HistoryContraction
import Paper25.TraceNorm
import Paper25.SourceBias

/-! The dimension-independent trace regularization step (10), applied to the
actual history inverse and the explicit catalytic selector. -/
noncomputable section
open scoped ComplexOrder
namespace Paper25

lemma history_matrix_isUnit {T J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ℕ → Matrix ι ι ℂ) : IsUnit (1 - historyShift T J S) := by
  let L := historyShift T J S
  exact ⟨⟨1-L, historySum L T,
    one_sub_mul_historySum L (L_nilpotent S),
    historySum_mul_one_sub L (L_nilpotent S)⟩, rfl⟩

/-- Equation (10), including the catalyst-dimension cancellation. The
Frobenius input is a property of consecutive channels, discharged for actual
Kraus channels by `KrausChannel.cptpFrobBound`. No trace approximation is
assumed in this theorem. -/
theorem history_normalized_regularization {T J K D : ℕ}
    (S : ℕ → Matrix (Fin (K^2) × Fin (D^2)) (Fin (K^2) × Fin (D^2)) ℂ)
    (hJ : T + 1 ≤ J) (hD : 0 < D)
    (hchannels : CPTPFrobBound S T (K * D))
    (ω η z : Fin (K^2) → ℂ)
    (hω : cinner ω ω = 1) (hz : cinner z z = 1)
    (hrestore : ExactRestoration (chainProd S 0 T) ω η)
    (lam : ℝ) (hlam : 0 < lam) :
    let A := 1 - historyShift T J S
    let Q := historySelector (⟨0, by omega⟩ : Fin J) ⟨T, by omega⟩
      (kronRankOneId (n := D^2) ω z)
    ‖Matrix.trace (Q * matrixRegInv A lam) / (D^2 : ℕ) - cinner z η‖ ≤
      (lam / 2) * (J : ℝ)^2 * (K : ℝ)^2 := by
  dsimp only
  let A := 1 - historyShift T J S
  let Q := historySelector (⟨0, by omega⟩ : Fin J) ⟨T, by omega⟩
    (kronRankOneId (n := D^2) ω z)
  have hd : (0 : ℝ) < (D : ℝ)^2 := by exact_mod_cast pow_pos hD 2
  have hdC : ((D^2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_ne_zero 2 hD.ne')
  have heq := eq9_history_trace S hJ ω η z hrestore hdC
  have htrace := matrix_trace_regularization_error Q A (history_matrix_isUnit S)
    (historySelector_contraction _ _ ω z hω hz) lam hlam
  have hfrob := history_frob_bound (J := J) S (K*D) hchannels
  have htrace' : ‖Matrix.trace (Q * matrixRegInv A lam) - Matrix.trace (Q * A⁻¹)‖ ≤
      (lam / 2) * (J : ℝ)^2 * ((K : ℝ) * D)^2 := by
    rw [norm_sub_rev]
    apply htrace.trans
    have hf : matrixFrobNormSq A⁻¹ ≤ (J : ℝ)^2 * (K*D : ℕ)^2 := hfrob
    have hh := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ lam/2)
    push_cast at hh
    nlinarith only [hh]
  change ‖Matrix.trace (Q * matrixRegInv A lam) / (D^2 : ℕ) - cinner z η‖ ≤ _
  rw [← heq, ← sub_div, norm_div]
  have hnorm : ‖((D^2 : ℕ) : ℂ)‖ = (D : ℝ)^2 := by
    norm_cast
  rw [hnorm]
  calc
    _ ≤ ((lam / 2) * (J : ℝ)^2 * ((K : ℝ) * D)^2) / (D : ℝ)^2 :=
      div_le_div_of_nonneg_right htrace' hd.le
    _ = (lam / 2) * (J : ℝ)^2 * (K : ℝ)^2 := by
      field_simp
      <;> ring

end Paper25
