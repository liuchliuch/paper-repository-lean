import Paper25.TraceNorm
import Paper25.Reduction

/-! # Selected-block filter error and equation (19)

The filter's operator-norm error is propagated through the normalized trace
of its actual selected matrix block. The history regularization contribution
is supplied by the proved matrix reduction, not assumed as a final bias bound.
-/

noncomputable section
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
open Matrix

namespace Paper25

/-- Real normalized trace of a finite square block. -/
def normalizedReTrace {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : ℝ :=
  M.trace.re / (Fintype.card ι : ℝ)

/-- An operator-norm approximation of the actual selected block gives the
same error in its normalized real trace. -/
theorem normalized_re_trace_filter_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Cfilter Cideal : Matrix ι ι ℂ) (hcard : 0 < Fintype.card ι)
    (eps : ℝ) (hfilter : ‖Cfilter - Cideal‖ ≤ eps) :
    |normalizedReTrace Cfilter - normalizedReTrace Cideal| ≤ eps := by
  have h := abs_normalized_re_trace_le_opNorm (Cfilter - Cideal) hcard
  unfold normalizedReTrace
  rw [Matrix.trace_sub, Complex.sub_re, sub_div] at h
  exact h.trans hfilter

/-- Equation (19) for the actual selected filter and ideal blocks. The
algebraic trace identity is the selected-block consequence of equation (17).
The regularization error is derived from the actual history, selector,
channel Frobenius bound, and Lemma 4. -/
theorem eq19_selected_filter_trace {T J K D : ℕ}
    (S : ℕ → Matrix (Fin (K ^ 2) × Fin (D ^ 2))
      (Fin (K ^ 2) × Fin (D ^ 2)) ℂ)
    (hJ : T + 1 ≤ J) (hD : 0 < D)
    (hchannels : CPTPFrobBound S T (K * D))
    (ω η z : Fin (K ^ 2) → ℂ)
    (hω : cinner ω ω = 1) (hz : cinner z z = 1)
    (hrestore : ExactRestoration (chainProd S 0 T) ω η)
    (lam : ℝ) (hlam : 0 < lam)
    (Cfilter Cideal : Matrix (Fin (D ^ 2)) (Fin (D ^ 2)) ℂ)
    (eps : ℝ) (hfilter : ‖Cfilter - Cideal‖ ≤ eps)
    (hselected :
      Cideal.trace = (lam : ℂ) * Matrix.trace
        (historySelector (⟨0, by omega⟩ : Fin J) ⟨T, by omega⟩
          (kronRankOneId (n := D ^ 2) ω z) *
            matrixRegInv (1 - historyShift T J S) lam)) :
    |normalizedReTrace Cfilter - lam * (cinner z η).re| ≤
      (lam ^ 2 / 2) * (J : ℝ) ^ 2 * (K : ℝ) ^ 2 + eps := by
  let A := 1 - historyShift T J S
  let Q := historySelector (⟨0, by omega⟩ : Fin J) ⟨T, by omega⟩
    (kronRankOneId (n := D ^ 2) ω z)
  have hreg := history_normalized_regularization S hJ hD hchannels ω η z
    hω hz hrestore lam hlam
  dsimp only at hreg
  have hnormideal : ‖Cideal.trace / ((D ^ 2 : ℕ) : ℂ) -
      (lam : ℂ) * cinner z η‖ ≤
      lam * ((lam / 2) * (J : ℝ) ^ 2 * (K : ℝ) ^ 2) := by
    have hs : Cideal.trace / ((D ^ 2 : ℕ) : ℂ) =
        (lam : ℂ) * (Matrix.trace (Q * matrixRegInv A lam) / ((D ^ 2 : ℕ) : ℂ)) := by
      rw [hselected]
      ring
    rw [hs, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
    exact mul_le_mul_of_nonneg_left hreg hlam.le
  have hideal : |normalizedReTrace Cideal - lam * (cinner z η).re| ≤
      lam * ((lam / 2) * (J : ℝ) ^ 2 * (K : ℝ) ^ 2) := by
    have h := (Complex.abs_re_le_norm (Cideal.trace / ((D ^ 2 : ℕ) : ℂ) -
      (lam : ℂ) * cinner z η)).trans hnormideal
    simpa only [normalizedReTrace, Fintype.card_fin, Complex.sub_re,
      Complex.div_natCast_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using h
  have hcard : 0 < Fintype.card (Fin (D ^ 2)) := by
    simpa only [Fintype.card_fin] using pow_pos hD 2
  have hfiltertrace := normalized_re_trace_filter_error Cfilter Cideal hcard eps hfilter
  calc
    _ ≤ |normalizedReTrace Cfilter - normalizedReTrace Cideal| +
        |normalizedReTrace Cideal - lam * (cinner z η).re| := abs_sub_le _ _ _
    _ ≤ eps + lam * ((lam / 2) * (J : ℝ) ^ 2 * (K : ℝ) ^ 2) :=
      add_le_add hfiltertrace hideal
    _ = _ := by ring

end Paper25
