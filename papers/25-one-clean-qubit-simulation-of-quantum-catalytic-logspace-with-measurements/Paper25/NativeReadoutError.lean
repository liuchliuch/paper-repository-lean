import Paper25.NativeReadoutCompilation
import Paper25.MatrixCompilationNorm
import Paper25.SourceWalkCompilation

/-!
# Dimension-free error propagation through the actual final readout

The only approximation input is the component error of the compiled walk/filter
unitary. The trace-cancellation branch, its controlled readout, and both actual
Hadamards propagate that error without a dimension factor. The final factor two
comes from the proved perturbation bound for the actual Born probability.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Paper25.NativeReadoutError
open OperationalModel OperationalModel.LocalCompilation

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Two direct-sum branches retain the larger common error bound. -/
lemma pairBlocks_error (A B A' B' : Matrix n n ℂ) (ε : ℝ)
    (hA : ‖A-A'‖ ≤ ε) (hB : ‖B-B'‖ ≤ ε) :
    ‖Matrix.fromBlocks A 0 0 B - Matrix.fromBlocks A' 0 0 B'‖ ≤ ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hA
  have hs : ‖selectMatrix (![A,B] : Fin 2 → Matrix n n ℂ) -
      selectMatrix (![A',B'] : Fin 2 → Matrix n n ℂ)‖ ≤ ε := by
    apply MatrixCompilationNorm.selectMatrix_error _ _ ε hε
    intro j
    fin_cases j
    · exact hA
    · exact hB
  rw [← SourceWalkCompilation.pairBlocks, ← SourceWalkCompilation.pairBlocks,
    MatrixCompilationNorm.submatrix_equiv_error]
  exact hs

/-- Reflection on the second branch is unitary, so it does not amplify the
component error. No unitary premise on the compared matrices is needed here. -/
theorem reflectedTraceUnitary_error (P W W' : Matrix n n ℂ)
    (hP : P.IsHermitian) (hPP : P*P=P) (ε : ℝ) (hW : ‖W-W'‖ ≤ ε) :
    ‖OneCleanQubit.reflectedTraceUnitary P W -
      OneCleanQubit.reflectedTraceUnitary P W'‖ ≤ ε := by
  apply pairBlocks_error _ _ _ _ ε hW
  rw [← mul_sub]
  calc
    _ ≤ ‖(2 : ℂ) • P - 1‖ * ‖W-W'‖ := norm_mul_le _ _
    _ ≤ 1 * ‖W-W'‖ := mul_le_mul_of_nonneg_right
      (Synthesis.unitary_opNorm_le (OneCleanQubit.reflection_unitary P hP hPP)) (norm_nonneg _)
    _ ≤ ε := by simpa only [one_mul] using hW

/-- Controlling a unitary approximation adds an exact identity branch. -/
theorem controlled_error (V V' : Matrix n n ℂ) (ε : ℝ) (hV : ‖V-V'‖ ≤ ε) :
    ‖OneCleanQubit.controlled V - OneCleanQubit.controlled V'‖ ≤ ε := by
  apply pairBlocks_error _ _ _ _ ε ?_ hV
  simpa only [sub_self, norm_zero] using (norm_nonneg _).trans hV

/-- The two Hadamards and the added clean-probe control have no error factor. -/
theorem circuit_error (V V' : Matrix n n ℂ) (ε : ℝ) (hV : ‖V-V'‖ ≤ ε) :
    ‖OneCleanQubit.circuit V - OneCleanQubit.circuit V'‖ ≤ ε := by
  have hcontrol := controlled_error V V' ε hV
  have hH : ‖(OneCleanQubit.hadamard : OneCleanQubit.ProbeMatrix n)‖ ≤ 1 :=
    Synthesis.unitary_opNorm_le OneCleanQubit.hadamard_unitary
  simp only [OneCleanQubit.circuit]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  calc
    _ ≤ ‖OneCleanQubit.hadamard * (OneCleanQubit.controlled V - OneCleanQubit.controlled V')‖ *
        ‖(OneCleanQubit.hadamard : OneCleanQubit.ProbeMatrix n)‖ := norm_mul_le _ _
    _ ≤ ‖OneCleanQubit.hadamard * (OneCleanQubit.controlled V - OneCleanQubit.controlled V')‖ * 1 :=
      mul_le_mul_of_nonneg_left hH (norm_nonneg _)
    _ ≤ ‖(OneCleanQubit.hadamard : OneCleanQubit.ProbeMatrix n)‖ *
        ‖OneCleanQubit.controlled V - OneCleanQubit.controlled V'‖ := by
      simpa only [mul_one] using norm_mul_le (OneCleanQubit.hadamard : OneCleanQubit.ProbeMatrix n)
        (OneCleanQubit.controlled V - OneCleanQubit.controlled V')
    _ ≤ 1 * ‖OneCleanQubit.controlled V - OneCleanQubit.controlled V'‖ :=
      mul_le_mul_of_nonneg_right hH (norm_nonneg _)
    _ ≤ ε := by simpa only [one_mul] using hcontrol

/-- The operational trace-test probability is Lipschitz in its input unitary,
with constant two and no dependence on the mixed-register dimension. -/
theorem output_probability_error [Nonempty n] (V V' : Matrix n n ℂ)
    (hV : OneCleanQubit.Unitary V) (hV' : OneCleanQubit.Unitary V')
    (ε : ℝ) (herror : ‖V-V'‖ ≤ ε) :
    |OneCleanQubit.probZero (OneCleanQubit.output V) -
      OneCleanQubit.probZero (OneCleanQubit.output V')| ≤ 2*ε := by
  have h := Synthesis.probZero_evolve_error (OneCleanQubit.circuit V)
    (OneCleanQubit.circuit V') OneCleanQubit.input
    (OneCleanQubit.circuit_unitary V hV) (OneCleanQubit.circuit_unitary V' hV')
    OneCleanQubit.input_posSemidef OneCleanQubit.input_trace
  exact h.trans (mul_le_mul_of_nonneg_left (circuit_error V V' ε herror) (by norm_num))

/-- Algebraic compatibility with any specified finite coordinate equivalence. -/
lemma reflectedTraceUnitary_reindex {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (P W : Matrix b b ℂ) :
    OneCleanQubit.reflectedTraceUnitary (P.submatrix e e) (W.submatrix e e) =
      (OneCleanQubit.reflectedTraceUnitary P W).submatrix (e.sumCongr e) (e.sumCongr e) := by
  have hR : (2 : ℂ) • P.submatrix e e - 1 = ((2 : ℂ) • P - 1).submatrix e e := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, e.injective.eq_iff]
  simp only [OneCleanQubit.reflectedTraceUnitary, hR, Matrix.submatrix_mul_equiv]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

/-- Full matrix error of the actual trace-cancellation gate list. -/
theorem traceCancellationCircuit_error {G : EffectiveGateSet} (conv : GateConvention G)
    {q : ℕ} (W R : EffectiveCircuit G q) (P W' : Operator q)
    (hP : P.IsHermitian) (hPP : P*P=P) (hR : R.matrix=projectorReflection P)
    (ε : ℝ) (hW : ‖W.matrix-W'‖ ≤ ε) :
    ‖(traceCancellationCircuit conv W R).matrix -
      (OneCleanQubit.reflectedTraceUnitary P W').submatrix (probeBasis q) (probeBasis q)‖ ≤ ε := by
  rw [traceCancellationCircuit_reflected conv W R P hR,
    MatrixCompilationNorm.submatrix_equiv_error]
  exact reflectedTraceUnitary_error P W.matrix W' hP hPP ε hW

/-- Full matrix error of the actual final clean-probe readout gate list. -/
theorem readoutCircuit_error {G : EffectiveGateSet} (conv : GateConvention G)
    {q : ℕ} (W R : EffectiveCircuit G q) (P W' : Operator q)
    (hP : P.IsHermitian) (hPP : P*P=P) (hR : R.matrix=projectorReflection P)
    (ε : ℝ) (hW : ‖W.matrix-W'‖ ≤ ε) :
    ‖(show OneCleanQubit.ProbeMatrix (Basis (q+1)) from
        (readoutCircuit conv (traceCancellationCircuit conv W R)).matrix) -
      (OneCleanQubit.circuit (OneCleanQubit.reflectedTraceUnitary P W')).submatrix
        ((probeBasis q).sumCongr (probeBasis q)) ((probeBasis q).sumCongr (probeBasis q))‖ ≤ ε := by
  rw [readoutCircuit_matrix, traceCancellationCircuit_reflected conv W R P hR,
    circuit_reindex, MatrixCompilationNorm.submatrix_equiv_error]
  exact circuit_error _ _ ε (reflectedTraceUnitary_error P W.matrix W' hP hPP ε hW)

/-- Final acceptance error, derived solely from the compiled component error.
The reflection and both readout Hadamards are actual gate-list semantics. -/
theorem reflectedReadout_accept_error {G : EffectiveGateSet} (conv : GateConvention G)
    {q : ℕ} (W R : EffectiveCircuit G q) (P W' : Operator q)
    (hP : P.IsHermitian) (hPP : P*P=P) (hR : R.matrix=projectorReflection P)
    (hW' : OneCleanQubit.Unitary W') (ε : ℝ) (hW : ‖W.matrix-W'‖ ≤ ε) :
    |(readoutCircuit conv (traceCancellationCircuit conv W R)).accept -
      OneCleanQubit.probZero (OneCleanQubit.output (OneCleanQubit.reflectedTraceUnitary P W'))| ≤ 2*ε := by
  rw [reflectedReadout_accept conv W R P hP hPP hR]
  exact output_probability_error _ _
    (OneCleanQubit.reflectedTraceUnitary_unitary P W.matrix hP hPP W.unitary)
    (OneCleanQubit.reflectedTraceUnitary_unitary P W' hP hPP hW') ε
    (reflectedTraceUnitary_error P W.matrix W' hP hPP ε hW)

/-- The same actual final readout bound when the ideal operator uses another
finite basis, with an explicit coordinate map for the compiled component. -/
theorem reflectedReadout_accept_error_reindex {G : EffectiveGateSet} (conv : GateConvention G)
    {q : ℕ} {b : Type*} [Fintype b] [DecidableEq b] [Nonempty b]
    (e : Basis q ≃ b) (W R : EffectiveCircuit G q) (P W' : Matrix b b ℂ)
    (hP : P.IsHermitian) (hPP : P*P=P)
    (hR : R.matrix=projectorReflection (P.submatrix e e))
    (hW' : OneCleanQubit.Unitary W') (ε : ℝ) (hW : ‖W.matrix-W'.submatrix e e‖ ≤ ε) :
    |(readoutCircuit conv (traceCancellationCircuit conv W R)).accept -
      OneCleanQubit.probZero (OneCleanQubit.output (OneCleanQubit.reflectedTraceUnitary P W'))| ≤ 2*ε := by
  have hPP' : P.submatrix e e * P.submatrix e e = P.submatrix e e := by
    rw [Matrix.submatrix_mul_equiv, hPP]
  have h := reflectedReadout_accept_error conv W R (P.submatrix e e) (W'.submatrix e e)
    (hP.submatrix e) hPP' hR (unitary_submatrix e W' hW') ε hW
  rw [reflectedTraceUnitary_reindex] at h
  have hp := probability_reindex (e.sumCongr e) (OneCleanQubit.reflectedTraceUnitary P W')
    (OneCleanQubit.reflectedTraceUnitary_unitary P W' hP hPP hW')
  rwa [hp] at h

end Paper25.NativeReadoutError
