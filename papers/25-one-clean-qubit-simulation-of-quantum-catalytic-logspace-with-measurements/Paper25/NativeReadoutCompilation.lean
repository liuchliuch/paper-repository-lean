import Paper25.ReflectionCompilation
import Paper25.CoherentFilterCircuit
import Paper25.Synthesis

/-! The extra trace-cancellation bit and final clean probe are compiled into
honest local gate lists. The scalar phase in the reflection is retained. -/
noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace Paper25.OperationalModel.LocalCompilation

def dataWires (q : ℕ) : Fin q ↪ Fin (q+1) where
  toFun := Fin.succ
  inj' := Fin.succ_injective q

lemma dataWires_inactive (q : ℕ) (x y : Basis (q+1)) :
    Inactive (dataWires q) x y ↔ x 0 = y 0 := by
  constructor
  · intro h
    apply h 0
    rintro ⟨i,hi⟩
    exact Fin.succ_ne_zero i hi
  · intro h j hj
    by_cases he : j = 0
    · simpa [he] using h
    · obtain ⟨i,rfl⟩ := Fin.eq_succ_of_ne_zero he
      exact False.elim (hj ⟨i,rfl⟩)

def physicalData {q : ℕ} (U : Operator q) : Operator (q+1) :=
  (Matrix.fromBlocks U 0 0 U).submatrix (probeBasis q) (probeBasis q)

lemma dataWires_lift {q : ℕ} (U : Operator q) :
    (placementOfEmbedding (dataWires q)).lift U = physicalData U := by
  ext x y
  simp only [lift_apply, active_placementOfEmbedding_eq, dataWires_inactive]
  change U (fun i => x i.succ) (fun i => y i.succ) * (if x 0 = y 0 then 1 else 0) = _
  have hb : ∀ b : Fin 2, b = 0 ∨ b = 1 := by intro b; fin_cases b <;> simp
  rcases hb (x 0) with hx | hx <;> rcases hb (y 0) with hy | hy <;>
    simp [physicalData, phaseLift, probeBasis, probeTensor, OneCleanQubit.tensorBasis,
      Matrix.fromBlocks, hx,hy]

def dataCircuit {G : EffectiveGateSet} {q : ℕ} (C : EffectiveCircuit G q) :
    EffectiveCircuit G (q+1) := embedCircuit (placementOfEmbedding (dataWires q)) C

lemma dataCircuit_matrix {G : EffectiveGateSet} {q : ℕ} (C : EffectiveCircuit G q) :
    (dataCircuit C).matrix = physicalData C.matrix := by
  rw [dataCircuit, embedCircuit_matrix, dataWires_lift]

/-- Apply W on both b branches, then apply R only on b=1. -/
def traceCancellationCircuit {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (W R : EffectiveCircuit G q) : EffectiveCircuit G (q+1) :=
  dataCircuit W ++ controlledCircuit conv R

theorem traceCancellationCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G)
    {q : ℕ} (W R : EffectiveCircuit G q) :
    (traceCancellationCircuit conv W R).matrix =
      (Matrix.fromBlocks W.matrix 0 0 (R.matrix*W.matrix)).submatrix
        (probeBasis q) (probeBasis q) := by
  rw [traceCancellationCircuit, EffectiveCircuit.matrix_append, controlledCircuit_matrix,
    dataCircuit_matrix, physicalData, physicalControl, Matrix.submatrix_mul_equiv]
  congr 1
  simp [OneCleanQubit.controlled, phaseLift, Matrix.fromBlocks_multiply]

theorem traceCancellationCircuit_reflected {G : EffectiveGateSet} (conv : GateConvention G)
    {q : ℕ} (W R : EffectiveCircuit G q) (P : Operator q)
    (hR : R.matrix = projectorReflection P) :
    (traceCancellationCircuit conv W R).matrix =
      (OneCleanQubit.reflectedTraceUnitary P W.matrix).submatrix
        (probeBasis q) (probeBasis q) := by
  rw [traceCancellationCircuit_matrix, hR]
  simp only [OneCleanQubit.reflectedTraceUnitary, projectorReflection, two_smul]

theorem traceCancellationCircuit_length {G : EffectiveGateSet} (conv : GateConvention G)
    {q : ℕ} (W R : EffectiveCircuit G q) :
    (traceCancellationCircuit conv W R).length ≤ W.length+conv.bound*R.length := by
  rw [traceCancellationCircuit, List.length_append, dataCircuit, embedCircuit_length]
  exact Nat.add_le_add_left (controlledCircuit_length conv R) _

lemma probability_reindex {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] [Nonempty a] [Nonempty b]
    (e : a ≃ b) (V : Matrix b b ℂ) (hV : OneCleanQubit.Unitary V) :
    OneCleanQubit.probZero (OneCleanQubit.output (V.submatrix e e)) =
      OneCleanQubit.probZero (OneCleanQubit.output V) := by
  have hleft := OneCleanQubit.output_signedBias _ (unitary_submatrix e V hV)
  have hright := OneCleanQubit.output_signedBias V hV
  rw [OneCleanQubit.trace_test _ (unitary_submatrix e V hV),
    trace_submatrix_equiv, Fintype.card_congr e] at hleft
  rw [OneCleanQubit.trace_test _ hV] at hright
  linarith

lemma circuit_reindex {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (V : Matrix b b ℂ) :
    OneCleanQubit.circuit (V.submatrix e e) =
      (OneCleanQubit.circuit V).submatrix (e.sumCongr e) (e.sumCongr e) := by
  have hH : (OneCleanQubit.hadamard : OneCleanQubit.ProbeMatrix a) =
      (OneCleanQubit.hadamard : OneCleanQubit.ProbeMatrix b).submatrix
        (e.sumCongr e) (e.sumCongr e) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [OneCleanQubit.hadamard, Matrix.submatrix_apply, Matrix.fromBlocks,
        Matrix.one_apply, e.injective.eq_iff]
  have hC : OneCleanQubit.controlled (V.submatrix e e) =
      (OneCleanQubit.controlled V).submatrix (e.sumCongr e) (e.sumCongr e) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [OneCleanQubit.controlled, Matrix.submatrix_apply, Matrix.fromBlocks,
        Matrix.one_apply, e.injective.eq_iff]
  simp only [OneCleanQubit.circuit, hH, hC, Matrix.submatrix_mul_equiv]

/-- Compile-time operator error changes the actual target Born probability
by at most twice that error, after a specified mixed-register coordinate map. -/
theorem target_accept_error {G : EffectiveGateSet} (C : EffectiveTargetCircuit G)
    {b : Type*} [Fintype b] [DecidableEq b] [Nonempty b]
    (e : Basis C.mixedQubits ≃ b) (V : Matrix b b ℂ) (hV : OneCleanQubit.Unitary V)
    (tau : ℝ)
    (herror : ‖C.matrix - (OneCleanQubit.circuit V).submatrix
      (e.sumCongr e) (e.sumCongr e)‖ ≤ tau) :
    |C.accept - OneCleanQubit.probZero (OneCleanQubit.output V)| ≤ 2*tau := by
  have h := Synthesis.probZero_evolve_error C.matrix
    (OneCleanQubit.circuit (V.submatrix e e)) OneCleanQubit.input C.unitary
      (OneCleanQubit.circuit_unitary _ (unitary_submatrix e V hV))
      OneCleanQubit.input_posSemidef OneCleanQubit.input_trace
  have hp := probability_reindex e V hV
  change |C.accept - OneCleanQubit.probZero (OneCleanQubit.output (V.submatrix e e))| ≤ _ at h
  rw [hp, circuit_reindex] at h
  exact h.trans (mul_le_mul_of_nonneg_left herror (by norm_num))

/-- The exact native final target has the operational probability of Lemma 6,
with one clean probe and q+1 mixed qubits, including b. -/
theorem reflectedReadout_accept {G : EffectiveGateSet} (conv : GateConvention G)
    {q : ℕ} (W R : EffectiveCircuit G q) (P : Operator q)
    (hP : P.IsHermitian) (hPP : P*P=P) (hR : R.matrix=projectorReflection P) :
    (readoutCircuit conv (traceCancellationCircuit conv W R)).accept =
      OneCleanQubit.probZero (OneCleanQubit.output
        (OneCleanQubit.reflectedTraceUnitary P W.matrix)) := by
  rw [readoutCircuit_accept, traceCancellationCircuit_reflected conv W R P hR]
  exact probability_reindex (probeBasis q) _
    (OneCleanQubit.reflectedTraceUnitary_unitary P W.matrix hP hPP W.unitary)

end Paper25.OperationalModel.LocalCompilation
