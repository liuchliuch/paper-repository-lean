import Paper25.LocalCompilation
import Paper25.BlockEncoding

/-! Hermitian dilation and compression-walk compilation from actual local
gate lists. The h selector occupies the first physical qubit. -/
noncomputable section
open Matrix
namespace Paper25.OperationalModel.LocalCompilation

def firstWire (q : ℕ) : Fin 1 ↪ Fin (q+1) where
  toFun _ := 0
  inj' _ _ _ := Subsingleton.elim _ _

lemma firstWire_inactive (q : ℕ) (x y : Basis (q+1)) :
    Inactive (firstWire q) x y ↔
      (fun i : Fin q => x i.succ) = (fun i : Fin q => y i.succ) := by
  constructor
  · intro h
    funext i
    apply h i.succ
    rintro ⟨j,hj⟩
    exact Fin.succ_ne_zero i hj.symm
  · intro h j hj
    have hj0 : j ≠ 0 := by
      intro he
      exact hj ⟨0,he.symm⟩
    obtain ⟨i,rfl⟩ := Fin.eq_succ_of_ne_zero hj0
    exact congrFun h i

def probeFlip {n : Type*} [Fintype n] [DecidableEq n] :
    OneCleanQubit.ProbeMatrix n := Matrix.fromBlocks 0 1 1 0

def physicalFlip (q : ℕ) : Operator (q+1) :=
  (probeFlip : OneCleanQubit.ProbeMatrix (Basis q)).submatrix (probeBasis q) (probeBasis q)

lemma firstWire_X (q : ℕ) :
    (placementOfEmbedding (firstWire q)).lift pauliX = physicalFlip q := by
  ext x y
  simp only [lift_apply, active_placementOfEmbedding_eq, firstWire_inactive]
  change (if x 0 = y 0 then 0 else 1) *
    (if (fun i : Fin q => x i.succ) = (fun i : Fin q => y i.succ) then 1 else 0) = _
  have hb : ∀ b : Fin 2, b = 0 ∨ b = 1 := by intro b; fin_cases b <;> simp
  have hx := hb (x 0)
  have hy := hb (y 0)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    simp [physicalFlip, probeFlip, probeBasis, probeTensor, OneCleanQubit.tensorBasis,
      hx,hy,Matrix.fromBlocks,Matrix.one_apply]

def flipCircuit {G : EffectiveGateSet} (conv : GateConvention G) (q : ℕ) :
    EffectiveCircuit G (q+1) := embedCircuit (placementOfEmbedding (firstWire q)) conv.X

lemma flipCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) (q : ℕ) :
    (flipCircuit conv q).matrix = physicalFlip q := by
  rw [flipCircuit, embedCircuit_matrix, conv.X_matrix, firstWire_X]

lemma probe_dilation_product {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) :
    probeFlip * OneCleanQubit.controlled U * probeFlip *
      OneCleanQubit.controlled U.conjTranspose * probeFlip = hermitianDilation U := by
  simp [probeFlip, OneCleanQubit.controlled, hermitianDilation,
    Matrix.fromBlocks_multiply, Matrix.star_eq_conjTranspose]

/-- X, controlled adjoint, X, controlled U, X is exactly the Hermitian
dilation, including its scalar phase and with no extra workspace. -/
def dilationCircuit {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) : EffectiveCircuit G (q+1) :=
  flipCircuit conv q ++ controlledCircuit conv (adjointCircuit conv C) ++
    flipCircuit conv q ++ controlledCircuit conv C ++ flipCircuit conv q

theorem dilationCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) :
    (dilationCircuit conv C).matrix =
      (hermitianDilation C.matrix).submatrix (probeBasis q) (probeBasis q) := by
  simp only [dilationCircuit, EffectiveCircuit.matrix_append, flipCircuit_matrix,
    controlledCircuit_matrix, adjointCircuit_matrix, physicalFlip, physicalControl,
    Matrix.submatrix_mul_equiv]
  rw [← probe_dilation_product C.matrix]
  simp only [Matrix.submatrix_mul_equiv, mul_assoc]

theorem dilationCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) :
    (dilationCircuit conv C).length ≤
      3 * conv.X.length + (conv.bound^2+conv.bound)*C.length := by
  simp only [dilationCircuit, List.length_append, flipCircuit, embedCircuit_length]
  have ha := adjointCircuit_length conv C
  have hc := controlledCircuit_length conv C
  have hac := controlledCircuit_length conv (adjointCircuit conv C)
  nlinarith

/-- The compression reflection follows the dilation in chronological order.
Its own local implementation is supplied by the separate zero-test circuit. -/
def walkCircuit {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (encoder : EffectiveCircuit G q) (reflection : EffectiveCircuit G (q+1)) :
    EffectiveCircuit G (q+1) := dilationCircuit conv encoder ++ reflection

theorem walkCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (encoder : EffectiveCircuit G q) (reflection : EffectiveCircuit G (q+1)) :
    (walkCircuit conv encoder reflection).matrix =
      reflection.matrix * (hermitianDilation encoder.matrix).submatrix
        (probeBasis q) (probeBasis q) := by
  rw [walkCircuit, EffectiveCircuit.matrix_append, dilationCircuit_matrix]

end Paper25.OperationalModel.LocalCompilation
