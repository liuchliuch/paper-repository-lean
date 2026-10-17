import PUT.CollisionWorkspace

/-! # Compiling entire testers into standard function-query algorithms -/
noncomputable section
open scoped InnerProductSpace
namespace PUT.CollisionQuerySimulation
open PUT.QueryModel PUT.CollisionCircuit

section Measurements
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Change the orthonormal encoding of a projective measurement. -/
def conjugateMeasurement (e : E ≃ₗᵢ[ℂ] F) (P : Measurement F) : Measurement E where
  reject := (e.symm : F →L[ℂ] E).comp (P.reject.comp (e : E →L[ℂ] F))
  idem := by intro x; simp [P.idem]
  hermitian := by
    intro x y
    change ⟪e.symm (P.reject (e x)),y⟫_ℂ = ⟪x,e.symm (P.reject (e y))⟫_ℂ
    rw [← e.inner_map_map, e.apply_symm_apply, P.hermitian]
    rw [← e.inner_map_map x, e.apply_symm_apply]

@[simp] theorem conjugateMeasurement_probability (e : E ≃ₗᵢ[ℂ] F)
    (P : Measurement F) (x : E) :
    (conjugateMeasurement e P).rejectionProbability x = P.rejectionProbability (e x) := by
  simp [conjugateMeasurement, Measurement.rejectionProbability]

/-- Conjugate every fixed operation, while keeping the actual query directions. -/
def conjugateCircuit (e : E ≃ₗᵢ[ℂ] F) (C : Circuit F) : Circuit E where
  initial := e.symm C.initial
  initial_norm := by simp [C.initial_norm]
  free := fun t => (e.trans (C.free t)).trans e.symm
  direction := C.direction
  measurement := conjugateMeasurement e C.measurement

@[simp] theorem conjugateCircuit_state (e : E ≃ₗᵢ[ℂ] F) (C : Circuit F)
    (U : F ≃ₗᵢ[ℂ] F) (T : ℕ) :
    (conjugateCircuit e C).state ((e.trans U).trans e.symm) T = e.symm (C.state U T) := by
  induction T with
  | zero => simp [conjugateCircuit, Circuit.state]
  | succ t ht =>
    simp only [Circuit.state, ht]
    cases hdir : C.direction t <;>
      simp [conjugateCircuit, hdir, queryUnitary, LinearIsometryEquiv.symm_trans]

@[simp] theorem conjugateCircuit_probability (e : E ≃ₗᵢ[ℂ] F) (C : Circuit F)
    (U : F ≃ₗᵢ[ℂ] F) (T : ℕ) :
    (conjugateCircuit e C).rejectProbability ((e.trans U).trans e.symm) T =
      C.rejectProbability U T := by
  unfold Circuit.rejectProbability
  rw [conjugateCircuit_state]
  change (conjugateMeasurement e C.measurement).rejectionProbability (e.symm (C.state U T)) = _
  rw [conjugateMeasurement_probability, e.apply_symm_apply]

end Measurements

variable {D : ℕ} [NeZero D]
variable {B : Type*} [Fintype B] [DecidableEq B]

/-- Repeat the same projective measurement on each ancillary block. -/
def blockMeasurement {I : Type*} [Fintype I] (P : Measurement (EuclideanSpace ℂ B)) :
    Measurement (Register I (EuclideanSpace ℂ B)) where
  reject := workspaceOperator P.reject
  idem := by intro x; ext i : 1; exact P.idem _
  hermitian := by
    intro x y
    simp only [PiLp.inner_apply, workspaceOperator_apply, P.hermitian]

/-- A final projective measurement for the compiled algorithm. -/
def compiledMeasurement (P : Measurement (EuclideanSpace ℂ B)) : Measurement (QuerySpace B D) :=
  conjugateMeasurement curry (blockMeasurement P)

@[simp] theorem compiledMeasurement_clean (P : Measurement (EuclideanSpace ℂ B))
    (v : EuclideanSpace ℂ B) :
    (compiledMeasurement (D := D) P).rejectionProbability (clean v) =
      P.rejectionProbability v := by
  rw [compiledMeasurement, conjugateMeasurement_probability]
  unfold Measurement.rejectionProbability
  have he : (blockMeasurement (I := Fin D × Fin D) P).reject (curry (clean v)) =
      curry (clean (P.reject v)) := by
    rw [curry_clean, curry_clean]
    ext q : 1
    by_cases hq : q = (0,0) <;> simp [blockMeasurement, hq]
  rw [he, LinearIsometryEquiv.norm_map, clean_norm]

def Implements.queryProgram {U} {N : ℕ} (h : Implements (B := B) (D := D) U N) :
    Direction → Program B D
  | .forward => h.program
  | .inverse => h.program.inverse

@[simp] theorem Implements.queryProgram_count {U} {N : ℕ}
    (h : Implements (B := B) (D := D) U N) (q : Direction) :
    (h.queryProgram q).queries = N := by
  cases q <;> simp [Implements.queryProgram, h.count]

@[simp] theorem Implements.queryProgram_correct {U} {N : ℕ}
    (h : Implements (B := B) (D := D) U N) (q : Direction) (f : Fin D → Fin D)
    (v : EuclideanSpace ℂ B) :
    (h.queryProgram q).operation f (clean v) = clean (queryUnitary (U f) q v) := by
  cases q with
  | forward => exact h.correct f v
  | inverse => exact h.inverse.correct f v

/-- Replace each actual oracle call of the original fixed-query circuit. -/
def compileCircuit {U} {N : ℕ} (C : Circuit (EuclideanSpace ℂ B))
    (h : Implements (B := B) (D := D) U N) : ℕ → Program B D
  | 0 => [.free (freeExtension (C.free 0))]
  | t+1 => compileCircuit C h t ++ h.queryProgram (C.direction t) ++
    [.free (freeExtension (C.free (t+1)))]

theorem compileCircuit_queries {U} {N : ℕ} (C : Circuit (EuclideanSpace ℂ B))
    (h : Implements (B := B) (D := D) U N) (T : ℕ) :
    (compileCircuit C h T).queries = N*T := by
  induction T with
  | zero => rfl
  | succ t ht =>
    simp only [compileCircuit, Program.queries_append, h.queryProgram_count, ht]
    simp [Program.queries, Nat.mul_succ]

theorem compileCircuit_correct {U} {N : ℕ} (C : Circuit (EuclideanSpace ℂ B))
    (h : Implements (B := B) (D := D) U N) (T : ℕ) (f : Fin D → Fin D) :
    (compileCircuit C h T).operation f (clean C.initial) = clean (C.state (U f) T) := by
  induction T with
  | zero => exact freeExtension_clean (C.free 0) C.initial
  | succ t ht =>
    simp only [compileCircuit, Program.operation_append, LinearIsometryEquiv.trans_apply,
      ht, h.queryProgram_correct, Program.operation, Gate.operation,
      freeExtension_clean, Circuit.state]
    rfl

/-- Standard quantum function-query algorithm, with actual unitary word,
normalized input, projective measurement, and its syntactic query count. -/
structure FunctionAlgorithm (B : Type*) [Fintype B] (D : ℕ) where
  initial : QuerySpace B D
  initial_norm : ‖initial‖ = 1
  measurement : Measurement (QuerySpace B D)
  program : Program B D

def FunctionAlgorithm.rejectProbability (A : FunctionAlgorithm B D) (f : Fin D → Fin D) : ℝ :=
  A.measurement.rejectionProbability (A.program.operation f A.initial)

def simulateCircuit {U} {N : ℕ} (C : Circuit (EuclideanSpace ℂ B))
    (h : Implements (B := B) (D := D) U N) (T : ℕ) : FunctionAlgorithm B D where
  initial := clean C.initial
  initial_norm := by rw [clean_norm]; exact C.initial_norm
  measurement := compiledMeasurement C.measurement
  program := compileCircuit C h T

@[simp] theorem simulateCircuit_queries {U} {N : ℕ} (C : Circuit (EuclideanSpace ℂ B))
    (h : Implements (B := B) (D := D) U N) (T : ℕ) :
    (simulateCircuit C h T).program.queries = N*T := compileCircuit_queries C h T

@[simp] theorem simulateCircuit_probability {U} {N : ℕ} (C : Circuit (EuclideanSpace ℂ B))
    (h : Implements (B := B) (D := D) U N) (T : ℕ) (f : Fin D → Fin D) :
    (simulateCircuit C h T).rejectProbability f = C.rejectProbability (U f) T := by
  simp only [simulateCircuit, FunctionAlgorithm.rejectProbability, compileCircuit_correct,
    compiledMeasurement_clean, Circuit.rejectProbability]

end PUT.CollisionQuerySimulation
