import Paper25.CPTP
import Paper25.Liouville

/-!
# Kraus semantics for the source operations (Appendix A.1)

A source channel carries an explicit finite Kraus family and the full identity
`∑ K† K = I`. In particular, trace preservation is required on every input
operator, not merely on one input state or through the scalar trace of its Choi
matrix. Composition and arbitrary reference extensions retain this identity.
The older `IsCPTP` certificate is used only as a consequence for Lemma 3.
-/
noncomputable section
open scoped ComplexOrder ComplexConjugate
open Kronecker
namespace Paper25

/-- The unnormalized Choi matrix of a rectangular finite Kraus family. -/
def krausChoi {ι ο κ : Type*} [Fintype κ]
    (K : κ → Matrix ο ι ℂ) : Matrix (ο × ι) (ο × ι) ℂ :=
  fun a b => ∑ r, K r a.1 a.2 * conj (K r b.1 b.2)

/-- Complete positivity follows from the Kraus representation, without an
assumption about reachable source states. -/
theorem krausChoi_posSemidef {ι ο κ : Type*} [Fintype ι] [Fintype ο] [Fintype κ]
    (K : κ → Matrix ο ι ℂ) : (krausChoi K).PosSemidef := by
  classical
  have h : ∀ s : Finset κ,
      (∑ r ∈ s, Matrix.vecMulVec (fun a : ο × ι => K r a.1 a.2)
        (star (fun a : ο × ι => K r a.1 a.2))).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (Matrix.PosSemidef.zero :
        (0 : Matrix (ο × ι) (ο × ι) ℂ).PosSemidef)
    | @insert r s hr ih =>
      simpa only [Finset.sum_insert hr] using
        (Matrix.posSemidef_vecMulVec_self_star (fun a : ο × ι => K r a.1 a.2)).add ih
  convert h Finset.univ using 1
  ext a b
  simp only [krausChoi, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  rfl

/-- An actual finite-dimensional quantum channel, with Kraus completeness. -/
structure KrausChannel (ι : Type*) [Fintype ι] [DecidableEq ι] where
  Outcome : Type
  outcomes : Fintype Outcome
  kraus : Outcome → Matrix ι ι ℂ
  complete : ∑ r, (kraus r).conjTranspose * kraus r = 1
attribute [instance] KrausChannel.outcomes

namespace KrausChannel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Action on arbitrary operators; no positivity hypothesis is used. -/
def act (C : KrausChannel ι) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ r, C.kraus r * X * (C.kraus r).conjTranspose

/-- Matrix of the channel in the matrix-unit basis. -/
def liouville (C : KrausChannel ι) : Matrix (ι × ι) (ι × ι) ℂ :=
  fun a b => ∑ r, C.kraus r a.1 b.1 * conj (C.kraus r a.2 b.2)

/-- Choi matrix associated to the actual Kraus channel. -/
def choi (C : KrausChannel ι) : Matrix (ι × ι) (ι × ι) ℂ :=
  krausChoi C.kraus

theorem choi_posSemidef (C : KrausChannel ι) : C.choi.PosSemidef :=
  krausChoi_posSemidef C.kraus

/-- Full partial-trace identity, including all off-diagonal input coordinates. -/
theorem choi_partialTrace (C : KrausChannel ι) (i j : ι) :
    ∑ a, C.choi (a, i) (a, j) = if i = j then 1 else 0 := by
  classical
  have hc := congrArg (fun M : Matrix ι ι ℂ => M j i) C.complete
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply] at hc
  simp only [choi, krausChoi]
  rw [Finset.sum_comm]
  simpa only [mul_comm, eq_comm] using hc

/-- Kraus completeness preserves the trace of every operator. -/
theorem trace_preserving (C : KrausChannel ι) (X : Matrix ι ι ℂ) :
    Matrix.trace (C.act X) = Matrix.trace X := by
  classical
  unfold act
  rw [Matrix.trace_sum]
  conv_lhs => arg 2; ext r; rw [Matrix.trace_mul_cycle]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, C.complete, one_mul]

/-- The identity channel. -/
def identity : KrausChannel ι where
  Outcome := Unit
  outcomes := inferInstance
  kraus _ := 1
  complete := by simp

@[simp] theorem identity_act (X : Matrix ι ι ℂ) :
    (identity : KrausChannel ι).act X = X := by simp [act, identity]

/-- Unitary conjugation; the full `U†U=I` identity is the sole gate premise. -/
def unitary (U : Matrix ι ι ℂ) (hU : U.conjTranspose * U = 1) : KrausChannel ι where
  Outcome := Unit
  outcomes := inferInstance
  kraus _ := U
  complete := by simpa using hU

@[simp] theorem unitary_act (U : Matrix ι ι ℂ) (hU : U.conjTranspose * U = 1)
    (X : Matrix ι ι ℂ) : (unitary U hU).act X = U * X * U.conjTranspose := by
  simp [unitary, act]

/-- `C.comp D` applies `D` first and `C` second. -/
def comp (C D : KrausChannel ι) : KrausChannel ι where
  Outcome := C.Outcome × D.Outcome
  outcomes := inferInstance
  kraus r := C.kraus r.1 * D.kraus r.2
  complete := by
    classical
    simp only [Matrix.conjTranspose_mul, Fintype.sum_prod_type]
    calc
      (∑ r, ∑ s, (D.kraus s).conjTranspose * (C.kraus r).conjTranspose *
          (C.kraus r * D.kraus s)) =
          ∑ s, (D.kraus s).conjTranspose *
            (∑ r, (C.kraus r).conjTranspose * C.kraus r) * D.kraus s := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s _
        simp only [Matrix.mul_sum, Matrix.sum_mul]
        apply Finset.sum_congr rfl
        intro r _
        noncomm_ring
      _ = 1 := by simp [C.complete, D.complete]

theorem comp_act (C D : KrausChannel ι) (X : Matrix ι ι ℂ) :
    (C.comp D).act X = C.act (D.act X) := by
  classical
  simp only [act, comp, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
    Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  noncomm_ring

/-- Matrix-unit vectorization connects the concrete channel action and Liouville matrix. -/
theorem liouville_action (C : KrausChannel ι) (X : Matrix ι ι ℂ) (a b : ι) :
    C.act X a b = ∑ p : ι × ι, C.liouville (a, b) p * X p.1 p.2 := by
  classical
  simp only [act, liouville, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.star_def, Finset.sum_mul, Fintype.sum_prod_type]
  conv_lhs => arg 2; ext r; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The action on a matrix unit is the corresponding Liouville column. -/
theorem act_single (C : KrausChannel ι) (i j a b : ι) :
    C.act (Matrix.single i j 1) a b = C.liouville (a, b) (i, j) := by
  classical
  simp only [act, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single, Matrix.of_apply, liouville, Complex.star_def]
  simp [ite_and]

/-- Channel composition is matrix multiplication in Liouville form. -/
theorem liouville_comp (C D : KrausChannel ι) :
    (C.comp D).liouville = C.liouville * D.liouville := by
  classical
  ext ⟨a, b⟩ ⟨i, j⟩
  rw [← act_single, comp_act, liouville_action]
  simp_rw [D.act_single]
  rfl

/-- Positive operators remain positive under the Kraus action. -/
theorem act_posSemidef (C : KrausChannel ι) (X : Matrix ι ι ℂ)
    (hX : X.PosSemidef) : (C.act X).PosSemidef := by
  classical
  have h : ∀ s : Finset C.Outcome,
      (∑ r ∈ s, C.kraus r * X * (C.kraus r).conjTranspose).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℂ).PosSemidef)
    | @insert r s hr ih =>
      simpa only [Finset.sum_insert hr] using
        (hX.mul_mul_conjTranspose_same (C.kraus r)).add ih
  exact h Finset.univ

/-- Extend a channel by the identity on an arbitrary inaccessible reference. -/
def extendRight (C : KrausChannel ι) (ρ : Type*) [Fintype ρ] [DecidableEq ρ] :
    KrausChannel (ι × ρ) where
  Outcome := C.Outcome
  outcomes := inferInstance
  kraus r := Matrix.kronecker (C.kraus r) (1 : Matrix ρ ρ ℂ)
  complete := by
    classical
    change (∑ r, (Matrix.kronecker (C.kraus r) (1 : Matrix ρ ρ ℂ)).conjTranspose *
      Matrix.kronecker (C.kraus r) (1 : Matrix ρ ρ ℂ)) = 1
    simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, one_mul]
    calc
      (∑ r, Matrix.kronecker ((C.kraus r).conjTranspose * C.kraus r)
          (1 : Matrix ρ ρ ℂ)) =
          Matrix.kronecker (∑ r, (C.kraus r).conjTranspose * C.kraus r)
            (1 : Matrix ρ ρ ℂ) := by
        ext i j
        simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.sum_mul]
      _ = 1 := by rw [C.complete, Matrix.kronecker, Matrix.one_kronecker_one]

/-- Identity extension on the left, used for an outcome work bit. -/
def extendLeft (C : KrausChannel ι) (ρ : Type*) [Fintype ρ] [DecidableEq ρ] :
    KrausChannel (ρ × ι) where
  Outcome := C.Outcome
  outcomes := inferInstance
  kraus r := Matrix.kronecker (1 : Matrix ρ ρ ℂ) (C.kraus r)
  complete := by
    classical
    change (∑ r, (Matrix.kronecker (1 : Matrix ρ ρ ℂ) (C.kraus r)).conjTranspose *
      Matrix.kronecker (1 : Matrix ρ ρ ℂ) (C.kraus r)) = 1
    simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, one_mul]
    calc
      (∑ r, Matrix.kronecker (1 : Matrix ρ ρ ℂ)
          ((C.kraus r).conjTranspose * C.kraus r)) =
          Matrix.kronecker (1 : Matrix ρ ρ ℂ)
            (∑ r, (C.kraus r).conjTranspose * C.kraus r) := by
        ext i j
        simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.mul_sum]
      _ = 1 := by rw [C.complete, Matrix.kronecker, Matrix.one_kronecker_one]

/-- A reference extension acts independently on every reference matrix block.
The off-diagonal reference blocks are included in this identity. -/
theorem extendRight_act_block (C : KrausChannel ι) (ρ : Type*)
    [Fintype ρ] [DecidableEq ρ] (X : Matrix (ι × ρ) (ι × ρ) ℂ)
    (a b : ι) (r s : ρ) :
    (C.extendRight ρ).act X (a, r) (b, s) =
      C.act (fun i j => X (i, r) (j, s)) a b := by
  classical
  simp only [act, extendRight, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kronecker_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Complex.star_def]
  simp [apply_ite]

/-- Explicit complete positivity: positivity is preserved after adjoining any
finite reference, including input correlations across the source/reference cut. -/
theorem completely_positive (C : KrausChannel ι) (ρ : Type*)
    [Fintype ρ] [DecidableEq ρ] (X : Matrix (ι × ρ) (ι × ρ) ℂ)
    (hX : X.PosSemidef) : ((C.extendRight ρ).act X).PosSemidef :=
  (C.extendRight ρ).act_posSemidef X hX

/-- Choi total trace is derived from the full partial trace, not used as a
replacement for trace preservation. -/
theorem choi_trace (C : KrausChannel ι) :
    Matrix.trace C.choi = (Fintype.card ι : ℂ) := by
  classical
  rw [Matrix.trace, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Matrix.diag_apply]
  simp_rw [C.choi_partialTrace]
  simp

/-- Bridge to the legacy Frobenius-bound certificate. -/
theorem toIsCPTP {d : ℕ} (C : KrausChannel (Fin d)) : IsCPTP C.liouville where
  choi_posSemidef := by simpa only [liouvilleToChoi, liouville, choi, krausChoi,
    Matrix.of_apply] using C.choi_posSemidef
  choi_trace := by simpa only [liouvilleToChoi, liouville, choi, krausChoi,
    Matrix.of_apply, Fintype.card_fin] using C.choi_trace

/-- Lemma 3 for an actual, fully trace-preserving source channel. -/
theorem liouville_frob_bound {d : ℕ} (C : KrausChannel (Fin d)) :
    entryNormSq C.liouville ≤ (d : ℝ) ^ 2 :=
  lemma_3_cptp_frob_bound C.liouville C.toIsCPTP

/-- Computational-basis dephasing of a source qubit. -/
def dephase : KrausChannel (Fin 2) where
  Outcome := Fin 2
  outcomes := inferInstance
  kraus u := Matrix.single u u 1
  complete := by
    change (∑ u : Fin 2, (Matrix.single u u (1 : ℂ)).conjTranspose *
      Matrix.single u u 1) = 1
    simp only [Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same, one_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.sum_apply, Fin.sum_univ_two, Matrix.single, Matrix.one_apply]

/-- Erase a source qubit to `|0⟩`, retaining no classical transcript. -/
def reset : KrausChannel (Fin 2) where
  Outcome := Fin 2
  outcomes := inferInstance
  kraus u := Matrix.single 0 u 1
  complete := by
    change (∑ u : Fin 2, (Matrix.single 0 u (1 : ℂ)).conjTranspose *
      Matrix.single 0 u 1) = 1
    simp only [Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same, one_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.sum_apply, Fin.sum_univ_two, Matrix.single, Matrix.one_apply]

/-- Dephasing is the nonselective measurement instrument on all operators. -/
theorem dephase_act (X : Matrix (Fin 2) (Fin 2) ℂ) :
    dephase.act X = Matrix.diagonal (fun i => X i i) := by
  simp only [act, dephase, Matrix.conjTranspose_single, star_one,
    Matrix.single_mul_mul_single, one_mul, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sum_apply, Fin.sum_univ_two, Matrix.single, Matrix.diagonal_apply]

/-- The reset channel has the advertised semantics `X ↦ |0⟩⟨0| Tr(X)`. -/
theorem reset_act (X : Matrix (Fin 2) (Fin 2) ℂ) :
    reset.act X = Matrix.single 0 0 (Matrix.trace X) := by
  simp only [act, reset, Matrix.conjTranspose_single, star_one,
    Matrix.single_mul_mul_single, one_mul, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sum_apply, Fin.sum_univ_two, Matrix.single, Matrix.trace]

/-- The source dephasing channel is exactly the Liouville matrix used in the
three-ancilla block encoding. -/
theorem dephase_liouville : dephase.liouville = dephasingL := by
  ext ⟨a, b⟩ ⟨i, j⟩
  change (∑ u : Fin 2, (Matrix.single u u (1 : ℂ)) a i *
    conj ((Matrix.single u u (1 : ℂ)) b j)) = dephasingL (a, b) (i, j)
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [dephasingL, pauliI, pauliZ, Matrix.kronecker, Fin.sum_univ_two,
      Matrix.single, Matrix.one_apply, Matrix.kronecker_apply]

/-- The source reset channel is exactly the Liouville matrix used in (11). -/
theorem reset_liouville : reset.liouville = resetL := by
  ext ⟨a, b⟩ ⟨i, j⟩
  change (∑ u : Fin 2, (Matrix.single 0 u (1 : ℂ)) a i *
    conj ((Matrix.single 0 u (1 : ℂ)) b j)) = resetL (a, b) (i, j)
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [resetL, Fin.sum_univ_two, Matrix.single]

/-- The unitary source primitive has Liouville matrix `U ⊗ conj U`. -/
theorem unitary_liouville {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U.conjTranspose * U = 1) : (unitary U hU).liouville = unitaryL U := by
  ext a b
  simp [liouville, unitary, unitaryL, Matrix.kronecker, Matrix.kronecker_apply]

lemma fin2_one_add_one : (1 : Fin 2) + 1 = 0 := by decide

/-- CNOT copies a computational-basis value into the outcome work bit. -/
def copyGate : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a b => if a.1 = b.1 ∧ a.2 = b.1 + b.2 then 1 else 0

theorem copyGate_unitary : copyGate.conjTranspose * copyGate = 1 := by
  ext ⟨a, b⟩ ⟨i, j⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [copyGate, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, fin2_one_add_one]

/-- The retained-outcome measurement in Appendix A.1: reset the outcome bit,
copy the measured basis value by CNOT, and dephase the outcome bit. -/
def measurement : KrausChannel (Fin 2 × Fin 2) :=
  (dephase.extendLeft (Fin 2)).comp
    ((unitary copyGate copyGate_unitary).comp (reset.extendLeft (Fin 2)))

end KrausChannel
end Paper25
