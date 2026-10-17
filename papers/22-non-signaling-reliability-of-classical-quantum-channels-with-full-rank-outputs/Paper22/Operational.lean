import Paper22.Programs

/-!
# Operational meaning of the equality program (Appendix A)

The operators below have exactly the indices `F_{x,mhat|m}` of Appendix A.
Both non-signaling conditions and the normalization are imposed as matrix
identities.  Equation (28) constructs an operation from a feasible pair.
Conversely, averaging the diagonal operators of an arbitrary operation gives
subnormalized effects; dividing only at positive input weights recovers a
feasible pair with the same actual channel success probability.
-/

open scoped MatrixOrder ComplexOrder
open Matrix

noncomputable section
namespace Paper22

variable {n d M : ℕ}

/-- A bipartite classical/quantum non-signaling operation.  `F x h m` is
`F_{x,h|m}`; the quantum input is Bob's channel output. -/
structure NSOperation (n d M : ℕ) where
  F : Fin n → Fin M → Fin M → Matrix (Fin d) (Fin d) ℂ
  positive : ∀ x h m, 0 ≤ F x h m
  normalized : ∀ m, ∑ x, ∑ h, F x h m = 1
  inputDistribution : Fin M → ProbDist n
  bob_to_alice : ∀ m x, ∑ h, F x h m = (inputDistribution m).q x • 1
  alice_to_bob : ∀ h m m', ∑ x, F x h m = ∑ x, F x h m'

/-- Average success after wiring the classical output into the cq channel. -/
def NSOperation.success (F : NSOperation n d M) (V : CQChannel n d) : ℝ :=
  (1 / M : ℝ) * ∑ m, ∑ x, (V.states x * F.F x m m).trace.re

/-- Equation (28), including its off-diagonal decoding operators. -/
def equalityOperationOperators (q : Fin n → ℝ)
    (Q : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin n) (h m : Fin M) : Matrix (Fin d) (Fin d) ℂ :=
  if h = m then q x • Q x else (q x / ((M : ℝ) - 1)) • (1 - Q x)

@[simp] theorem equalityOperationOperators_diagonal (q : Fin n → ℝ)
    (Q : Fin n → Matrix (Fin d) (Fin d) ℂ) (x : Fin n) (m : Fin M) :
    equalityOperationOperators q Q x m m = q x • Q x := by
  simp [equalityOperationOperators]

/-- A finite message row has one diagonal and `M-1` off-diagonal entries. -/
theorem sum_message_diagonal_offDiagonal (A B : Matrix (Fin d) (Fin d) ℂ)
    (m : Fin M) :
    (∑ h : Fin M, if h = m then A else B) = A + ((M : ℝ) - 1) • B := by
  classical
  have hM : 1 ≤ M := by
    have hm := m.isLt
    omega
  have hc : ((Finset.univ.erase m).card : ℝ) = (M : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_fin,
      Nat.cast_sub hM,
      Nat.cast_one]
  calc
    _ = (∑ h ∈ Finset.univ.erase m, if h = m then A else B) + A := by
      simpa using (Finset.sum_erase_add (s := Finset.univ)
        (fun h : Fin M => if h = m then A else B) (Finset.mem_univ m)).symm
    _ = (∑ _h ∈ Finset.univ.erase m, B) + A := by
      congr 1
      apply Finset.sum_congr rfl
      intro h hh
      simp only [Finset.mem_erase] at hh
      simp [hh.1]
    _ = A + ((M : ℝ) - 1) • B := by
      rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, hc, add_comm]

/-- Every operator in (28) is positive semidefinite. -/
theorem equalityOperationOperators_nonneg {q : Fin n → ℝ}
    {Q : Fin n → Matrix (Fin d) (Fin d) ℂ}
    (hM : 2 ≤ M) (hq : ∀ x, 0 ≤ q x) (hQ : ∀ x, IsEffect (Q x))
    (x : Fin n) (h m : Fin M) : 0 ≤ equalityOperationOperators q Q x h m := by
  unfold equalityOperationOperators
  split_ifs
  · exact smul_nonneg (hq x) (hQ x).nonneg
  · have hden : 0 ≤ (M : ℝ) - 1 := by
      have : (2 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    exact smul_nonneg (div_nonneg (hq x) hden) (hQ x).one_sub_nonneg

/-- The Bob-to-Alice marginal of (28) is the unchanged distribution `q`. -/
theorem equalityOperationOperators_bob_to_alice {q : Fin n → ℝ}
    {Q : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : 2 ≤ M)
    (x : Fin n) (m : Fin M) :
    ∑ h, equalityOperationOperators q Q x h m = q x • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have hden : (M : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  simp only [equalityOperationOperators]
  rw [sum_message_diagonal_offDiagonal, smul_smul]
  have hs : ((M : ℝ) - 1) * (q x / ((M : ℝ) - 1)) = q x := by
    field_simp
  rw [hs]
  rw [← smul_add, add_sub_cancel]

/-- The Alice-to-Bob marginal of (28) is uniform on message estimates. -/
theorem equalityOperationOperators_alice_to_bob {q : Fin n → ℝ}
    {Q : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : 2 ≤ M)
    (hqQ : NSFeasible M q Q) (h m : Fin M) :
    ∑ x, equalityOperationOperators q Q x h m =
      (1 / M : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hden : (M : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  by_cases hhm : h = m
  · simpa [equalityOperationOperators, hhm] using hqQ.2.2.2
  · simp only [equalityOperationOperators, hhm, ↓reduceIte]
    simp_rw [div_eq_mul_inv, MulAction.mul_smul, smul_comm (q _)]
    simp only [one_smul]
    rw [← Finset.smul_sum]
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hqQ.2.1, one_smul, hqQ.2.2.2]
    have he : (1 : Matrix (Fin d) (Fin d) ℂ) - (1 / M : ℝ) • 1 =
        (1 - 1 / M : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      rw [sub_smul, one_smul]
    rw [he, smul_smul]
    congr 1
    field_simp [hden, hM0]
    <;> ring

/-- The normalized operation defined by equation (28). -/
def equalityOperation {q : Fin n → ℝ}
    {Q : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : 2 ≤ M)
    (hqQ : NSFeasible M q Q) : NSOperation n d M where
  F := equalityOperationOperators q Q
  positive := equalityOperationOperators_nonneg hM hqQ.1 hqQ.2.2.1
  normalized m := by
    simp_rw [equalityOperationOperators_bob_to_alice hM]
    rw [← Finset.sum_smul, hqQ.2.1, one_smul]
  inputDistribution := fun _ => ⟨q, hqQ.1, hqQ.2.1⟩
  bob_to_alice m x := equalityOperationOperators_bob_to_alice hM x m
  alice_to_bob h m m' := by
    rw [equalityOperationOperators_alice_to_bob hM hqQ,
      equalityOperationOperators_alice_to_bob hM hqQ]

/-- The success identity in Appendix A, evaluated on the actual cq matrices. -/
theorem equalityOperation_success (V : CQChannel n d) {q : Fin n → ℝ}
    {Q : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : 2 ≤ M)
    (hqQ : NSFeasible M q Q) :
    (equalityOperation hM hqQ).success V = ∑ x, q x * (V.states x * Q x).trace.re := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  simp [NSOperation.success, equalityOperation, Matrix.trace_smul,
    Finset.sum_const, nsmul_eq_mul, hM0]

/-- Error and success sum to one for a probability-weighted effect family. -/
theorem programObjective_eq_one_sub_success (V : CQChannel n d)
    {q : Fin n → ℝ} (Q : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hq1 : ∑ x, q x = 1) :
    programObjective V.states q Q = 1 - ∑ x, q x * (V.states x * Q x).trace.re := by
  simp_rw [programObjective, mul_sub, Matrix.mul_one, Matrix.trace_sub,
    Complex.sub_re, (V.isDensity _).trace_one, Complex.one_re, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, hq1]

/-- Convert subnormalized effects to the source's `Q_x=G_x/q_x`, using zero
at zero input weight. -/
def normalizedEffects (q : Fin n → ℝ)
    (G : Fin n → Matrix (Fin d) (Fin d) ℂ) (x : Fin n) : Matrix (Fin d) (Fin d) ℂ :=
  if 0 < q x then (q x)⁻¹ • G x else 0

/-- Division at positive weights, and the zero case, both preserve effects. -/
theorem normalizedEffects_isEffect {q : Fin n → ℝ}
    {G : Fin n → Matrix (Fin d) (Fin d) ℂ}
    (hq : ∀ x, 0 ≤ q x) (hG0 : ∀ x, 0 ≤ G x)
    (hGq : ∀ x, G x ≤ q x • (1 : Matrix (Fin d) (Fin d) ℂ)) (x : Fin n) :
    IsEffect (normalizedEffects q G x) := by
  unfold normalizedEffects
  split_ifs with hx
  · refine ⟨smul_nonneg (inv_nonneg.mpr (hq x)) (hG0 x), ?_⟩
    simpa [smul_smul, hx.ne'] using matrix_smul_mono (inv_nonneg.mpr (hq x)) (hGq x)
  · exact IsEffect.zero

/-- The zero-weight branch loses no operator, since then `G_x=0`. -/
theorem smul_normalizedEffects {q : Fin n → ℝ}
    {G : Fin n → Matrix (Fin d) (Fin d) ℂ}
    (hq : ∀ x, 0 ≤ q x) (hG0 : ∀ x, 0 ≤ G x)
    (hGq : ∀ x, G x ≤ q x • (1 : Matrix (Fin d) (Fin d) ℂ)) (x : Fin n) :
    q x • normalizedEffects q G x = G x := by
  unfold normalizedEffects
  split_ifs with hx
  · simp [smul_smul, hx.ne']
  · have hx0 : q x = 0 := le_antisymm (le_of_not_gt hx) (hq x)
    have hG : G x = 0 := le_antisymm (by simpa [hx0] using hGq x) (hG0 x)
    simp [hG]

/-- Exact equivalence between the SDP variables `0≤G_x≤q_x I` and the
probability/effect variables, including zero input weights. -/
theorem subnormalizedEffects_to_NSFeasible {q : Fin n → ℝ}
    {G : Fin n → Matrix (Fin d) (Fin d) ℂ}
    (hq : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1) (hG0 : ∀ x, 0 ≤ G x)
    (hGq : ∀ x, G x ≤ q x • (1 : Matrix (Fin d) (Fin d) ℂ))
    (hG1 : ∑ x, G x = (1 / M : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ)) :
    NSFeasible M q (normalizedEffects q G) := by
  refine ⟨hq, hq1, normalizedEffects_isEffect hq hG0 hGq, ?_⟩
  simpa only [smul_normalizedEffects hq hG0 hGq] using hG1

/-- Input weights obtained by averaging over the uniformly distributed message. -/
def NSOperation.averageInput (F : NSOperation n d M) (x : Fin n) : ℝ :=
  (1 / M : ℝ) * ∑ m, (F.inputDistribution m).q x

/-- The averaged successful decoding operators. -/
def NSOperation.diagonalAverage (F : NSOperation n d M)
    (x : Fin n) : Matrix (Fin d) (Fin d) ℂ :=
  (1 / M : ℝ) • ∑ m, F.F x m m

theorem NSOperation.averageInput_nonneg (F : NSOperation n d M) (x : Fin n) :
    0 ≤ F.averageInput x := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun m _ => (F.inputDistribution m).nonneg x

theorem NSOperation.averageInput_sum (F : NSOperation n d M) (hM : 0 < M) :
    ∑ x, F.averageInput x = 1 := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [NSOperation.averageInput]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp [ProbDist.sum_eq_one, hM0]

theorem NSOperation.diagonalAverage_nonneg (F : NSOperation n d M) (x : Fin n) :
    0 ≤ F.diagonalAverage x := by
  apply smul_nonneg (by positivity)
  exact Finset.sum_nonneg fun m _ => F.positive x m m

/-- Each successful decoding operator is bounded by the full Alice marginal. -/
theorem NSOperation.diagonalAverage_le_input (F : NSOperation n d M) (x : Fin n) :
    F.diagonalAverage x ≤ F.averageInput x • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  unfold NSOperation.diagonalAverage NSOperation.averageInput
  rw [MulAction.mul_smul, Finset.sum_smul]
  apply matrix_smul_mono (by positivity)
  apply Finset.sum_le_sum
  intro m _
  calc
    F.F x m m ≤ ∑ h, F.F x h m :=
      Finset.single_le_sum (fun h _ => F.positive x h m) (Finset.mem_univ m)
    _ = (F.inputDistribution m).q x • 1 := F.bob_to_alice m x

/-- The other non-signaling condition fixes the sum of averaged diagonals. -/
theorem NSOperation.diagonalAverage_sum (F : NSOperation n d M) (hM : 0 < M) :
    ∑ x, F.diagonalAverage x =
      (1 / M : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  let m₀ : Fin M := ⟨0, hM⟩
  unfold NSOperation.diagonalAverage
  rw [← Finset.smul_sum, Finset.sum_comm]
  congr 1
  calc
    (∑ m, ∑ x, F.F x m m) = ∑ m, ∑ x, F.F x m m₀ := by
      apply Finset.sum_congr rfl
      intro m _
      exact F.alice_to_bob m m m₀
    _ = ∑ x, ∑ m, F.F x m m₀ := Finset.sum_comm
    _ = 1 := F.normalized m₀

/-- Recover the equality program from any actual non-signaling operation. -/
theorem NSOperation.toNSFeasible (F : NSOperation n d M) (hM : 0 < M) :
    NSFeasible M F.averageInput (normalizedEffects F.averageInput F.diagonalAverage) :=
  subnormalizedEffects_to_NSFeasible F.averageInput_nonneg (F.averageInput_sum hM)
    F.diagonalAverage_nonneg F.diagonalAverage_le_input (F.diagonalAverage_sum hM)

/-- Averaging preserves the actual success probability for every cq channel. -/
theorem NSOperation.success_eq_diagonalAverage (F : NSOperation n d M)
    (V : CQChannel n d) :
    F.success V = ∑ x, (V.states x * F.diagonalAverage x).trace.re := by
  simp_rw [NSOperation.diagonalAverage, Matrix.mul_smul, Matrix.mul_sum,
    Matrix.trace_smul, Matrix.trace_sum, Complex.smul_re, Complex.re_sum, smul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  rfl

/-- The recovered equality-program pair has exactly the operational error. -/
theorem NSOperation.programObjective_recovered (F : NSOperation n d M)
    (V : CQChannel n d) (hM : 0 < M) :
    programObjective V.states F.averageInput
      (normalizedEffects F.averageInput F.diagonalAverage) = 1 - F.success V := by
  rw [programObjective_eq_one_sub_success V _ (F.averageInput_sum hM),
    F.success_eq_diagonalAverage V]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [← smul_normalizedEffects F.averageInput_nonneg F.diagonalAverage_nonneg
    F.diagonalAverage_le_input x, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]
  rfl

/-- Every equality-program error is achieved by an actual non-signaling operation. -/
theorem equalityOperation_error (V : CQChannel n d) {q : Fin n → ℝ}
    {Q : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : 2 ≤ M)
    (hqQ : NSFeasible M q Q) :
    1 - (equalityOperation hM hqQ).success V = programObjective V.states q Q := by
  rw [equalityOperation_success V hM hqQ,
    programObjective_eq_one_sub_success V Q hqQ.2.1]

/-- Equality of achievable errors, with all quantifiers over actual matrices. -/
theorem operational_error_iff_program (V : CQChannel n d) (hM : 2 ≤ M) (e : ℝ) :
    (∃ F : NSOperation n d M, e = 1 - F.success V) ↔
      ∃ q Q, NSFeasible M q Q ∧ e = programObjective V.states q Q := by
  constructor
  · rintro ⟨F, rfl⟩
    refine ⟨F.averageInput, normalizedEffects F.averageInput F.diagonalAverage,
      F.toNSFeasible (by omega), ?_⟩
    exact (F.programObjective_recovered V (by omega)).symm
  · rintro ⟨q, Q, hqQ, rfl⟩
    exact ⟨equalityOperation hM hqQ, (equalityOperation_error V hM hqQ).symm⟩

/-- The symmetric `G,H` data in Appendix A also directly recover the program. -/
theorem symmetricOperators_to_NSFeasible {q : Fin n → ℝ}
    {G H : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : 2 ≤ M)
    (hq : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (hG : ∀ x, 0 ≤ G x) (hH : ∀ x, 0 ≤ H x)
    (hrow : ∀ x, G x + ((M : ℝ) - 1) • H x = q x • 1)
    (hcol : ∑ x, G x = (1 / M : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ)) :
    NSFeasible M q (normalizedEffects q G) := by
  apply subnormalizedEffects_to_NSFeasible hq hq1 hG _ hcol
  intro x
  have hden : 0 ≤ (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  calc
    G x ≤ G x + ((M : ℝ) - 1) • H x := le_add_of_nonneg_right (smul_nonneg hden (hH x))
    _ = q x • 1 := hrow x

/-- A symmetric operation constructed by averaging successful diagonals and
completing the unsuccessful entries. -/
def NSOperation.symmetrized (F : NSOperation n d M) (hM : 2 ≤ M) : NSOperation n d M :=
  equalityOperation hM (F.toNSFeasible (by omega))

/-- Symmetrization keeps the averaged successful operator at each input. -/
theorem NSOperation.symmetrized_diagonal (F : NSOperation n d M) (hM : 2 ≤ M)
    (x : Fin n) (m : Fin M) :
    (F.symmetrized hM).F x m m = F.diagonalAverage x := by
  change equalityOperationOperators _ _ x m m = _
  rw [equalityOperationOperators_diagonal]
  exact smul_normalizedEffects F.averageInput_nonneg F.diagonalAverage_nonneg
    F.diagonalAverage_le_input x

/-- Simultaneous relabeling of messages and estimates leaves this operation
unchanged, as required of the symmetric form in Appendix A. -/
theorem NSOperation.symmetrized_permutation_invariant (F : NSOperation n d M)
    (hM : 2 ≤ M) (π : Equiv.Perm (Fin M)) (x : Fin n) (h m : Fin M) :
    (F.symmetrized hM).F x (π h) (π m) = (F.symmetrized hM).F x h m := by
  change equalityOperationOperators _ _ x (π h) (π m) =
    equalityOperationOperators _ _ x h m
  simp only [equalityOperationOperators, Equiv.apply_eq_iff_eq]

/-- Symmetrization preserves success on every cq channel. -/
theorem NSOperation.symmetrized_success (F : NSOperation n d M) (hM : 2 ≤ M)
    (V : CQChannel n d) : (F.symmetrized hM).success V = F.success V := by
  rw [NSOperation.success_eq_diagonalAverage F V]
  unfold NSOperation.success
  simp_rw [F.symmetrized_diagonal hM]
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  simp [Finset.sum_const, nsmul_eq_mul, hM0]

/-- The operational optimum before any SDP change of variables. -/
def epsNSOperational (V : CQChannel n d) (M : ℕ) : ℝ :=
  sInf {e | ∃ F : NSOperation n d M, e = 1 - F.success V}

/-- Appendix A identifies the operational optimum with the equality program. -/
theorem epsNSOperational_eq_epsNS (V : CQChannel n d) (hM : 2 ≤ M) :
    epsNSOperational V M = epsNS V M := by
  unfold epsNSOperational epsNS
  congr 1
  ext e
  exact operational_error_iff_program V hM e

end Paper22
end
