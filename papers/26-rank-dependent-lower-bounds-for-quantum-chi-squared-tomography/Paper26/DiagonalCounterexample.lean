import Paper26.Classical
import Paper26.PositiveLossBridge
import Paper26.ShellAccounting

/-!
# Appendix C, equation (55), for actual quantum density matrices

The two strictly positive probability vectors are embedded as concrete
diagonal complex density matrices.  Their actual quantum Bures and
right-inverse losses have the same exact classical value, independently of
the output eigenbasis selected by the spectral theorem.  A quantitative
small-q criterion and arbitrarily small witnesses prove unbounded loss at
a fixed Frobenius error.  No external theorem is added.
-/
noncomputable section
open scoped BigOperators ENNReal ComplexOrder Matrix

namespace Paper26.DiagonalCounterexample

open QuantumModel

/-- The true state diag(q+b, 1-q-b), with its actual PSD/trace-one proofs. -/
def input (b q : ℝ) (hb : 0 < b) (hq : 0 < q) (hqb : q < 1 - b) :
    Density (Fin 2) :=
  Density.diagonal (Classical.counterexampleInput b q)
    (Classical.counterexampleInput_distribution hb hq hqb).1
    (Classical.counterexampleInput_distribution hb hq hqb).2

/-- The output state diag(q, 1-q), not merely a probability-vector surrogate. -/
def estimate (b q : ℝ) (hb : 0 < b) (hq : 0 < q) (hqb : q < 1 - b) :
    Density (Fin 2) :=
  Density.diagonal (Classical.counterexampleEstimate q)
    (Classical.counterexampleEstimate_distribution hq (by linarith)).1
    (Classical.counterexampleEstimate_distribution hq (by linarith)).2

theorem input_posDef (b q : ℝ) (hb : 0 < b) (hq : 0 < q) (hqb : q < 1 - b) :
    (input b q hb hq hqb).matrix.PosDef := by
  apply Density.diagonal_posDef
  intro i
  fin_cases i <;> simp [Classical.counterexampleInput] <;> linarith

theorem estimate_posDef (b q : ℝ) (hb : 0 < b) (hq : 0 < q) (hqb : q < 1 - b) :
    (estimate b q hb hq hqb).matrix.PosDef := by
  apply Density.diagonal_posDef
  intro i
  fin_cases i <;> simp [Classical.counterexampleEstimate] <;> linarith

/-- The exact matrix Frobenius formula, including the off-diagonal zero terms. -/
theorem frobenius_exact (b q : ℝ) (hb : 0 < b) (hq : 0 < q) (hqb : q < 1 - b) :
    SpectralLoss.frobeniusSq
      ((input b q hb hq hqb).matrix - (estimate b q hb hq hqb).matrix) = 2 * b ^ 2 := by
  unfold input estimate
  rw [Density.frobeniusSq_diagonal_difference]
  exact Classical.counterexample_frobenius b q

/-- Actual quantum Bures loss, with the intrinsic spectral-basis definition. -/
theorem chiB_exact (b q : ℝ) (hb : 0 < b) (hq : 0 < q) (hqb : q < 1 - b) :
    chiB (input b q hb hq hqb) (estimate b q hb hq hqb) =
      ENNReal.ofReal (b ^ 2 * (1 / q + 1 / (1 - q))) := by
  have hpos : ∀ i, 0 < Classical.counterexampleEstimate q i := by
    intro i
    fin_cases i <;> simp [Classical.counterexampleEstimate] <;> linarith
  unfold input estimate
  rw [PositiveLossBridge.chiB_diagonal _ _ _ _ _ _ hpos]
  exact congrArg ENNReal.ofReal (Classical.counterexample_chiSquared b q)

/-- Actual quantum right-inverse loss has exactly the same value. -/
theorem chiR_exact (b q : ℝ) (hb : 0 < b) (hq : 0 < q) (hqb : q < 1 - b) :
    chiR (input b q hb hq hqb) (estimate b q hb hq hqb) =
      ENNReal.ofReal (b ^ 2 * (1 / q + 1 / (1 - q))) := by
  have hpos : ∀ i, 0 < Classical.counterexampleEstimate q i := by
    intro i
    fin_cases i <;> simp [Classical.counterexampleEstimate] <;> linarith
  unfold input estimate
  rw [PositiveLossBridge.chiR_diagonal _ _ _ _ _ _ hpos]
  exact congrArg ENNReal.ofReal (Classical.counterexample_chiSquared b q)

/-- Both equality signs of equation (55), for the same actual pair of states. -/
theorem equation55 (b q : ℝ) (hb : 0 < b) (hq : 0 < q) (hqb : q < 1 - b) :
    SpectralLoss.frobeniusSq
        ((input b q hb hq hqb).matrix - (estimate b q hb hq hqb).matrix) = 2 * b ^ 2 ∧
      chiB (input b q hb hq hqb) (estimate b q hb hq hqb) =
        ENNReal.ofReal (b ^ 2 * (1 / q + 1 / (1 - q))) ∧
      chiR (input b q hb hq hqb) (estimate b q hb hq hqb) =
        ENNReal.ofReal (b ^ 2 * (1 / q + 1 / (1 - q))) :=
  ⟨frobenius_exact b q hb hq hqb, chiB_exact b q hb hq hqb, chiR_exact b q hb hq hqb⟩

/-- A quantitative version of divergence as q decreases to zero: every
admissible q below this explicit positive scale gives loss larger than M. -/
theorem loss_gt_of_small_q (b q : ℝ) (hb : 0 < b) (hq : 0 < q)
    (hqb : q < 1 - b) (M : ℝ) (hsmall : q ≤ b ^ 2 / (|M| + 1)) :
    ENNReal.ofReal M < chiB (input b q hb hq hqb) (estimate b q hb hq hqb) ∧
      ENNReal.ofReal M < chiR (input b q hb hq hqb) (estimate b q hb hq hqb) := by
  have hfirst : |M| + 1 ≤ b ^ 2 / q := by
    apply (le_div_iff₀ hq).mpr
    have hc := (le_div_iff₀ (by positivity : 0 < |M| + 1)).mp hsmall
    nlinarith
  have htail : 0 ≤ b ^ 2 / (1 - q) := div_nonneg (sq_nonneg _) (by linarith)
  have he : b ^ 2 * (1 / q + 1 / (1 - q)) = b ^ 2 / q + b ^ 2 / (1 - q) := by ring
  have hlarge : M < b ^ 2 * (1 / q + 1 / (1 - q)) := by
    rw [he]
    linarith [le_abs_self M]
  have hpos : 0 < b ^ 2 * (1 / q + 1 / (1 - q)) := by
    rw [he]
    linarith [abs_nonneg M]
  rw [chiB_exact, chiR_exact]
  exact ⟨(ENNReal.ofReal_lt_ofReal_iff hpos).mpr hlarge,
    (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hlarge⟩

/-- The bad output parameter may be arbitrarily small, for every fixed
0<b<1 and every proposed finite loss bound.  Both states stay positive definite. -/
theorem arbitrarily_small_bad_estimates (b : ℝ) (hb : 0 < b) (hb1 : b < 1)
    (M η : ℝ) (hη : 0 < η) :
    ∃ (q : ℝ) (hq : 0 < q) (hqb : q < 1 - b), q < η ∧
      (input b q hb hq hqb).matrix.PosDef ∧ (estimate b q hb hq hqb).matrix.PosDef ∧
      SpectralLoss.frobeniusSq
        ((input b q hb hq hqb).matrix - (estimate b q hb hq hqb).matrix) = 2 * b ^ 2 ∧
      ENNReal.ofReal M < chiB (input b q hb hq hqb) (estimate b q hb hq hqb) ∧
      ENNReal.ofReal M < chiR (input b q hb hq hqb) (estimate b q hb hq hqb) := by
  let q := min ((1 - b) / 2) (min (b ^ 2 / (|M| + 1)) (η / 2))
  have hq : 0 < q := by
    have hfirst : 0 < (1 - b) / 2 := by linarith
    exact lt_min hfirst (lt_min (by positivity) (by positivity))
  have hqb : q < 1 - b := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hqη : q < η := by
    have hle : q ≤ η / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hsmall : q ≤ b ^ 2 / (|M| + 1) := (min_le_right _ _).trans (min_le_left _ _)
  exact ⟨q, hq, hqb, hqη, input_posDef b q hb hq hqb, estimate_posDef b q hb hq hqb,
    frobenius_exact b q hb hq hqb, loss_gt_of_small_q b q hb hq hqb M hsmall⟩

/-- Actual positive-definite quantum states with the same Frobenius error
1/8 can have both quantum chi-squared losses above every proposed bound. -/
theorem no_uniform_frobenius_control (M : ℝ) :
    ∃ ρ σ : Density (Fin 2), ρ.matrix.PosDef ∧ σ.matrix.PosDef ∧
      SpectralLoss.frobeniusSq (ρ.matrix - σ.matrix) = 1 / 8 ∧
      ENNReal.ofReal M < chiB ρ σ ∧ ENNReal.ofReal M < chiR ρ σ := by
  obtain ⟨q, hq, hqb, _, hpρ, hpσ, hf, hB, hR⟩ :=
    arbitrarily_small_bad_estimates (1 / 4) (by norm_num) (by norm_num) M 1 (by norm_num)
  refine ⟨input (1 / 4) q (by norm_num) hq hqb,
    estimate (1 / 4) q (by norm_num) hq hqb, hpρ, hpσ, ?_, hB, hR⟩
  simpa only [show 2 * (1 / 4 : ℝ) ^ 2 = 1 / 8 by norm_num] using hf

/-- The actual Frobenius error is unchanged by any unitary change of basis. -/
theorem frobeniusSq_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    SpectralLoss.frobeniusSq (Normalization.conjugate (U : Matrix ι ι ℂ) A) =
      SpectralLoss.frobeniusSq A := by
  have h : ShellAccounting.frobeniusSq
      (((U : Matrix ι ι ℂ) * A) * (U : Matrix ι ι ℂ)ᴴ) =
      ShellAccounting.frobeniusSq A := by
    rw [ShellAccounting.frobeniusSq_mul_unitary _ _ (by
      simpa only [Matrix.conjTranspose_conjTranspose] using PositiveLossBridge.unitary_left U),
      ShellAccounting.frobeniusSq_unitary_mul _ _ (PositiveLossBridge.unitary_left U)]
  simpa only [Normalization.conjugate, SpectralLoss.frobeniusSq,
    ShellAccounting.frobeniusSq, Complex.normSq_eq_norm_sq] using h

/-- Equation (55) also holds for the actual states in any common unitary basis. -/
theorem equation55_unitary (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (b q : ℝ) (hb : 0 < b) (hq : 0 < q) (hqb : q < 1 - b) :
    let ρ := PositiveLossBridge.conjugateDensity U (input b q hb hq hqb)
    let σ := PositiveLossBridge.conjugateDensity U (estimate b q hb hq hqb)
    SpectralLoss.frobeniusSq (ρ.matrix - σ.matrix) = 2 * b ^ 2 ∧
      chiB ρ σ = ENNReal.ofReal (b ^ 2 * (1 / q + 1 / (1 - q))) ∧
      chiR ρ σ = ENNReal.ofReal (b ^ 2 * (1 / q + 1 / (1 - q))) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [PositiveLossBridge.conjugateDensity_matrix, PositiveLossBridge.conjugateDensity_matrix,
      ← Normalization.conjugate_sub, frobeniusSq_conjugate]
    exact frobenius_exact b q hb hq hqb
  · rw [PositiveLossBridge.chiB_unitary _ _ _ (estimate_posDef b q hb hq hqb)]
    exact chiB_exact b q hb hq hqb
  · rw [PositiveLossBridge.chiR_unitary _ _ _ (estimate_posDef b q hb hq hqb)]
    exact chiR_exact b q hb hq hqb

end Paper26.DiagonalCounterexample
