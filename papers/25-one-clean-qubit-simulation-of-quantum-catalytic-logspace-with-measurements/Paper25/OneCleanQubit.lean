import Paper25.TraceReadout
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.NoncommRing

/-!
# Operational semantics of the one-clean-qubit trace test (Lemma 6)

A probe is indexed by the two summands of `n ⊕ n`. This is the computational
basis `|0⟩ ⊗ |i⟩, |1⟩ ⊗ |i⟩`. The initial density is `|0⟩⟨0| ⊗ I/card n`.
The circuit is the actual product `H controlled(V) H`; measurement is the
trace of the corresponding principal block of its conjugated density.
-/

noncomputable section
open scoped ComplexOrder ComplexConjugate
open Matrix
namespace Paper25.OneCleanQubit

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev ProbeMatrix (n : Type*) := Matrix (n ⊕ n) (n ⊕ n) ℂ

/-- Both inverse identities, so gate legality is checked independently of readout. -/
def Unitary {a : Type*} [Fintype a] [DecidableEq a] (U : Matrix a a ℂ) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

lemma unitary_mul {a : Type*} [Fintype a] [DecidableEq a]
    {U V : Matrix a a ℂ} (hU : Unitary U) (hV : Unitary V) : Unitary (U * V) := by
  constructor
  · rw [Matrix.conjTranspose_mul, mul_assoc, ← mul_assoc U.conjTranspose,
      hU.1, one_mul, hV.1]
  · rw [Matrix.conjTranspose_mul, mul_assoc, ← mul_assoc V,
      hV.2, one_mul, hU.2]

lemma block_identity : Matrix.fromBlocks (1 : Matrix n n ℂ) 0 0 1 = (1 : ProbeMatrix n) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

lemma trace_blocks (A B C D : Matrix n n ℂ) :
    Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  simp [Matrix.trace, Fintype.sum_sum_type, Matrix.fromBlocks]

/-- Matrix of the probe Hadamard, tensored with the identity of the target. -/
def hadamard : ProbeMatrix n :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • Matrix.fromBlocks 1 1 1 (-1)

private lemma hadamard_scalar_sq :
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (1 / 2 : ℂ) := by
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [← Complex.ofReal_mul, h]
  norm_num

lemma hadamard_adjoint : (hadamard : ProbeMatrix n).conjTranspose = hadamard := by
  simp [hadamard, Matrix.conjTranspose_smul, Matrix.fromBlocks_conjTranspose]

lemma hadamard_square : (hadamard : ProbeMatrix n) * hadamard = 1 := by
  rw [hadamard, smul_mul_smul, hadamard_scalar_sq, Matrix.fromBlocks_multiply]
  have h : (Matrix.fromBlocks (1 * 1 + 1 * 1) (1 * 1 + 1 * (-1))
      (1 * 1 + (-1) * 1) (1 * 1 + (-1) * (-1)) : ProbeMatrix n)
      = (2 : ℂ) • Matrix.fromBlocks (1 : Matrix n n ℂ) 0 0 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.smul_apply, two_smul]
    all_goals split_ifs <;> norm_num
  rw [h, smul_smul, block_identity]
  norm_num

lemma hadamard_unitary : Unitary (hadamard : ProbeMatrix n) := by
  rw [Unitary, hadamard_adjoint]
  exact ⟨hadamard_square, hadamard_square⟩

/-- Control on the probe's `|1⟩` state. -/
def controlled (V : Matrix n n ℂ) : ProbeMatrix n := Matrix.fromBlocks 1 0 0 V

lemma controlled_unitary (V : Matrix n n ℂ) (hV : Unitary V) : Unitary (controlled V) := by
  constructor <;>
    simp only [controlled, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_one,
      Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply, mul_one, one_mul,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  · rw [hV.1, block_identity]
  · rw [hV.2, block_identity]

/-- Explicit chronological circuit: first Hadamard, controlled V, last Hadamard. -/
def circuit (V : Matrix n n ℂ) : ProbeMatrix n := hadamard * controlled V * hadamard

lemma circuit_unitary (V : Matrix n n ℂ) (hV : Unitary V) : Unitary (circuit V) :=
  unitary_mul (unitary_mul hadamard_unitary (controlled_unitary V hV)) hadamard_unitary

/-- One pure probe and a completely mixed target. -/
def input : ProbeMatrix n :=
  ((Fintype.card n : ℂ)⁻¹) • Matrix.fromBlocks 1 0 0 0

lemma input_is_diagonal : (input : ProbeMatrix n) =
    Matrix.diagonal (fun i => match i with
      | Sum.inl _ => (Fintype.card n : ℂ)⁻¹
      | Sum.inr _ => 0) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [input, Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal]

lemma input_posSemidef : (input : ProbeMatrix n).PosSemidef := by
  rw [input_is_diagonal]
  apply Matrix.PosSemidef.diagonal
  intro i
  rcases i with i | i <;> simp

lemma input_trace [Nonempty n] : Matrix.trace (input : ProbeMatrix n) = 1 := by
  rw [input, Matrix.trace_smul, trace_blocks]
  simp only [Matrix.trace_one, Matrix.trace_zero, add_zero]
  exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := n))

/-- Unitary dynamics on density matrices. -/
def evolve {a : Type*} [Fintype a] (U ρ : Matrix a a ℂ) := U * ρ * U.conjTranspose

lemma evolve_posSemidef {a : Type*} [Fintype a] (U ρ : Matrix a a ℂ)
    (hρ : ρ.PosSemidef) : (evolve U ρ).PosSemidef :=
  hρ.mul_mul_conjTranspose_same U

lemma evolve_trace {a : Type*} [Fintype a] [DecidableEq a]
    (U ρ : Matrix a a ℂ) (hU : Unitary U) : Matrix.trace (evolve U ρ) = Matrix.trace ρ := by
  unfold evolve
  rw [Matrix.trace_mul_cycle, hU.1, one_mul]

lemma evolve_comp {a : Type*} [Fintype a] (U V ρ : Matrix a a ℂ) :
    evolve (U * V) ρ = evolve U (evolve V ρ) := by
  simp only [evolve, Matrix.conjTranspose_mul]
  simp only [mul_assoc]

/-- The density after the first Hadamard. -/
lemma after_first_hadamard :
    evolve (hadamard : ProbeMatrix n) input =
      (1 / (2 * Fintype.card n) : ℂ) • Matrix.fromBlocks 1 1 1 1 := by
  rw [evolve, hadamard_adjoint]
  simp only [hadamard, input, smul_mul_smul, Matrix.fromBlocks_multiply,
    one_mul, mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    neg_mul, mul_neg]
  have hs : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (Fintype.card n : ℂ)⁻¹ *
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / (2 * Fintype.card n) := by
    calc
      _ = ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) *
        (Fintype.card n : ℂ)⁻¹ := by ring
      _ = _ := by rw [hadamard_scalar_sq]; simp [div_eq_mul_inv, mul_comm]
  rw [hs]
  simp only [Matrix.fromBlocks_multiply, one_mul, mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, neg_zero]

/-- The joint density before the final Hadamard; no partial-state formula is assumed. -/
lemma after_controlled (V : Matrix n n ℂ) (hV : Unitary V) :
    evolve (controlled V) (evolve (hadamard : ProbeMatrix n) input) =
      (1 / (2 * Fintype.card n) : ℂ) • Matrix.fromBlocks 1 V.conjTranspose V 1 := by
  rw [after_first_hadamard]
  simp only [evolve, controlled, Matrix.mul_smul, smul_mul_assoc,
    Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, one_mul, mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, hV.2]

/-- Output of the complete one-clean-qubit circuit. -/
def output (V : Matrix n n ℂ) : ProbeMatrix n := evolve (circuit V) input

lemma output_explicit (V : Matrix n n ℂ) (hV : Unitary V) :
    output V = (1 / (4 * Fintype.card n) : ℂ) •
      Matrix.fromBlocks ((2 : ℂ) • (1 : Matrix n n ℂ) + V + V.conjTranspose)
        (V - V.conjTranspose) (V.conjTranspose - V)
        ((2 : ℂ) • (1 : Matrix n n ℂ) - V - V.conjTranspose) := by
  simp only [output, circuit, evolve_comp]
  rw [after_controlled V hV]
  rw [evolve, hadamard_adjoint]
  simp only [hadamard, smul_mul_smul]
  have hs : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (1 / (2 * Fintype.card n) : ℂ) *
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / (4 * Fintype.card n) := by
    calc
      _ = ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) *
        (1 / (2 * Fintype.card n) : ℂ) := by ring
      _ = _ := by rw [hadamard_scalar_sq]; ring
  rw [hs]
  congr 1
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1 <;> simp only [one_mul, mul_one, neg_mul, mul_neg, two_smul] <;> abel

/-- Born measurement of the probe in the computational basis. -/
def probZero (ρ : ProbeMatrix n) : ℝ := (Matrix.trace ρ.toBlocks₁₁).re

def probOne (ρ : ProbeMatrix n) : ℝ := (Matrix.trace ρ.toBlocks₂₂).re

def expectationZ (ρ : ProbeMatrix n) : ℝ := probZero ρ - probOne ρ

lemma measurement_sum (ρ : ProbeMatrix n) : probZero ρ + probOne ρ = (Matrix.trace ρ).re := by
  have hρ : ρ = Matrix.fromBlocks ρ.toBlocks₁₁ ρ.toBlocks₁₂ ρ.toBlocks₂₁ ρ.toBlocks₂₂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  conv_rhs => rw [hρ, trace_blocks]
  rfl

lemma probZero_nonneg (ρ : ProbeMatrix n) (hρ : ρ.PosSemidef) : 0 ≤ probZero ρ := by
  exact (RCLike.nonneg_iff.mp ((hρ.submatrix Sum.inl).trace_nonneg)).1

lemma probOne_nonneg (ρ : ProbeMatrix n) (hρ : ρ.PosSemidef) : 0 ≤ probOne ρ := by
  exact (RCLike.nonneg_iff.mp ((hρ.submatrix Sum.inr).trace_nonneg)).1

lemma output_posSemidef (V : Matrix n n ℂ) : (output V).PosSemidef :=
  evolve_posSemidef _ _ input_posSemidef

lemma output_trace [Nonempty n] (V : Matrix n n ℂ) (hV : Unitary V) :
    Matrix.trace (output V) = 1 := by
  rw [output, evolve_trace _ _ (circuit_unitary V hV), input_trace]

lemma output_probabilities [Nonempty n] (V : Matrix n n ℂ) (hV : Unitary V) :
    0 ≤ probZero (output V) ∧ probZero (output V) ≤ 1 ∧
      0 ≤ probOne (output V) ∧ probOne (output V) ≤ 1 := by
  have h0 := probZero_nonneg (output V) (output_posSemidef V)
  have h1 := probOne_nonneg (output V) (output_posSemidef V)
  have hsum := measurement_sum (output V)
  rw [output_trace V hV] at hsum
  simp only [Complex.one_re] at hsum
  exact ⟨h0, by linarith, h1, by linarith⟩

/-- The Born effect is the projector onto the probe's `|0⟩` space. -/
def zeroEffect : ProbeMatrix n := Matrix.fromBlocks 1 0 0 0

lemma probZero_born (ρ : ProbeMatrix n) :
    probZero ρ = (Matrix.trace (zeroEffect * ρ)).re := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks ρ]
  simp [zeroEffect, probZero, Matrix.fromBlocks_multiply, trace_blocks]

lemma probZero_output [Nonempty n] (V : Matrix n n ℂ) (hV : Unitary V) :
    probZero (output V) = 1 / 2 + (Matrix.trace V).re / (2 * Fintype.card n) := by
  have hblock : (output V).toBlocks₁₁ =
      (1 / (4 * Fintype.card n) : ℂ) •
        ((2 : ℂ) • (1 : Matrix n n ℂ) + V + V.conjTranspose) := by
    rw [output_explicit V hV]
    rfl
  unfold probZero
  rw [hblock, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_one, Matrix.trace_conjTranspose]
  have hsum : (2 : ℂ) * Fintype.card n + Matrix.trace V + star (Matrix.trace V)
      = ((2 * Fintype.card n + 2 * (Matrix.trace V).re : ℝ) : ℂ) := by
    rw [add_assoc, show star (Matrix.trace V) = conj (Matrix.trace V) from rfl,
      Complex.add_conj]
    push_cast
    rfl
  simp only [smul_eq_mul]
  rw [hsum]
  have hc : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := n)
  have hd : (1 / (4 * Fintype.card n) : ℂ) =
      ((1 / (4 * (Fintype.card n : ℝ)) : ℝ) : ℂ) := by push_cast; rfl
  rw [hd, ← Complex.ofReal_mul, Complex.ofReal_re]
  field_simp [hc]
  <;> ring

/-- Actual final Pauli-Z expectation of the circuit, from density evolution. -/
theorem trace_test [Nonempty n] (V : Matrix n n ℂ) (hV : Unitary V) :
    expectationZ (output V) = (Matrix.trace V).re / Fintype.card n := by
  have hsum := measurement_sum (output V)
  rw [output_trace V hV] at hsum
  have hzero := probZero_output V hV
  simp only [Complex.one_re] at hsum
  unfold expectationZ
  have hc : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := n)
  have hdiv : (Matrix.trace V).re / Fintype.card n =
      2 * ((Matrix.trace V).re / (2 * Fintype.card n)) := by field_simp [hc]
  rw [hdiv]
  linarith

/-- With acceptance on outcome zero, Pauli-Z expectation is the signed acceptance bias. -/
lemma output_signedBias [Nonempty n] (V : Matrix n n ℂ) (hV : Unitary V) :
    expectationZ (output V) = 2 * probZero (output V) - 1 := by
  have hsum := measurement_sum (output V)
  rw [output_trace V hV] at hsum
  simp only [Complex.one_re] at hsum
  unfold expectationZ
  linarith

/-- Hermitian projectors give legal reflection gates; no reflection legality is assumed. -/
lemma reflection_unitary (P : Matrix n n ℂ) (hP : P.IsHermitian) (hPP : P * P = P) :
    Unitary ((2 : ℂ) • P - 1) := by
  have hstar : ((2 : ℂ) • P - 1).conjTranspose = (2 : ℂ) • P - 1 := by
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP.eq]
  have hsquare : ((2 : ℂ) • P - 1) * ((2 : ℂ) • P - 1) = 1 := by
    rw [two_smul]
    noncomm_ring [hPP]
  rw [Unitary, hstar]
  exact ⟨hsquare, hsquare⟩

/-- The auxiliary maximally mixed bit chooses the two unitary blocks of Lemma 6. -/
def reflectedTraceUnitary (P W : Matrix n n ℂ) : ProbeMatrix n :=
  Matrix.fromBlocks W 0 0 (((2 : ℂ) • P - 1) * W)

lemma reflectedTraceUnitary_unitary (P W : Matrix n n ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (hW : Unitary W) :
    Unitary (reflectedTraceUnitary P W) := by
  have hRW := unitary_mul (reflection_unitary P hP hPP) hW
  constructor <;>
    simp only [reflectedTraceUnitary, Matrix.fromBlocks_conjTranspose,
      Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add]
  · rw [hW.1, hRW.1, block_identity]
  · rw [hW.2, hRW.2, block_identity]

lemma reflectedTraceUnitary_trace (P W : Matrix n n ℂ) :
    Matrix.trace (reflectedTraceUnitary P W) = 2 * Matrix.trace (P * W) := by
  rw [reflectedTraceUnitary, trace_blocks, sub_mul, smul_mul_assoc, one_mul,
    Matrix.trace_sub, Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

/-- Lemma 6 as an operational trace test with unitary implementation and valid probabilities. -/
theorem ancillary_block_readout [Nonempty n] (P W : Matrix n n ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (hW : Unitary W) :
    Unitary (circuit (reflectedTraceUnitary P W)) ∧
      (0 ≤ probZero (output (reflectedTraceUnitary P W)) ∧
        probZero (output (reflectedTraceUnitary P W)) ≤ 1) ∧
      expectationZ (output (reflectedTraceUnitary P W)) =
        (Matrix.trace (P * W)).re / Fintype.card n := by
  have hV := reflectedTraceUnitary_unitary P W hP hPP hW
  refine ⟨circuit_unitary _ hV, ?_, ?_⟩
  · have h := output_probabilities _ hV
    exact ⟨h.1, h.2.1⟩
  · rw [trace_test _ hV, reflectedTraceUnitary_trace]
    simp only [Fintype.card_sum, Nat.cast_add]
    norm_num [Complex.mul_re]
    have hc : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := n)
    field_simp
    <;> ring

/-- Identification of the two-summand representation with the probe-target tensor basis. -/
def tensorBasis : (Fin 2 × n) ≃ (n ⊕ n) where
  toFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  invFun p := match p with | Sum.inl i => (0, i) | Sum.inr i => (1, i)
  left_inv p := by rcases p with ⟨i, a⟩; fin_cases i <;> simp
  right_inv p := by rcases p with a | a <;> simp

/-- The density is literally `|0⟩⟨0| ⊗ I/N` in the tensor-product basis. -/
lemma input_tensor : (input : ProbeMatrix n).submatrix tensorBasis tensorBasis =
    Matrix.kronecker (Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0))
      ((Fintype.card n : ℂ)⁻¹ • (1 : Matrix n n ℂ)) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;>
    simp [input, tensorBasis, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply,
      Matrix.diagonal]

/-- A specified all-zero ancillary block, tensored with the catalyst identity. -/
def ancillaryProjector (a : Type*) [Fintype a] [DecidableEq a] (z : a) :
    Matrix (a × n) (a × n) ℂ := Matrix.diagonal (fun i => if i.1 = z then 1 else 0)

lemma ancillaryProjector_hermitian (a : Type*) [Fintype a] [DecidableEq a] (z : a) :
    (ancillaryProjector (n := n) a z).IsHermitian := by
  apply Matrix.PosSemidef.isHermitian
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ if i.1 = z then 1 else 0
  split_ifs <;> simp

lemma ancillaryProjector_idempotent (a : Type*) [Fintype a] [DecidableEq a] (z : a) :
    ancillaryProjector (n := n) a z * ancillaryProjector a z = ancillaryProjector a z := by
  rw [ancillaryProjector, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

/-- Multiplying by the ancillary projector selects precisely the source's small block. -/
lemma trace_ancillaryProjector (a : Type*) [Fintype a] [DecidableEq a] (z : a)
    (W : Matrix (a × n) (a × n) ℂ) :
    Matrix.trace (ancillaryProjector a z * W) =
      Matrix.trace (W.submatrix (fun i => (z, i)) (fun i => (z, i))) := by
  simp only [ancillaryProjector, Matrix.diagonal_mul, Matrix.trace,
    Matrix.diag_apply, Matrix.submatrix_apply]
  rw [Fintype.sum_prod_type]
  simp

/-- Source Lemma 6, with the all-zero block and the auxiliary mixed bit explicit. -/
theorem lemma6 [Nonempty n] (k : ℕ)
    (W : Matrix (Fin (2 ^ k) × n) (Fin (2 ^ k) × n) ℂ) (hW : Unitary W) :
    let P := ancillaryProjector (Fin (2 ^ k)) (0 : Fin (2 ^ k))
    let a := (Matrix.trace (W.submatrix (fun i => (0, i)) (fun i => (0, i)))).re /
      Fintype.card n
    expectationZ (output (reflectedTraceUnitary P W)) = a / (2 ^ k : ℝ) := by
  dsimp only
  have h := (ancillary_block_readout
    (ancillaryProjector (Fin (2 ^ k)) (0 : Fin (2 ^ k))) W
    (ancillaryProjector_hermitian _ _) (ancillaryProjector_idempotent _ _) hW).2.2
  rw [trace_ancillaryProjector] at h
  rw [h]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

end Paper25.OneCleanQubit
