import Paper37.BoundedLoopEncoding
import Mathlib.Computability.TMComputable

/-!
A precise generic binary bounded-loop-to-Turing-machine simulation interface.
The external input quantifies over every first-order Expr and every finite
input list; it contains no renewal predictor, DP, horizon, risk, or cost bound.
All instantiation and polynomial-budget transport below are proved in Lean.
-/
namespace Paper37.BoundedLoopMachine
noncomputable section
open Paper37.BoundedLoop Paper37.BoundedLoopEncoding

/-- Actual input length, dynamic evaluator charge, and actual intermediate
representation peak, with a deliberately loose generic simulation exponent.
Binary schoolbook primitives cost quadratically in representation size;
a cubic RAM-to-single-tape simulation gives a total degree at most nine. -/
def executionBudget (e : Expr) (xs : List Value) : ℕ :=
  (e.work (inputEnv xs) + (inputEncoding.encode xs).length + e.peak (inputEnv xs) + 1)^9

/-- A real finite TM2 and a pointwise execution proof on the concrete bit
encoding. In addition to Mathlib's finite labels, states, and stack set, every
internal stack alphabet is explicitly finite. This excludes hiding unbounded
integers or semantic operations in an infinite tape alphabet. -/
structure Compilation (e : Expr) extends Turing.TM2ComputableAux Bool Bool where
  finiteAlphabets : ∀ k : tm.K, Finite (tm.Γ k)
  constant : ℕ
  constant_pos : 0 < constant
  outputs : ∀ xs : List Value,
    Turing.TM2OutputsInTime tm
      (List.map inputAlphabet.invFun (inputEncoding.encode xs))
      (some (List.map outputAlphabet.invFun (valueEncoding.encode (runProgram e xs))))
      (constant * executionBudget e xs)

/-- The sole computational external theorem input: the generic finite-language
binary interpreter simulation. Its quantifiers cover ALL syntax and inputs.
The source is the standard RAM/Turing polynomial simulation, John E. Savage,
*Models of Computation* (1998), §8.4.1, Theorem 8.4.1, pp.331–332:
https://cs.brown.edu/people/jsavage/book/pdfs/ModelsOfComputation_Chapter8.pdf
The theorem states a cubic deterministic-TM simulation for the elementary RAM
instruction set. Here its usual finite bounded-loop interpreter specialization
first implements binary multiplication/division by schoolbook bit operations,
and arrays by delimited finite sequences. Fixed syntax/register-stack factors
are absorbed in the program constant. An operation uses at most quadratic work
in the reached representation size; cubing yields the intentionally loose
ninth-power bound. The concrete encoding, dynamic operands, and source charge
are fixed above rather than supplied by the caller.

This specialization is an explicitly disclosed theorem parameter, not an axiom
or a claimed Lean proof of the generic interpreter compiler. No paper-specific
algorithmic step or polynomial operand bound is part of this input. -/
def BoundedLoopSimulationPrinciple : Prop := ∀ e : Expr, Nonempty (Compilation e)

noncomputable def compiler (simulation : BoundedLoopSimulationPrinciple) (e : Expr) : Compilation e :=
  Classical.choice (simulation e)

/-- Increasing a time budget preserves the very same terminating machine
execution and its actual step count. -/
def outputsInTime_mono {tm : Turing.FinTM2}
    {a : List (tm.Γ tm.k₀)} {b : Option (List (tm.Γ tm.k₁))} {m n : ℕ}
    (h : Turing.TM2OutputsInTime tm a b m) (hmn : m ≤ n) :
    Turing.TM2OutputsInTime tm a b n :=
  { toEvalsTo := h.toEvalsTo
    steps_le_m := h.steps_le_m.trans hmn }

/-- The explicit time polynomial used by the generic transport theorem. -/
def timePolynomial (C : ℕ) (W I S : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C C * (W+I+S+1)^9

lemma timePolynomial_eval (C : ℕ) (W I S : Polynomial ℕ) (n : ℕ) :
    (timePolynomial C W I S).eval n = C*(W.eval n+I.eval n+S.eval n+1)^9 := by
  simp only [timePolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_one]

lemma executionBudget_le (e : Expr) (xs : List Value) (W I S : ℕ)
    (hw : e.work (inputEnv xs)≤W) (hi : (inputEncoding.encode xs).length≤I)
    (hs : e.peak (inputEnv xs)≤S) : executionBudget e xs≤(W+I+S+1)^9 := by
  unfold executionBudget
  apply Nat.pow_le_pow_left
  omega

/-- Arbitrary source parameters may bound work, encoded input, and the true
execution peak. The result is an actual finite machine plus a polynomial in
that parameter, even when the parameter is a numerical horizon rather than
the length of a binary-coded horizon. -/
theorem machine_with_polynomial_budget (simulation : BoundedLoopSimulationPrinciple)
    (e : Expr) (valid : List Value → Prop) (size : List Value → ℕ)
    (W I S : Polynomial ℕ)
    (hw : ∀ xs, valid xs → e.work (inputEnv xs)≤W.eval (size xs))
    (hi : ∀ xs, valid xs → (inputEncoding.encode xs).length≤I.eval (size xs))
    (hs : ∀ xs, valid xs → e.peak (inputEnv xs)≤S.eval (size xs)) :
    ∃ M : Turing.TM2ComputableAux Bool Bool,
      (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
      ∃ p : Polynomial ℕ, ∀ xs, valid xs →
        Nonempty (Turing.TM2OutputsInTime M.tm
          (List.map M.inputAlphabet.invFun (inputEncoding.encode xs))
          (some (List.map M.outputAlphabet.invFun (valueEncoding.encode (runProgram e xs))))
          (p.eval (size xs))) := by
  let c := compiler simulation e
  refine ⟨c.toTM2ComputableAux,c.finiteAlphabets,timePolynomial c.constant W I S,?_⟩
  intro xs hx
  refine ⟨?_⟩
  apply outputsInTime_mono (c.outputs xs)
  rw [timePolynomial_eval]
  exact Nat.mul_le_mul_left c.constant
    (executionBudget_le e xs _ _ _ (hw xs hx) (hi xs hx) (hs xs hx))

/-- Restricting the domain keeps exactly the same explicit bit strings. The
machine is not asked to check the validity predicate or synthesize an input. -/
noncomputable def restrictedInputEncoding (valid : List Value → Prop) :
    Computability.FinEncoding {xs : List Value // valid xs} := by
  classical
  exact {
    Γ := Bool
    encode xs := inputEncoding.encode xs.val
    decode bs := (inputEncoding.decode bs).bind (fun xs => if h : valid xs then some ⟨xs,h⟩ else none)
    decode_encode xs := by simp [inputEncoding.decode_encode,xs.property]
    ΓFin := inferInstance }

/-- Polynomial work and intermediate representations in actual encoded input
length imply Mathlib's bundled TM2ComputableInPolyTime, with all alphabets
finite and the machine computing the original evaluator's exact output. -/
theorem computableInPolyTime (simulation : BoundedLoopSimulationPrinciple)
    (e : Expr) (valid : List Value → Prop) (W S : Polynomial ℕ)
    (hw : ∀ xs, valid xs → e.work (inputEnv xs)≤W.eval (inputEncoding.encode xs).length)
    (hs : ∀ xs, valid xs → e.peak (inputEnv xs)≤S.eval (inputEncoding.encode xs).length) :
    ∃ M : Turing.TM2ComputableInPolyTime (restrictedInputEncoding valid) valueEncoding
      (fun xs => runProgram e xs.val), ∀ k : M.tm.K, Finite (M.tm.Γ k) := by
  let c := compiler simulation e
  let M : Turing.TM2ComputableInPolyTime (restrictedInputEncoding valid) valueEncoding
      (fun xs => runProgram e xs.val) := {
    toTM2ComputableAux := c.toTM2ComputableAux
    time := timePolynomial c.constant W Polynomial.X S
    outputsFun := by
      intro xs
      change Turing.TM2OutputsInTime c.tm
        (List.map c.inputAlphabet.invFun (inputEncoding.encode xs.val))
        (some (List.map c.outputAlphabet.invFun (valueEncoding.encode (runProgram e xs.val)))) _
      apply outputsInTime_mono (c.outputs xs.val)
      rw [timePolynomial_eval,Polynomial.eval_X]
      exact Nat.mul_le_mul_left c.constant
        (executionBudget_le e xs.val _ _ _ (hw xs.val xs.property) (le_refl _) (hs xs.val xs.property)) }
  exact ⟨M,c.finiteAlphabets⟩

/-- The same genuine finite TM, forgetting only the polynomial representation
of its time function, has the requested TM2ComputableInTime interface. -/
theorem computableInTime (simulation : BoundedLoopSimulationPrinciple)
    (e : Expr) (valid : List Value → Prop) (W S : Polynomial ℕ)
    (hw : ∀ xs, valid xs → e.work (inputEnv xs)≤W.eval (inputEncoding.encode xs).length)
    (hs : ∀ xs, valid xs → e.peak (inputEnv xs)≤S.eval (inputEncoding.encode xs).length) :
    ∃ M : Turing.TM2ComputableInTime (restrictedInputEncoding valid) valueEncoding
      (fun xs => runProgram e xs.val), ∀ k : M.tm.K, Finite (M.tm.Γ k) := by
  obtain ⟨M,hM⟩ := computableInPolyTime simulation e valid W S hw hs
  exact ⟨M.toTM2ComputableInTime,hM⟩

end
end Paper37.BoundedLoopMachine
