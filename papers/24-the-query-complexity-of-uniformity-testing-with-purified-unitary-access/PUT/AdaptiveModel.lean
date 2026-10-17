import PUT.SourceTargets

/-!
# Finite adaptive projective-query protocols

The syntax permits branch-dependent known unitaries, query directions,
measurements, and early termination. Its semantics propagates unnormalized
branch vectors, so the squared norm at each leaf is its actual probability.

The external normalization law is stated separately from all lower bounds.
It uses exactly `2*Q` fixed-direction controlled calls: one forward slot and
one inverse slot per adaptive query depth, with inactive padding on all
other histories. This factor is necessary to allow different branches to
choose opposite directions for arbitrary preparation unitaries.
-/
noncomputable section
namespace PUT.AdaptiveModel
open PUT.QueryModel PUT.SourceTargets

/-- A finite adaptive projective-query tree. `halt true` rejects uniformity.
All node labels are fixed independently of the unknown oracle. -/
inductive Protocol (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  | halt (reject : Bool)
  | free (unitary : H ≃ₗᵢ[ℂ] H) (next : Protocol H)
  | query (direction : Direction) (next : Protocol H)
  | measure (measurement : Measurement H) (acceptBranch rejectBranch : Protocol H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Born probability of final rejection, including each measurement history.
Branch vectors are not renormalized: the sum accounts for the history weights. -/
def Protocol.outputReject (U : H ≃ₗᵢ[ℂ] H) : Protocol H → H → ℝ
  | .halt reject, ψ => if reject then ‖ψ‖ ^ 2 else 0
  | .free V next, ψ => next.outputReject U (V ψ)
  | .query direction next, ψ => next.outputReject U (queryUnitary U direction ψ)
  | .measure P acceptBranch rejectBranch, ψ =>
      acceptBranch.outputReject U (P.accept ψ) +
        rejectBranch.outputReject U (P.reject ψ)

/-- Actual maximum number of oracle calls on a root-to-leaf path. -/
def Protocol.worstQueries : Protocol H → ℕ
  | .halt _ => 0
  | .free _ next => next.worstQueries
  | .query _ next => next.worstQueries + 1
  | .measure _ acceptBranch rejectBranch =>
      max acceptBranch.worstQueries rejectBranch.worstQueries

/-- The recursive semantics has the probability bounds expected of a physical
projective protocol, for arbitrary unnormalized input states. -/
theorem Protocol.outputReject_bounds (P : Protocol H) (U : H ≃ₗᵢ[ℂ] H) (ψ : H) :
    0 ≤ P.outputReject U ψ ∧ P.outputReject U ψ ≤ ‖ψ‖ ^ 2 := by
  induction P generalizing ψ with
  | halt reject =>
    cases reject <;> simp [Protocol.outputReject, sq_nonneg]
  | free V next ih =>
    simpa [Protocol.outputReject] using ih (V ψ)
  | query direction next ih =>
    simpa [Protocol.outputReject] using ih (queryUnitary U direction ψ)
  | measure P acceptBranch rejectBranch ihA ihR =>
    obtain ⟨ha0,ha1⟩ := ihA (P.accept ψ)
    obtain ⟨hr0,hr1⟩ := ihR (P.reject ψ)
    constructor
    · exact add_nonneg ha0 hr0
    · exact (add_le_add ha1 hr1).trans_eq (P.pythagoras ψ).symm

/-- A zero-query adaptive protocol's output is still independent of the
unknown oracle, even with arbitrary measurements and early termination. -/
theorem Protocol.zero_queries (P : Protocol H) (hP : P.worstQueries = 0)
    (U V : H ≃ₗᵢ[ℂ] H) (ψ : H) : P.outputReject U ψ = P.outputReject V ψ := by
  induction P generalizing ψ with
  | halt reject => rfl
  | free W next ih => exact ih hP (W ψ)
  | query direction next ih => simp [Protocol.worstQueries] at hP
  | measure P acceptBranch rejectBranch ihA ihR =>
    have ha : acceptBranch.worstQueries = 0 := by
      have := le_max_left acceptBranch.worstQueries rejectBranch.worstQueries
      change max acceptBranch.worstQueries rejectBranch.worstQueries = 0 at hP
      omega
    have hr : rejectBranch.worstQueries = 0 := by
      have := le_max_right acceptBranch.worstQueries rejectBranch.worstQueries
      change max acceptBranch.worstQueries rejectBranch.worstQueries = 0 at hP
      omega
    simp only [Protocol.outputReject, ihA ha, ihR hr]

/-- An adaptive tester works on every finite garbage dimension, with arbitrary
finite physical workspace and an oracle-independent normalized initial state. -/
structure AdaptiveTesterFamily (d : ℕ) where
  workspace : ℕ → ℕ
  initial : ∀ M, TestSpace d M (workspace M)
  initial_norm : ∀ M, ‖initial M‖ = 1
  protocol : ∀ M, Protocol (TestSpace d M (workspace M))

def AdaptiveTesterFamily.oracle {d : ℕ} (A : AdaptiveTesterFamily d) {M : ℕ}
    (U : PreparationOracle d M) :
    TestSpace d M (A.workspace M) ≃ₗᵢ[ℂ] TestSpace d M (A.workspace M) :=
  withWorkspace (ι := Fin (A.workspace M)) (controlled U.unitary)

def AdaptiveTesterFamily.rejectProbability {d : ℕ} (A : AdaptiveTesterFamily d) {M : ℕ}
    (U : PreparationOracle d M) : ℝ :=
  (A.protocol M).outputReject (A.oracle U) (A.initial M)

theorem AdaptiveTesterFamily.probability_bounds {d : ℕ} (A : AdaptiveTesterFamily d)
    {M : ℕ} (U : PreparationOracle d M) :
    0 ≤ A.rejectProbability U ∧ A.rejectProbability U ≤ 1 := by
  have h := (A.protocol M).outputReject_bounds (A.oracle U) (A.initial M)
  simpa only [AdaptiveTesterFamily.rejectProbability, A.initial_norm, one_pow] using h

/-- Uniformity success on every valid promised preparation oracle. -/
def AdaptiveTesterFamily.Tests {d : ℕ} (A : AdaptiveTesterFamily d) (ε : ℝ) : Prop :=
  ∀ (M : ℕ) (U : PreparationOracle d M),
    ((∀ i, U.probability i = (1 : ℝ)/d) → A.rejectProbability U ≤ 1/100) ∧
    (ε < tvDist U.probability (uniform d) → 99/100 ≤ A.rejectProbability U)

/-- A bound on actual oracle calls, determined syntactically for every branch. -/
def AdaptiveTesterFamily.BoundedQueries {d : ℕ} (A : AdaptiveTesterFamily d)
    (Q : ℕ) : Prop := ∀ M, (A.protocol M).worstQueries ≤ Q

def AdaptiveTesterFamily.BoundedTests {d : ℕ} (A : AdaptiveTesterFamily d)
    (ε : ℝ) (Q : ℕ) : Prop := A.Tests ε ∧ A.BoundedQueries Q

/-- Source Theorem 1 for finite adaptive protocols, including early halting
and branch-dependent forward/inverse controlled queries. -/
def AdaptiveTheorem1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (ε : ℝ),
    2 ≤ d → 0 < ε → ε < 1/2 →
    ∀ (A : AdaptiveTesterFamily d) (Q : ℕ), A.BoundedTests ε Q →
      theorem1Bound c d ε ≤ (Q : ℝ)

end PUT.AdaptiveModel

namespace PUT.External
open PUT.QueryModel PUT.SourceTargets PUT.AdaptiveModel

/-- Explicit standard external input: exact unitary purification/deferred
measurement with recorded finite histories and controlled-query padding.

Primary source for unitary purification: John Watrous, *Quantum Computational
Complexity* (2008), Section III.3, Figure 5:
https://cs.uwaterloo.ca/~watrous/Papers/QuantumComputationalComplexity.pdf

This interface specializes that standard circuit principle to finite query
trees and includes the standard two-slot query scheduling consequence. Each
adaptive query depth uses a forward and an inverse controlled slot; inactive
history blocks and stopped branches are padded. The law preserves rejection
on every full oracle, including inputs outside the testing promise. Its
conclusion contains no success condition and no lower bound.
-/
def AdaptiveNormalizationLaw : Prop :=
  ∀ (d : ℕ) (A : AdaptiveTesterFamily d) (Q : ℕ), A.BoundedQueries Q →
    ∃ C : TesterFamily d, ∀ (M : ℕ) (U : PreparationOracle d M),
      (C.circuit M).rejectProbability (C.oracle U) (2*Q) = A.rejectProbability U

end PUT.External

namespace PUT.AdaptiveModel
open PUT.QueryModel PUT.SourceTargets

/-- The external normal-form law only transfers output distributions. The
paper's lower bound for adaptive protocols is derived here, with the factor
of two in query scheduling absorbed into its positive constant. -/
theorem adaptive_lower_of_normalized (hNormal : PUT.External.AdaptiveNormalizationLaw)
    (hMain : SourceTargets.Theorem1) : AdaptiveTheorem1 := by
  obtain ⟨c,hc,hMain⟩ := hMain
  refine ⟨c/2, by positivity, ?_⟩
  intro d ε hd hε hεhalf A Q hA
  obtain ⟨C,hC⟩ := hNormal d A Q hA.2
  have hTests : C.Tests ε (2*Q) := by
    intro M U
    rw [hC M U]
    exact hA.1 M U
  have h := hMain d ε hd hε hεhalf C (2*Q) hTests
  have hcast : ((2*Q : ℕ) : ℝ) = 2*(Q : ℝ) := by norm_cast
  rw [hcast] at h
  unfold theorem1Bound at h ⊢
  linarith

end PUT.AdaptiveModel
