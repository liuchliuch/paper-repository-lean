import Paper22.Basic
import Paper22.Programs
import Paper22.EffectCompletion
import Paper22.OneShot
import Paper22.ReliabilityReduction

/-!
# Paper statements

Independently readable statements for the numbered results of
"Non-signaling reliability of classical-quantum channels with full-rank outputs"
(the original source inventory is summarized in `README.md`).
-/

open scoped MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace Paper22.PaperStatements

/-- **Lemma 1 (Effect completion).**
Let `M ≥ 2` be an integer and put `K = M + 6`. Suppose `q` is a probability distribution
on a finite set and `Tₓ` are effects on a finite-dimensional Hilbert space such that
`A := ∑ₓ qₓ Tₓ ≤ I/K`. Then there are effects `Qₓ` satisfying
`Tₓ ≤ Qₓ ≤ I` and `∑ₓ qₓ Qₓ = I/M`. -/
def lemma_1_effect_completion : Prop :=
  ∀ (n d : ℕ) (M : ℕ), 2 ≤ M → ∀ (K : ℕ), K = M + 6 →
    ∀ (q : Fin n → ℝ), (∀ i, 0 ≤ q i) → (∑ i, q i = 1) →
      ∀ (T : Fin n → Matrix (Fin d) (Fin d) ℂ), (∀ x, IsEffect (T x)) →
        ((∑ x, q x • T x) ≤ (1 / (K : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) →
          ∃ Q : Fin n → Matrix (Fin d) (Fin d) ℂ,
            (∀ x, IsEffect (Q x)) ∧ (∀ x, T x ≤ Q x) ∧
            ((∑ x, q x • Q x) = (1 / (M : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ))

/-- **Theorem 1 (One-shot comparison).**
For every finite cq channel `V` and integer `M ≥ 2`,
`ε_MC(M,V) ≤ ε_NS(M,V) ≤ ε_MC(M+6,V)`. -/
def theorem_1_one_shot : Prop :=
  ∀ (n d : ℕ) (V : CQChannel n d) (M : ℕ), 2 ≤ M →
    epsMC V M ≤ epsNS V M ∧ epsNS V M ≤ epsMC V (M + 6)

/-- The original, unconditional mathematical conclusion of Theorem 2.
This definition records the original quantifiers. Its external exponent dependency
is deliberately explicit in the verified contract below. -/
def theorem_2_reliability_original : Prop :=
  ∀ (n d : ℕ) (W : CQChannel n d), W.FullRank →
    ∀ R : ℝ, 0 < R → R < holevoCapacity W →
      Filter.Tendsto (nsErrorExpEReal W R) Filter.atTop (nhds (spherePackingExtended W R)) ∧
      Filter.Tendsto (ansErrorExpEReal W R) Filter.atTop (nhds (spherePackingExtended W R))

/-- **Theorem 2, relative to the published meta-converse exponent.**
The user's updated external-result policy permits the explicitly cited Eq23 as
an external input. All original channel and rate quantifiers remain in the
conclusion. Eq26 has been proved internally, so there is no activation premise.
See external-dependencies.json for the exact source, assumptions, unit conversion,
and use sites. This contract does not claim a Lean proof of Eq23 itself. -/
def theorem_2_reliability : Prop :=
  ExternalMetaConverseLimit → theorem_2_reliability_original

/-- The earlier two-input transfer statement, retained as valid partial progress. -/
def theorem_2_reliability_legacy_two_inputs : Prop :=
  ∀ (extMeta : ExternalMetaConverseLimit) (extAct : ExternalActivationIdentity)
    (n d : ℕ) (W : CQChannel n d), W.FullRank →
    ∀ R : ℝ, 0 < R → R < holevoCapacity W →
      Filter.Tendsto (nsErrorExpEReal W R) Filter.atTop (nhds (spherePackingExtended W R)) ∧
      Filter.Tendsto (ansErrorExpEReal W R) Filter.atTop (nhds (spherePackingExtended W R))

end Paper22.PaperStatements

end
