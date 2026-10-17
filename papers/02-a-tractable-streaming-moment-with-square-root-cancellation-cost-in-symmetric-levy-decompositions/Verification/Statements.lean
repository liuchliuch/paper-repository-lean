import Paper02.Basic
import Paper02.RudinShapiro
import Paper02.LSym
import Paper02.Bounds
import Paper02.Main
import Paper02.Bernstein
import Paper02.BernsteinAnalytic
import Paper02.WeightEval
import Paper02.BernsteinRepresentation
import Paper02.SparseRecovery
import Paper02.StreamingSpace
import Paper02.Streaming
import Paper02.SparseRecoverySpace
import Paper02.GenericTractability

/-!
# Independently readable Comparator specification for paper 02

These specifications distinguish full source statements from auxiliary
estimates. Coverage of the complete paper is tracked separately in
`publication.json`; successful comparison does not establish unlisted claims.
-/

namespace Verification.Specification

open Paper02 Paper02.RS Paper02.LSym Paper02.Bounds Paper02.Main Paper02.Bernstein Real

/-- Theorem 1.1: `f` is even, bounded by 3, vanishes at 0. -/
def Theorem11_f_props : Prop :=
  f 0 = 0 ∧ (∀ k : ℤ, 0 ≤ f k) ∧ (∀ k : ℤ, f k ≤ 3) ∧ (∀ k : ℤ, f (-k) = f k)

/-- Lemma 2.4: `T_m + U_m = 2^m - 1`. -/
def Lemma24_transitions : Prop :=
  ∀ m : ℕ, T m + U m = 2 ^ m - 1

/-- Lemma 2.1 kernel: `D(A k²) = A`. -/
def Lemma21_gaussian : Prop :=
  ∀ (A : ℝ) (k : ℤ), secondDiff (fun x : ℤ => A * (x : ℝ) ^ 2) k = A

/-- Lemma 2.1 kernel: `D(1-cos(k s)) = (1-cos s) cos(k s)`. -/
def Lemma21_cos : Prop :=
  ∀ (s : ℝ) (k : ℤ),
    secondDiff (fun x : ℤ => 1 - Real.cos ((x : ℝ) * s)) k
      = (1 - Real.cos s) * Real.cos ((k : ℝ) * s)

/-- Corollary 2.2, Gaussian part. -/
def Cor22_gaussian : Prop :=
  ∀ {ι : Type} [Fintype ι] (a : ι → ℝ) (k : ι → ℤ) (A : ℝ),
    0 ≤ A → ∀ (M : ℝ),
    (∀ t : ℝ, |∑ i, a i * Real.cos ((k i : ℝ) * t)| ≤ M) →
    |∑ i, a i * secondDiff (fun x : ℤ => A * (x : ℝ) ^ 2) (k i)| ≤ A * M

/-- Corollary 2.2, finite atomic jump part. -/
def Cor22_atomic : Prop :=
  ∀ {ι J : Type} [Fintype ι] [Fintype J]
    (a : ι → ℝ) (k : ι → ℤ) (c : J → ℝ) (s : J → ℝ),
    (∀ j, 0 ≤ c j) → ∀ (M : ℝ),
    (∀ t : ℝ, |∑ i, a i * Real.cos ((k i : ℝ) * t)| ≤ M) →
    |∑ i, a i * secondDiff
        (fun x : ℤ => ∑ j, c j * (1 - Real.cos ((x : ℝ) * s j))) (k i)|
      ≤ (∑ j, c j * (1 - Real.cos (s j))) * M

/-- Proposition 3.1 (algebraic core). -/
def Prop31_algebra : Prop :=
  ∀ (N : ℕ) (η ρ s1 : ℝ), 16 ≤ N → η < 1 / 6 →
    (1 - 6 * η) * ((N:ℝ) - 3) ≤ s1 * (Real.sqrt (2 * (N:ℝ)) + 3) →
    s1 ≤ 3 * ρ →
    (1 - 6 * η) * ((N:ℝ) - 3) / (3 * (Real.sqrt (2 * (N:ℝ)) + 3)) ≤ ρ

/-- Proposition 3.3 (Cauchy–Schwarz / Parseval). -/
def Prop33_bound : Prop :=
  ∀ (p : ℕ) (c : Fin p → ℝ), 0 < p → (∑ j, |c j| ^ 2 ≤ 9) →
    (∑ j, |c j|) ≤ 3 * Real.sqrt (p:ℝ)

/-- Proposition B.2 ratio identity. -/
def PropB2_ratio : Prop :=
  ∀ (α k : ℝ), k ≠ 0 → α > 0 →
    ((α⁻¹ * k ^ 2 - α⁻¹ * k ^ 2 / (1 + |k|) ^ α) / (k ^ 2 * log (1 + |k|)))
      = (1 - Real.exp (-α * log (1 + |k|))) / (α * log (1 + |k|))

/-- Proposition B.2 envelope (B.4). -/
def PropB2_envelope : Prop :=
  ∀ (α k : ℝ), 1 ≤ |k| → α > 0 →
    α⁻¹ * k ^ 2 + α⁻¹ * k ^ 2 / (1 + |k|) ^ α
      ≤ (2 / (α * log 2)) * (k ^ 2 * log (1 + |k|))

/-- Error of second differences under a uniform pointwise bound. -/
def SecondDiff_error : Prop :=
  ∀ (e : ℤ → ℝ) (k : ℤ) (η : ℝ),
    |e (k + 1)| ≤ 3 * η → |e k| ≤ 3 * η → |e (k - 1)| ≤ 3 * η →
    |secondDiff e k| ≤ 6 * η

/-- Lemma 2.1 on the actual circle, for arbitrary original Lévy measures. -/
def Lemma21_full : Prop :=
  ∀ g : ℝ → ℝ, IsLSym g →
    ∃ μ : MeasureTheory.Measure Real.Angle, MeasureTheory.IsFiniteMeasure μ ∧
      μ Set.univ = ENNReal.ofReal (g 1) ∧
      ∀ k : ℤ, secondDiff (RestrictInt g) k =
        ∫ t : Real.Angle, Real.Angle.cos (k • t) ∂μ

/-- Corollary 2.2 with the exact uniform norm, without an assumed bound. -/
def Cor22_full : Prop :=
  ∀ {ι : Type} [Fintype ι] (gp gn : ℝ → ℝ), IsLSym gp → IsLSym gn →
    ∀ (a : ι → ℝ) (k : ι → ℤ),
      |∑ i, a i * secondDiff (RestrictInt (fun x => gp x - gn x)) (k i)| ≤
        (gp 1 + gn 1) * cosinePolynomialNorm a k

/-- Remark 2.3: continuous generators, original normalized representation,
probability mixture, and the complete zero-mass conclusion. -/
def Remark23_full : Prop :=
  (∀ k : ℤ, Continuous (normalizedGenerator k)) ∧
  (∀ (g : ℝ → ℝ) (c : LSymCert g) (k : ℤ),
    g (k : ℝ) = ∫ t, normalizedGenerator k t ∂circleMeasure c) ∧
  (∀ g : ℝ → ℝ, IsLSym g → 0 < g 1 →
    ∃ μ : MeasureTheory.Measure Real.Angle, MeasureTheory.IsProbabilityMeasure μ ∧
      ∀ k : ℤ, g (k : ℝ) / g 1 = ∫ t, normalizedGenerator k t ∂μ) ∧
  (∀ (g : ℝ → ℝ) (c : LSymCert g), g 1 = 0 →
    c.A = 0 ∧ ∀ᵐ s ∂c.ν, ∃ n : ℤ, 0 < n ∧ (n : ℝ) * (2 * Real.pi) = s) ∧
  (∀ g : ℝ → ℝ, IsLSym g → g 1 = 0 → ∀ k : ℤ, g (k : ℝ) = 0)

/-- Lemma 2.4: the classical P/Q words, full norm identity, and both counts. -/
def Lemma24_full : Prop :=
  ∀ (m : ℕ) (t : ℝ),
    ‖RP m (Complex.exp ((t : ℂ) * Complex.I))‖ ^ 2 +
      ‖SQ m (Complex.exp ((t : ℂ) * Complex.I))‖ ^ 2 = 2 * (2 ^ m : ℕ) ∧
    ‖RP m (Complex.exp ((t : ℂ) * Complex.I))‖ ≤ Real.sqrt (2 * (2 ^ m : ℕ)) ∧
    T m + U m = 2 ^ m - 1 ∧
    (2 ≤ m → T m = if Odd m then 2 ^ m / 2 else 2 ^ m / 2 - 1)

/-- Lemma 2.5 with the actual target (1.6) and exact endpoints. -/
def Lemma25_full : Prop :=
  ∀ m : ℕ, 16 ≤ 2 ^ m →
    (∑ k ∈ Finset.Icc 2 (2 ^ m - 2), rudinShapiro k * secondDiff f (k : ℤ)) =
      if Odd m then -((2 ^ m : ℕ) : ℝ) + 1 else -((2 ^ m : ℕ) : ℝ) + 3

/-- Proposition 3.1 from its original hypotheses, without a pairing premise. -/
def Prop31_full : Prop :=
  ∀ (m : ℕ) (η ρ : ℝ) (gp gn : ℝ → ℝ),
    16 ≤ 2 ^ m → 0 ≤ η → η < 1 / 6 →
    AdmissibleLSymPair gp gn f (2 ^ m - 1) η ρ →
    (1 - 6 * η) * (((2 ^ m : ℕ) : ℝ) - 3) /
      (3 * (Real.sqrt (2 * (2 ^ m : ℕ)) + 3)) ≤ ρ

def Cor32_full : Prop :=
  ∀ n : ℕ, 15 ≤ n → ∀ η : ℝ, 0 ≤ η → η < 1 / 6 →
    (1 - 6 * η) * Real.sqrt ((n : ℝ) + 1) / (8 * Real.sqrt 2) < rho f n η

/-- Proposition 3.3, with an actual finite atomic Lévy split. -/
def Prop33_full : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ gp gn : ℝ → ℝ,
    AdmissibleLSymPair gp gn f n 0 (6 * Real.sqrt (2 * (n : ℝ) + 1))

/-- The complete cancellation-cost chain of Theorem 1.1; streaming is separate. -/
def Theorem11_bounds : Prop :=
  ∀ n : ℕ, 15 ≤ n → ∀ η : ℝ, 0 < η → η < 1 / 6 →
    (1 - 6 * η) * Real.sqrt ((n : ℝ) + 1) / (8 * Real.sqrt 2) < rho f n η ∧
      rho f n η ≤ rho f n 0 ∧ rho f n 0 ≤ 6 * Real.sqrt (2 * (n : ℝ) + 1)

def Theorem11_theta : Prop :=
  ∀ η : ℝ, 0 < η → η < 1 / 6 →
    Asymptotics.IsTheta Filter.atTop (fun n : ℕ => rho f n η)
      (fun n : ℕ => Real.sqrt (n : ℝ))

/-- The analytic obstruction to the original bivariate polynomial bound. -/
def No_polynomial_control : Prop :=
  ¬ ∃ Q : Polynomial (Polynomial ℝ), ∀ n : ℕ, 1 ≤ n →
    ∀ η : ℝ, 0 < η → η < 1 →
      rho f n η ≤ (Q.eval (Polynomial.C η⁻¹)).eval (log (2 * (n : ℝ)))

/-- Lemma B.1 using precisely the analytic characterization stated in Appendix B. -/
def LemmaB1_full : Prop :=
  ∀ a b c : ℝ, 0 < a → a ≤ 1 → 0 < b → b ≤ 1 → 0 ≤ c → b * c ≤ a →
    CompleteBernsteinZero (bernsteinKernel a b c)

/-- Both inequalities (B.5), for every positive y. -/
def B5_full : Prop :=
  ∀ y : ℝ, 0 < y → 1 - y / 2 ≤ (1 - exp (-y)) / y ∧ (1 - exp (-y)) / y ≤ 1

/-- The full explicit B.2 approximation and envelope; the negative exponent's
Lévy membership is deliberately not included in this auxiliary statement. -/
def PropB2_estimates : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    AdmissibleSplit
      (RestrictInt (singlePositive (singleAlpha n ε)))
      (RestrictInt (singleNegative (singleAlpha n ε)))
      (fun k => singleMoment k) n ε (log (1 + n) / (ε * log 2))

/-- The full explicit B.3 approximation/envelope with a uniform constant.
Membership of the two exponents in the original Lévy cone remains separate. -/
def PropB3_estimates : Prop :=
  ∀ p β : ℝ, 0 < p → p ≤ 2 → 0 < β → β ≤ 2 →
    ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    AdmissibleSplit
      (RestrictInt (powerPositive p β (powerAlpha p β m n ε) m))
      (RestrictInt (powerNegative p β (powerAlpha p β m n ε) m))
      (fun k => powerMoment p β m k) n ε (powerCancellation p β m n ε) ∧
    powerCancellation p β m n ε ≤
      powerCostConstant p β m * (ε⁻¹ * log (n : ℝ)) ^ m

/-- The actual executable integer-valued witness equals the source target. -/
def Witness_evaluator : Prop :=
  ∀ k : ℤ, (Paper02.WeightEval.weight k : ℝ) = f k

/-- The cost chain also uses the paper's faithful empty-set=∞ definition. -/
def Theorem11_ennreal_bounds : Prop :=
  ∀ n : ℕ, 15 ≤ n → ∀ η : ℝ, 0 < η → η < 1 / 6 →
    ENNReal.ofReal ((1 - 6 * η) * Real.sqrt ((n : ℝ) + 1) / (8 * Real.sqrt 2)) <
      Paper02.Cutoff.rhoExtended f n η ∧
    Paper02.Cutoff.rhoExtended f n η ≤ Paper02.Cutoff.rhoExtended f n 0 ∧
    Paper02.Cutoff.rhoExtended f n 0 ≤ ENNReal.ofReal (6 * Real.sqrt (2 * (n : ℝ) + 1))

/-- The general Gaussian-mixture subordination used after (B.1). -/
def Gaussian_mixture : Prop :=
  ∀ μ : MeasureTheory.Measure ℝ, (∀ᵐ u ∂μ, 0 ≤ u) →
    MeasureTheory.Integrable (fun u : ℝ => min u 1) μ →
    IsLSym (fun x : ℝ => ∫ u, (1 - exp (-u * x ^ 2)) ∂μ)

/-- Subordination from an actual positive Bernstein representation, explicitly
distinct from the still-unproved analytic-to-measure implication. -/
def Bernstein_representation_subordination : Prop :=
  ∀ φ : ℝ → ℝ, HasBernsteinRepresentation φ → IsLSym (fun x : ℝ => φ (x ^ 2))

/-- The actual Hankel decoder's exact-recovery and dense-rejection guarantees
in A.1. Operational workspace and running time are separate claims. -/
def LemmaA1_correctness : Prop :=
  ∀ {d q U K : ℕ} [Fact q.Prime], d < q → 2 * U < q →
    ∀ v : Fin d → ℤ, (∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U) →
      (∀ z : ZMod q, (Paper02.SparseRecovery.integerSupport v).card ≤ K →
        Paper02.SparseRecovery.decodeHankelSummary U K z
          (Paper02.SparseRecovery.integerSummary K z v) = some v) ∧
      (K < (Paper02.SparseRecovery.integerSupport v).card →
        ((Finset.univ.filter (fun z : ZMod q =>
          Paper02.SparseRecovery.decodeHankelSummary (d := d) U K z
            (Paper02.SparseRecovery.integerSummary K z v) ≠ none)).card : ℝ) / q ≤
          (d : ℝ) / q)

/-- The exact finite online summary's bit capacity in A.1. -/
def LemmaA1_summary_bits : Prop :=
  ∀ (K q : ℕ) [NeZero q],
    Paper02.StreamingSpace.FitsBits (Paper02.SparseRecovery.Summary K (ZMod q))
      ((2 * K + 1) * Paper02.WeightEval.registerBits q)

/-- The actual one-pass state, real finite affine seeds and independent
checksum seeds satisfy the amplified witness estimate for every fixed stream.
The bounded-workspace execution of the final decoder remains separate. -/
def Witness_stream_probability : Prop :=
  ∀ {d J ℓ q U K : ℕ} [Fact q.Prime],
    d ≤ 2 ^ ℓ → d ≤ 2 ^ J → d < q → 2 * U < q → 2 ≤ K →
    ∀ {ε δ : ℝ}, 0 < ε → ε ≤ 1 → 0 < δ →
      65536 / ε ^ 2 ≤ (K : ℝ) →
      (J + 1 : ℕ) * ((d : ℝ) / q) ≤ 1 / 64 →
      ∀ b : ℕ, 8 * log (1 / δ) ≤ (2 * b + 1 : ℕ) →
      ∀ stream : List (Paper02.SparseRecovery.Update d),
        (∀ i, -(U : ℤ) ≤ Paper02.SparseRecovery.finalVector stream i ∧
          Paper02.SparseRecovery.finalVector stream i ≤ U) →
        ((Paper02.Sampling.FiniteLaw.uniform (Paper02.Streaming.CopySeed J ℓ q)).iid
          (Fin (2 * b + 1))).prob
          {seeds | ε * Paper02.Streaming.moment f (Paper02.SparseRecovery.finalVector stream) <
            |Paper02.Sampling.median b (fun i => Paper02.Streaming.output (d := d) f U K
              (seeds i) (Paper02.Streaming.run K (seeds i) stream)) -
              Paper02.Streaming.moment f (Paper02.SparseRecovery.finalVector stream)|} ≤ δ

/-- A.1's actual halting sparse-recovery implementation, including its input
summary, random checksum and live registers in the O(K² log q) bound. The
separate polynomial running-time consequence is an external-dependency exemption. -/
def LemmaA1_operational : Prop :=
  ∀ {d q U K : ℕ} [Fact q.Prime], 1 ≤ K → d < q → 2 * U < q →
    Paper02.StreamingSpace.FitsBits
      (ZMod q × Paper02.SparseRecovery.Summary K (ZMod q) ×
        Paper02.RecoveryMachine.State d U K q)
      (512 * K ^ 2 * Paper02.WeightEval.registerBits q) ∧
    ∀ (z : ZMod q) (summary : Paper02.SparseRecovery.Summary K (ZMod q)),
      ∃ out : Option (Paper02.CompactCandidates.CompactCode d U K),
        Paper02.RecoveryMachine.Reaches z summary
          (Paper02.RecoveryMachine.initial summary) (.halt out) ∧
        out.map Paper02.CompactCandidates.candidateValue =
          Paper02.SparseRecovery.decodeHankelSummary U K z summary

/-- Proposition 3.4 uses the full operational bit-space streaming class (1.3). -/
def Prop34_full : Prop := Paper02.BitSpaceModel.IsTEvenPlus f

/-- A.2: the only evaluator assumption concerns a single bounded weight.
The conclusion includes update execution, decoder termination, all live bits,
final-vector-only promise and actual failure probability for every fixed stream. -/
def LemmaA2_full : Prop :=
  ∀ w : ℤ → ℕ, w 0 = 0 → (∀ k, k ≠ 0 → 1 ≤ w k) → (∀ k, w k ≤ 3) →
    Paper02.GenericTractability.HasPolylogEvaluator w →
    Paper02.GenericTractability.MomentSketchable (fun k => (w k : ℝ))

/-- Every component of Theorem 1.1, including the faithful +∞ infimum convention. -/
def Theorem11_full : Prop :=
  Paper02.BitSpaceModel.IsTEvenPlus f ∧
  Theorem11_ennreal_bounds ∧
  (∀ n : ℕ, 1 ≤ n → rho f n 0 ≤ 6 * Real.sqrt (2 * (n : ℝ) + 1)) ∧
  Theorem11_theta ∧ No_polynomial_control

end Verification.Specification
