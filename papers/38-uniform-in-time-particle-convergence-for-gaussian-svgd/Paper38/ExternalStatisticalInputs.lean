import Paper38.Sampling

/-!
# Explicit, unformalized external statistical inputs (user-authorized)

No axiom is declared here. Each input is an ordinary argument of theorems using
it. Every constant is chosen before N and the tail parameter; all laws are the
actual raw independent standard Gaussian sample law. None of the fields refers
to the SVGD dynamics, its oracle, an energy sublevel, or particle convergence.

Matching upper: Bobkov--Ledoux [5] Cor.6.14 (d=1), Ledoux [8] Thm1 (d=2),
Ledoux--Zhu [9] Thm1.1, p=2 (d>=3). Lower: [5] Cor6.14, Talagrand [16] main
result/display(1) plus the independent-two-sample triangle argument, [9] Thm1.1.
Finite excluded N are absorbed by a fixed constant, exactly as source S6.p8.

Concentration is the Gaussian isoperimetric Lipschitz concentration for the
raw empirical W2 statistic, and scalar Bernstein applied to the d^2 raw
Gaussian products; source S7.p3 and S7.p7--p8 describe the reduction. Its
specializations below concern only raw sample statistics, not the paper's
all-time event H_N(x). The latter must still be derived using the oracle.

Covariance moments: NS is Wishart_d(N-1,I), source (6.11). Log moment:
Anderson [1], Lemma7.2.1 (Bartlett decomposition), with chi-square log-moment
identities and digamma/trigamma bounds, source (7.17)--(7.19). At N=d+1 no
inverse-covariance moment is postulated.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Paper38.ExternalStatisticalInputs
open Model Sampling

structure Matching (d : ℕ) where
  upperConstant : ℝ
  upper_pos : 0 < upperConstant
  lowerConstant : ℝ
  lower_pos : 0 < lowerConstant
  expected_upper : ∀ N : ℕ, d + 1 ≤ N →
    (∫⁻ ω, rawError d N ω ∂law d N) ≤ ENNReal.ofReal (upperConstant * rate d N)
  expected_lower : ∀ N : ℕ, d + 1 ≤ N →
    ENNReal.ofReal (lowerConstant * rate d N) ≤ ∫⁻ ω, rawError d N ω ∂law d N

/-- The displayed raw covariance moment (6.11) and its integrability. -/
structure CovarianceMoments (d : ℕ) where
  full_rank : ∀ N : ℕ, d + 1 ≤ N →
    ∀ᵐ ω ∂law d N, (covariance d N ω).PosDef
  integrable : ∀ N : ℕ, d + 1 ≤ N →
    Integrable (fun ω => frobSq (1 - covariance d N ω)) (law d N)
  exact_secondMoment : ∀ N : ℕ, d + 1 ≤ N →
    (∫ ω, frobSq (1 - covariance d N ω) ∂law d N) =
      (((N : ℝ) - 1) * d * (d + 1) + d) / (N : ℝ) ^ 2

structure Concentration (d : ℕ) where
  C : ℝ
  c : ℝ
  c0 : ℝ
  C_pos : 0 < C
  c_pos : 0 < c
  c0_pos : 0 < c0
  good_measurable : ∀ N : ℕ, MeasurableSet (good d N)
  good_tail : ∀ N : ℕ, d + 1 ≤ N →
    law d N (good d N)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * N))
  raw_matching_event : ∀ (N : ℕ), d + 1 ≤ N → ∀ x : ℝ, 1 ≤ x →
    ∃ H : Set (Sample d N), MeasurableSet H ∧
      law d N Hᶜ ≤ ENNReal.ofReal (Real.exp (-x)) ∧
      ∀ ω ∈ H, rawError d N ω ≤ ENNReal.ofReal (C * (rate d N + x / N))
  raw_covariance_event : ∀ (N : ℕ), d + 1 ≤ N → ∀ x : ℝ,
    1 ≤ x → x ≤ c0 * N →
    ∃ H : Set (Sample d N), MeasurableSet H ∧
      law d N Hᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * x)) ∧
      ∀ ω ∈ H, defect d N ω ≤ C * (1 + x) / N ∧
        opNorm (covariance d N ω - 1) ≤ 1 / 2

/-- Raw Gaussian moments and log-Wishart input. The subsequent energy-envelope
combination and exceptional-event Cauchy--Schwarz remain own proof obligations. -/
structure LogWishart (d : ℕ) where
  polynomialConstant : ℝ
  logConstant : ℝ
  polynomialConstant_pos : 0 < polynomialConstant
  logConstant_pos : 0 < logConstant
  polynomial_moment : ∀ N : ℕ, d + 1 ≤ N →
    (∫⁻ ω, ENNReal.ofReal (‖mean d N ω‖ ^ 4 + (covariance d N ω).trace ^ 2)
      ∂law d N) ≤ ENNReal.ofReal polynomialConstant
  log_moment : ∀ N : ℕ, d + 1 ≤ N →
    (∫⁻ ω, ENNReal.ofReal (logDetDefect d N ω ^ 2) ∂law d N) ≤
      ENNReal.ofReal logConstant

/-- Equivalent initialized-coordinate raw moment inputs. These are standard
Gaussian sample mean/Wishart trace/log-Wishart moments, not the combined
energy-envelope estimate (7.16). Their constants depend on d, μ0, Σ0 but
precede N. Original hypotheses are the fixed positive definite Σ0 and N≥d+1.
No particle trajectory or potential V occurs. -/
structure InitializedMoments (d : ℕ) (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef) where
  meanConstant : ℝ
  traceConstant : ℝ
  logConstant : ℝ
  meanConstant_nonneg : 0 ≤ meanConstant
  traceConstant_nonneg : 0 ≤ traceConstant
  logConstant_nonneg : 0 ≤ logConstant
  mean_measurable : ∀ N, Measurable (initializedMeanSq μ0 S0 N)
  trace_measurable : ∀ N, Measurable (initializedTrace μ0 S0 N)
  log_measurable : ∀ N, Measurable (initializedLog μ0 S0 N)
  mean_fourth : ∀ N, d + 1 ≤ N →
    (∫⁻ ω, ENNReal.ofReal (initializedMeanSq μ0 S0 N ω ^ 2) ∂law d N) ≤
      ENNReal.ofReal meanConstant
  trace_second : ∀ N, d + 1 ≤ N →
    (∫⁻ ω, ENNReal.ofReal (initializedTrace μ0 S0 N ω ^ 2) ∂law d N) ≤
      ENNReal.ofReal traceConstant
  log_second : ∀ N, d + 1 ≤ N →
    (∫⁻ ω, ENNReal.ofReal (initializedLog μ0 S0 N ω ^ 2) ∂law d N) ≤
      ENNReal.ofReal logConstant

/-- All user-retained raw statistical results, with initialized moments
quantified over every fixed Gaussian population before the sample size. This
is an ordinary theorem-argument bundle and declares no axioms. -/
structure Baselines (d : ℕ) where
  matching : Matching d
  covariance : CovarianceMoments d
  concentration : Concentration d
  initialized : ∀ (μ : E d) (S : Mat d) (hS : S.PosDef), InitializedMoments d μ S hS

end Paper38.ExternalStatisticalInputs
