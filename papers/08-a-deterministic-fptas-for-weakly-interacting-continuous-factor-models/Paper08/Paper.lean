import Paper08.Algorithm
import Paper08.Analytic
import Paper08.AntidiagonalCost
import Paper08.Appendix
import Paper08.ArithmeticBounds
import Paper08.Basic
import Paper08.BitComplexity
import Paper08.BoundedRuleQ
import Paper08.CellGrid
import Paper08.CertifiedConstants
import Paper08.Coeff
import Paper08.ComplexPathLog
import Paper08.ComplexSector
import Paper08.Connected
import Paper08.Cor13
import Paper08.CubeExponentialPath
import Paper08.CubeMarginal
import Paper08.CubeNormLoss
import Paper08.CubeWeighted
import Paper08.CubeZeroFreeMain
import Paper08.CubeZeroFreeParameters
import Paper08.Dyadic
import Paper08.EffectiveAccess
import Paper08.EfficientIdentity
import Paper08.EfficientSupports
import Paper08.Enumeration
import Paper08.FPTAS
import Paper08.FPTASAlgorithm
import Paper08.FPTASCorrectness
import Paper08.FPTASCost
import Paper08.FPTASDiscreteCost
import Paper08.FPTASDiscretePolynomial
import Paper08.FPTASOracleTime
import Paper08.FPTASProgram
import Paper08.FactorModel
import Paper08.FullAlgorithm
import Paper08.FullCorollary
import Paper08.GridSurrogate
import Paper08.ImplementedAlgorithm
import Paper08.Integral
import Paper08.Interaction
import Paper08.LogRecurrence
import Paper08.LowDegreeAlgorithm
import Paper08.LowDegreeComplexity
import Paper08.LowDegreeDiscreteCost
import Paper08.LowDegreeGuarantee
import Paper08.LowDegreePolynomial
import Paper08.LowDegreeProgram
import Paper08.LowerBound
import Paper08.LowerBoundAdaptive
import Paper08.LowerBoundConsequences
import Paper08.LowerBoundGrid
import Paper08.LowerBoundLip
import Paper08.LowerBoundMass
import Paper08.LowerBoundOracle
import Paper08.LowerBoundSmooth
import Paper08.MainTheorem
import Paper08.ModelSupport
import Paper08.MomentArithmetic
import Paper08.MomentSeries
import Paper08.Moments
import Paper08.MultiMoments
import Paper08.Oracle
import Paper08.OriginalTheorems
import Paper08.Parameters
import Paper08.Perturbation
import Paper08.PrimalArity
import Paper08.PrimitiveAlgorithm
import Paper08.PrimitiveExpressions
import Paper08.PrimitiveInputHeight
import Paper08.PrimitiveIntegralProgram
import Paper08.PrimitiveMomentsQ
import Paper08.PrimitiveParameters
import Paper08.PrimitiveProgram
import Paper08.ProgramPolynomial
import Paper08.Quadrature
import Paper08.QuadratureIntegral
import Paper08.QuadratureOperationCount
import Paper08.QuadratureRealOperationCount
import Paper08.QuadratureSeries
import Paper08.RationalProgram
import Paper08.RationalQuadrature
import Paper08.RationalRecurrenceProgram
import Paper08.SchoolbookArithmetic
import Paper08.SmallDegree
import Paper08.Stability
import Paper08.Support
import Paper08.Surrogate
import Paper08.TupleCount
import Paper08.ZeroFree
import Paper08.ZeroFreeFreeze
import Paper08.ZeroFreeInduction
import Paper08.ZeroFreeLog
import Paper08.ZeroFreeMarginal
import Paper08.ZeroFreeModel
import Paper08.ZeroFreePhase
import Paper08.ZeroFreeRatio
import Paper08.ZeroFreeReplacementBound
import Paper08.ZeroFreeReplacementPath
import Paper08.ZeroFreeTelescoping
/-!
# Paper-facing components and production import closure

Imports the actual integral, multivariate moment/support, analytic logarithm,
executable rational quadrature, recurrence, support enumeration, complete
rational approximation, precision, query-count and representation-size proofs.
`OriginalTheorems.theorem_1_2` gives fixed program constants and one
numerical exponent before all oracle polynomial parameters and all inputs,
with actual accuracy, `(n/ε)^C` oracle calls, logarithmic precision, complete
non-oracle binary/control costs and polynomial accumulated oracle time.
`OriginalTheorems.corollary_1_3_ge_two` and `LowDegreeGuarantee` cover both
primal-degree regimes. `PrimitiveAlgorithm.lemma33` includes the actual
primitive execution cost. `CubeZeroFreeMain.original_closed_disk` proves the
common closed β-disk from the original model promises for every factor
subcollection; the main theorem has no extra common-nonvanishing premise.
Earlier conditional component wrappers are retained for compatibility.

The exact numbered-result scope, including computation-model obligations and
appendix coverage, is recorded in `publication.json`.
-/

noncomputable section

open scoped Real BigOperators

namespace Paper08
namespace Paper

/-! ## Lemma 2.1 / 2.2 — zero-free disk and coefficients -/

/-- `β = 1/(3c√(r-1)q) > 1` under (1.3); a rational `R` with `1 < R < β`
can be chosen (algebraic form of Lemma 2.1). -/
theorem lemma_2_1_beta_gt_one (p : FPTAS.Params) : 1 < FPTAS.beta p :=
  FPTAS.beta_gt_one p

/-- `κ = 2Rq/(2R-1)` and the series identity (2.4). -/
theorem lemma_2_2_kappa (R q h : ℝ) :
    2 * R * h * q / (2 * R - 1) = Coeff.kappa R q * h :=
  Coeff.kappa_eq R q h

/-- Monotonicity step of (2.4): `|Q| ≥ e^{-κ h}`. -/
theorem lemma_2_2_absQ {Q κ h : ℝ} (hQ : 0 < Q) (hlog : Real.log Q ≥ -(κ * h)) :
    Q ≥ Real.exp (-(κ * h)) :=
  Coeff.exp_neg_le_of_log_abs hQ hlog

/-! ## Lemma 2.3 — support extraction -/

/-- The inclusion–exclusion multiplier of (2.8) is `1` on `S = A`. -/
theorem lemma_2_3_multiplier_self {α : Type*} [DecidableEq α] (A : Finset α) :
    Support.ieMultiplier A A = 1 :=
  Support.ie_multiplier_self A

/-- Alternating binomial sum of (2.8)–(2.9). -/
theorem lemma_2_3_binomial (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - k) * (n.choose k : ℤ)))
      = if n = 0 then 1 else 0 :=
  Support.sum_choose_alternating n

/-! ## Lemma 3.1 / 3.2 — total-level quadrature -/

/-- Query count of (3.2). -/
theorem lemma_3_1_query_bound (J t r : ℕ) :
    (2 * t : ℝ) * (Nat.choose (J + t) t) * (2 : ℝ) ^ (r * J)
      ≤ (2 * t : ℝ) * (2 : ℝ) ^ ((r + 1) * J + t) :=
  Quadrature.query_bound J t r

/-- Truncation error of (3.5) given the level choice (3.1). -/
theorem lemma_3_1_truncation {J : ℕ} {B τ : ℝ} {t : ℕ}
    (hB : 0 < B) (hτ : 0 < τ)
    (hJ : Quadrature.satisfies_level_choice J B τ t) :
    B * (2 : ℝ) ^ (-(J : ℝ) / 2) * C0 ^ t ≤ τ / 2 :=
  Quadrature.truncation_error_le hB hτ hJ

/-- Sample-error budget of Lemma 3.2. -/
theorem lemma_3_2_sum_error {J : ℕ} {ζ : ℝ} (hζ : 0 ≤ ζ) :
    ζ + (∑ _ℓ ∈ Finset.range J, (2 * ζ : ℝ)) ≤ 2 * (J + 1 : ℝ) * ζ :=
  Quadrature.sum_increment_error hζ

/-! ## Lemma 4.1 — stability (algebraic input) -/

theorem three_term_accuracy_split {w x y z ε : ℝ}
    (h1 : |w - x| ≤ ε / 3) (h2 : |x - y| ≤ ε / 3) (h3 : |y - z| ≤ ε / 3) :
    |w - z| ≤ ε :=
  Coeff.three_term_split h1 h2 h3

/-! ## Theorem 1.2 and Corollary 1.3 -/

theorem parameter_regime (p : FPTAS.Params) :
    3 * p.c * Real.sqrt (p.r - 1) * p.q ≤ 1 - p.σ :=
  p.regime

theorem theorem_1_2_accurate_exp {Zhat Z ε : ℝ}
    (h : FPTAS.Accurate Zhat Z ε) :
    Real.exp (-ε) ≤ Zhat / Z ∧ Zhat / Z ≤ Real.exp ε :=
  FPTAS.accurate_exp_form h

theorem corollary_1_3_eta_two {Δ : ℝ} (hΔ : 1 ≤ Δ) :
    (11 / 10 : ℝ) * 3 * Δ * Real.sqrt 2 * (Real.log (3 / 2) / (2 * Δ)) < 1 :=
  FPTAS.eta_two_bound hΔ

theorem corollary_1_3_eta_ge_three {η Δ : ℝ} (hη : 3 ≤ η) (hΔ : 1 ≤ Δ) :
    (11 / 10 : ℝ) * 3 * Δ * Real.sqrt η * (Real.log (1 + 1 / η) / (2 * Δ)) < 1 :=
  FPTAS.eta_ge_three_bound hη hΔ

theorem corollary_1_3_log_bound : Real.log (3 / 2) < 5 / 12 :=
  FPTAS.log_three_halves_lt

/-! ## Lemma A.1 and Proposition B.1 -/

theorem lemma_A_1_log_lipschitz {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| :=
  log_abs_sub_le_abs_sub hx hy

theorem prop_B_1_bump {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    Appendix.bump t ≤ 1 :=
  Appendix.bump_le_one ht

end Paper
end Paper08
