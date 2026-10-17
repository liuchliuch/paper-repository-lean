import PUT.QueryPrior
import PUT.Progress
import PUT.DirichletMeasure

/-!
# Operational adversary lower bound with genuine continuous priors

This module proves the progress-to-query part of paper 24, Section 4, for
actual `Circuit.priorEvolution` runs and an actual bounded operator between
their vector-valued L² spaces. The good-event probability is a real measure,
not a finite surrogate. Neither the final progress drop nor the query lower
bound is assumed.

The optional `NinefoldMajorityCertificate` is an explicit external-theorem
interface for nine independent repetitions and majority vote. It contains
only pointwise output-error implications at `9 * Q` actual calls, never an
adversary inequality. Standard circuit purification is described in John
Watrous, "Quantum Computational Complexity", Section III.3 (pp. 9--10),
and repetition/error reduction in Section IV.2, Proposition 3 (pp. 12--13):
https://cs.uwaterloo.ca/~watrous/Papers/QuantumComputationalComplexity.pdf .
The finite union-bound constant `2^9 * (1/100)^5` is checked below. No
external theorem is installed as a Lean axiom, and the normalized-circuit
operational lower bound uses no such external input.
-/
noncomputable section

namespace PUT.TestingLowerBound

open MeasureTheory PUT.QueryModel
open scoped ENNReal InnerProductSpace

variable {X₀ X₁ H : Type*} [MeasurableSpace X₀] [MeasurableSpace X₁]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {μ₀ : Measure X₀} {μ₁ : Measure X₁}
  [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]

/-- The actual Born probability in the vector-valued L² evolution. -/
def meanRejection (C : Circuit H) (U : PointwiseUnitary μ₁ H) (T : ℕ) : ℝ :=
  (C.measurement.lift (μ := μ₁)).rejectionProbability ((C.priorEvolution U).state T)

theorem meanRejection_eq_integral (C : Circuit H) (U : PointwiseUnitary μ₁ H) (T : ℕ) :
    meanRejection C U T = ∫ x, C.rejectProbability (U.unitary x) T ∂μ₁ :=
  C.prior_rejection_probability U T

/-- The actual per-input Born probabilities are integrable under the prior.
This is derived from the L² run, not added as a regularity assumption. -/
theorem rejection_integrable (C : Circuit H) (U : PointwiseUnitary μ₁ H) (T : ℕ) :
    Integrable (fun x => C.rejectProbability (U.unitary x) T) μ₁ := by
  let f := (C.measurement.lift (μ := μ₁)).reject ((C.priorEvolution U).state T)
  have hf : Integrable (fun x => ‖f x‖ ^ 2) μ₁ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  apply hf.congr
  filter_upwards [C.measurement.reject.coeFn_compLpL ((C.priorEvolution U).state T),
    C.priorEvolution_state_ae U T] with x hP hs
  change ‖(C.measurement.reject.compLpL 2 μ₁ ((C.priorEvolution U).state T)) x‖ ^ 2 = _
  rw [hP, hs]
  rfl

theorem meanRejection_bounds (C : Circuit H) (U : PointwiseUnitary μ₁ H) (T : ℕ) :
    0 ≤ meanRejection C U T ∧ meanRejection C U T ≤ 1 :=
  (C.measurement.lift (μ := μ₁)).probability_bounds _
    ((C.priorEvolution U).state_norm T)

/-- Correctness on the null promise implies the corresponding actual
average rejection probability is at most the error. -/
theorem meanRejection_le_of_success (C : Circuit H) (U : PointwiseUnitary μ₁ H)
    (T : ℕ) (δ : ℝ)
    (hsuccess : ∀ᵐ x ∂μ₁, C.rejectProbability (U.unitary x) T ≤ δ) :
    meanRejection C U T ≤ δ := by
  rw [meanRejection_eq_integral]
  have h := integral_mono_ae (rejection_integrable C U T) (integrable_const δ) hsuccess
  simpa using h

/-- Correctness is required only on the good event. Arbitrary behavior
outside the testing promise is handled using Born probability nonnegativity. -/
theorem meanRejection_ge_of_good_event (C : Circuit H) (U : PointwiseUnitary μ₁ H)
    (T : ℕ) (s : Set X₁) (hs : MeasurableSet s) (q₀ δ : ℝ)
    (hδ : δ ≤ 1) (hmass : q₀ ≤ μ₁.real s)
    (hsuccess : ∀ᵐ x ∂μ₁, x ∈ s → 1 - δ ≤ C.rejectProbability (U.unitary x) T) :
    q₀ * (1 - δ) ≤ meanRejection C U T := by
  have hpoint : ∀ᵐ x ∂μ₁,
      s.indicator (fun _ => 1 - δ) x ≤ C.rejectProbability (U.unitary x) T := by
    filter_upwards [hsuccess] with x hx
    by_cases hxs : x ∈ s
    · simpa [hxs] using hx hxs
    · simpa [hxs] using (C.rejectProbability_bounds (U.unitary x) T).1
  have hi := integral_mono_ae ((integrable_const (1 - δ)).indicator hs)
    (rejection_integrable C U T) hpoint
  rw [integral_indicator_const (1 - δ) hs] at hi
  change μ₁.real s * (1 - δ) ≤ _ at hi
  rw [meanRejection_eq_integral]
  exact (mul_le_mul_of_nonneg_right hmass (sub_nonneg.mpr hδ)).trans hi

/-- The actual operator assumptions used by the source. `on_constant` is
the vector-valued form of `Γ 1 = A 1` for `Γ ⊗ I`: each constant physical
vector has unchanged physical component and constant latent component.
The remaining fields are genuine commutation and query-difference statements
on the actual L² spaces. No progress trajectory is supplied. -/
structure AdversaryConditions (C : Circuit H)
    (U₀ : PointwiseUnitary μ₀ H) (U₁ : PointwiseUnitary μ₁ H)
    (Γ : Lp H 2 μ₁ →L[ℂ] Lp H 2 μ₀) (A B : ℝ) : Prop where
  norm_le : ‖Γ‖ ≤ A
  on_constant : ∀ ψ : H, Γ (Lp.const 2 μ₁ ψ) = (A : ℂ) • Lp.const 2 μ₀ ψ
  free_commutation : ∀ t y, Γ ((C.priorEvolution U₁).free t y) =
    (C.priorEvolution U₀).free t (Γ y)
  measurement_commutation : ∀ y,
    (C.measurement.lift (μ := μ₀)).reject (Γ y) =
      Γ ((C.measurement.lift (μ := μ₁)).reject y)
  query_difference : ∀ t,
    ‖Γ.comp ((C.priorEvolution U₁).query t : Lp H 2 μ₁ →L[ℂ] Lp H 2 μ₁) -
      ((C.priorEvolution U₀).query t : Lp H 2 μ₀ →L[ℂ] Lp H 2 μ₀).comp Γ‖ ≤ B

/-- `W₀ = A` follows from the constant-vector eigen-equation and the
normalized circuit input. It is not a progress assumption. -/
theorem initial_progress (C : Circuit H)
    (U₀ : PointwiseUnitary μ₀ H) (U₁ : PointwiseUnitary μ₁ H)
    (Γ : Lp H 2 μ₁ →L[ℂ] Lp H 2 μ₀) {A B : ℝ}
    (hΓ : AdversaryConditions C U₀ U₁ Γ A B) :
    runProgress Γ (C.priorEvolution U₀) (C.priorEvolution U₁) 0 = A := by
  have hinit : Γ ((C.priorEvolution U₁).state 0) =
      (A : ℂ) • (C.priorEvolution U₀).state 0 :=
    hΓ.on_constant (C.free 0 C.initial)
  have hn := (C.priorEvolution U₀).state_norm 0
  change (inner ℂ ((C.priorEvolution U₀).state 0)
    (Γ ((C.priorEvolution U₁).state 0))).re = A
  rw [hinit, inner_smul_right, inner_self_eq_norm_sq_to_K, hn]
  simp

/-- Average separation follows from actual success and actual good-event
mass. This is the operational content of paper (30), prior to applying the
adversary argument. -/
theorem average_separation (C : Circuit H)
    (U₀ : PointwiseUnitary μ₀ H) (U₁ : PointwiseUnitary μ₁ H)
    (T : ℕ) (s : Set X₁) (hs : MeasurableSet s) {q₀ δ : ℝ}
    (hq₀ : 0 < q₀) (hq₀_one : q₀ ≤ 1) (_hδ : 0 ≤ δ) (hδ_small : δ ≤ (q₀ / 8) ^ 2)
    (hmass : q₀ ≤ μ₁.real s)
    (hnull : ∀ᵐ x ∂μ₀, C.rejectProbability (U₀.unitary x) T ≤ δ)
    (hgood : ∀ᵐ x ∂μ₁, x ∈ s → 1 - δ ≤ C.rejectProbability (U₁.unitary x) T) :
    meanRejection C U₀ T ≤ δ ∧
      q₀ * (1 - δ) ≤ meanRejection C U₁ T ∧
      q₀ / 2 ≤ meanRejection C U₁ T := by
  have hsquare : (q₀ / 8) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hhalf : δ ≤ 1 / 2 := by nlinarith
  have h₁ := meanRejection_ge_of_good_event C U₁ T s hs q₀ δ (by linarith) hmass hgood
  exact ⟨meanRejection_le_of_success C U₀ T δ hnull, h₁, by nlinarith⟩

/-- Operational lower bound for a normalized circuit with `T` actual
queries, on two genuine continuous priors. All progress and average
separation inequalities are derived from the displayed structural inputs. -/
theorem prior_query_lower (C : Circuit H)
    (U₀ : PointwiseUnitary μ₀ H) (U₁ : PointwiseUnitary μ₁ H)
    (Γ : Lp H 2 μ₁ →L[ℂ] Lp H 2 μ₀) (A B q₀ δ : ℝ) (T : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hq₀ : 0 < q₀) (hq₀_one : q₀ ≤ 1)
    (hδ : 0 ≤ δ) (hδ_small : δ ≤ (q₀ / 8) ^ 2)
    (hΓ : AdversaryConditions C U₀ U₁ Γ A B)
    (s : Set X₁) (hs : MeasurableSet s) (hmass : q₀ ≤ μ₁.real s)
    (hnull : ∀ᵐ x ∂μ₀, C.rejectProbability (U₀.unitary x) T ≤ δ)
    (hgood : ∀ᵐ x ∂μ₁, x ∈ s → 1 - δ ≤ C.rejectProbability (U₁.unitary x) T) :
    q₀ * A / (8 * B) ≤ (T : ℝ) := by
  have hsep := average_separation C U₀ U₁ T s hs hq₀ hq₀_one hδ hδ_small hmass hnull hgood
  let E₀ := C.priorEvolution U₀
  let E₁ := C.priorEvolution U₁
  have hr₀ := meanRejection_bounds C U₀ T
  have hr₁ := meanRejection_bounds C U₁ T
  have hfrac := PUT.separation_fractional q₀ (meanRejection C U₀ T)
    (meanRejection C U₁ T) δ A hA hq₀ (by linarith)
    hr₀.1 hsep.1 hδ hδ_small hsep.2.2 hr₁.2
  have hfinal : |runProgress Γ E₀ E₁ T| ≤ A * (1 - q₀ / 8) :=
    (runProgress_final Γ E₀ E₁ (C.measurement.lift (μ := μ₀))
      (C.measurement.lift (μ := μ₁)) hΓ.measurement_commutation hΓ.norm_le T).trans hfrac
  exact PUT.progress_query_lower A B q₀ (runProgress Γ E₀ E₁) T hA hB hq₀
    (initial_progress C U₀ U₁ Γ hΓ)
    (fun t _ => runProgress_step Γ E₀ E₁ hΓ.free_commutation hΓ.query_difference t) hfinal

/-- Ninefold query overhead gives exactly the denominator `72 B`. The
premises concern the actual amplified circuit at `9Q` actual calls. -/
theorem prior_query_lower_ninefold (C : Circuit H)
    (U₀ : PointwiseUnitary μ₀ H) (U₁ : PointwiseUnitary μ₁ H)
    (Γ : Lp H 2 μ₁ →L[ℂ] Lp H 2 μ₀) (A B q₀ δ : ℝ) (Q : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hq₀ : 0 < q₀) (hq₀_one : q₀ ≤ 1)
    (hδ : 0 ≤ δ) (hδ_small : δ ≤ (q₀ / 8) ^ 2)
    (hΓ : AdversaryConditions C U₀ U₁ Γ A B)
    (s : Set X₁) (hs : MeasurableSet s) (hmass : q₀ ≤ μ₁.real s)
    (hnull : ∀ᵐ x ∂μ₀, C.rejectProbability (U₀.unitary x) (9 * Q) ≤ δ)
    (hgood : ∀ᵐ x ∂μ₁, x ∈ s → 1 - δ ≤ C.rejectProbability (U₁.unitary x) (9 * Q)) :
    q₀ * A / (72 * B) ≤ (Q : ℝ) := by
  have h := prior_query_lower C U₀ U₁ Γ A B q₀ δ (9 * Q)
    hA hB hq₀ hq₀_one hδ hδ_small hΓ s hs hmass hnull hgood
  have hmul := (div_le_iff₀ (by positivity : 0 < 8 * B)).mp h
  apply (div_le_iff₀ (by positivity : 0 < 72 * B)).mpr
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hmul
  nlinarith

/-- An event at TV distance at least `2ε` is contained in the source's
strict alternative event. This transfers an actual continuous mass bound. -/
theorem strict_tv_promise_mass {d : ℕ} (p : X₁ → Fin d → ℝ) {ε q₀ : ℝ}
    (hε : 0 < ε)
    (hmass : q₀ ≤ μ₁.real {x | 2 * ε ≤ PUT.tvDist (p x) (PUT.uniform d)}) :
    q₀ ≤ μ₁.real {x | ε < PUT.tvDist (p x) (PUT.uniform d)} := by
  apply hmass.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  exact lt_of_lt_of_le (by linarith : ε < 2 * ε) hx

/-- The operational ninefold lower bound with the actual strict TV
promise. A mass bound at `TV ≥ 2ε`, such as the continuous Dirichlet Lemma 2,
is transferred to that promise inside the proof. -/
theorem prior_query_lower_ninefold_tv {d : ℕ} (p : X₁ → Fin d → ℝ)
    (hp : Measurable p) {ε : ℝ} (hε : 0 < ε)
    (C : Circuit H) (U₀ : PointwiseUnitary μ₀ H) (U₁ : PointwiseUnitary μ₁ H)
    (Γ : Lp H 2 μ₁ →L[ℂ] Lp H 2 μ₀) (A B q₀ δ : ℝ) (Q : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hq₀ : 0 < q₀) (hq₀_one : q₀ ≤ 1)
    (hδ : 0 ≤ δ) (hδ_small : δ ≤ (q₀ / 8) ^ 2)
    (hΓ : AdversaryConditions C U₀ U₁ Γ A B)
    (hmass : q₀ ≤ μ₁.real {x | 2 * ε ≤ PUT.tvDist (p x) (PUT.uniform d)})
    (hnull : ∀ᵐ x ∂μ₀, C.rejectProbability (U₀.unitary x) (9 * Q) ≤ δ)
    (hgood : ∀ᵐ x ∂μ₁, ε < PUT.tvDist (p x) (PUT.uniform d) →
      1 - δ ≤ C.rejectProbability (U₁.unitary x) (9 * Q)) :
    q₀ * A / (72 * B) ≤ (Q : ℝ) := by
  have hs : MeasurableSet {x | ε < PUT.tvDist (p x) (PUT.uniform d)} :=
    measurableSet_lt measurable_const ((PUT.measurable_tvDist_uniform d).comp hp)
  exact prior_query_lower_ninefold C U₀ U₁ Γ A B q₀ δ Q hA hB hq₀ hq₀_one
    hδ hδ_small hΓ _ hs (strict_tv_promise_mass p hε hmass) hnull hgood

/-- The elementary bound on the error of a ninefold majority, obtained by
union-bounding the at most `2^9` failure subsets of size at least five. -/
def ninefoldError : ℝ := 2 ^ 9 * (1 / 100 : ℝ) ^ 5

theorem ninefoldError_nonneg : 0 ≤ ninefoldError := by norm_num [ninefoldError]

theorem paper_ninefold_error : ninefoldError < (((1 / 144 : ℝ) / 8) ^ 2) := by
  norm_num [ninefoldError]

/-- Exact external-theorem interface for error amplification. Both sides
are actual circuits and actual input unitaries. An implementation theorem
for nine independent copies plus coherent majority supplies this certificate.
This declaration asserts no existence and adds no axiom. -/
structure NinefoldMajorityCertificate
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (original : Circuit K)
    (original₀ : X₀ → K ≃ₗᵢ[ℂ] K) (original₁ : X₁ → K ≃ₗᵢ[ℂ] K)
    (amplified : Circuit H) (U₀ : PointwiseUnitary μ₀ H) (U₁ : PointwiseUnitary μ₁ H)
    (Q : ℕ) : Prop where
  null_error : ∀ x, original.rejectProbability (original₀ x) Q ≤ 1 / 100 →
    amplified.rejectProbability (U₀.unitary x) (9 * Q) ≤ ninefoldError
  alternative_error : ∀ x, 99 / 100 ≤ original.rejectProbability (original₁ x) Q →
    1 - ninefoldError ≤ amplified.rejectProbability (U₁.unitary x) (9 * Q)

/-- The actual original algorithm inherits the operational lower bound
from an explicit ninefold-normalization/amplification certificate. All
adversary and TV-prior deductions are proved internally. -/
theorem lower_of_ninefold_certificate
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (original : Circuit K)
    (original₀ : X₀ → K ≃ₗᵢ[ℂ] K) (original₁ : X₁ → K ≃ₗᵢ[ℂ] K)
    (C : Circuit H) (U₀ : PointwiseUnitary μ₀ H) (U₁ : PointwiseUnitary μ₁ H)
    (Γ : Lp H 2 μ₁ →L[ℂ] Lp H 2 μ₀) (A B q₀ : ℝ) (Q : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hq₀ : 0 < q₀) (hq₀_one : q₀ ≤ 1)
    (herror : ninefoldError ≤ (q₀ / 8) ^ 2)
    (hΓ : AdversaryConditions C U₀ U₁ Γ A B)
    (hamp : NinefoldMajorityCertificate original original₀ original₁ C U₀ U₁ Q)
    (s : Set X₁) (hs : MeasurableSet s) (hmass : q₀ ≤ μ₁.real s)
    (hnull : ∀ᵐ x ∂μ₀, original.rejectProbability (original₀ x) Q ≤ 1 / 100)
    (hgood : ∀ᵐ x ∂μ₁, x ∈ s → 99 / 100 ≤ original.rejectProbability (original₁ x) Q) :
    q₀ * A / (72 * B) ≤ (Q : ℝ) := by
  apply prior_query_lower_ninefold C U₀ U₁ Γ A B q₀ ninefoldError Q
    hA hB hq₀ hq₀_one ninefoldError_nonneg herror hΓ s hs hmass
  · filter_upwards [hnull] with x hx
    exact hamp.null_error x hx
  · filter_upwards [hgood] with x hx hxs
    exact hamp.alternative_error x (hx hxs)

end PUT.TestingLowerBound
