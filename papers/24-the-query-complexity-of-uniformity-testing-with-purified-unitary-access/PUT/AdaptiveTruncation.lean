import PUT.AdaptiveModel

/-!
# Query truncation on promised inputs

The source's query bound is required only on promised oracles. We measure
that bound by the Born mass of histories that would perform query `Q+1`.
Truncating those histories gives a syntactically bounded finite protocol;
its output agrees with the original whenever that overrun mass is zero.
No new external input occurs in the truncation or lower-bound transfer.
-/
noncomputable section
namespace PUT.AdaptiveModel
open PUT.QueryModel PUT.SourceTargets

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Total Born mass of histories about to make a `(Q+1)`st query. Branch
vectors retain their history weights, and zero-mass histories cost nothing. -/
def Protocol.overrunProbability (U : H ≃ₗᵢ[ℂ] H) : Protocol H → ℕ → H → ℝ
  | .halt _, _, _ => 0
  | .free V next, Q, ψ => next.overrunProbability U Q (V ψ)
  | .query _ _, 0, ψ => ‖ψ‖ ^ 2
  | .query direction next, Q+1, ψ =>
      next.overrunProbability U Q (queryUnitary U direction ψ)
  | .measure P acceptBranch rejectBranch, Q, ψ =>
      acceptBranch.overrunProbability U Q (P.accept ψ) +
        rejectBranch.overrunProbability U Q (P.reject ψ)

/-- Stop and accept immediately before a query would exceed the budget.
All operations before that event, including intermediate measurements, remain. -/
def Protocol.truncateQueries : Protocol H → ℕ → Protocol H
  | .halt reject, _ => .halt reject
  | .free V next, Q => .free V (next.truncateQueries Q)
  | .query _ _, 0 => .halt false
  | .query direction next, Q+1 => .query direction (next.truncateQueries Q)
  | .measure P acceptBranch rejectBranch, Q =>
      .measure P (acceptBranch.truncateQueries Q) (rejectBranch.truncateQueries Q)

/-- The overrun quantity is an actual probability mass. -/
theorem Protocol.overrunProbability_bounds (P : Protocol H) (U : H ≃ₗᵢ[ℂ] H)
    (Q : ℕ) (ψ : H) :
    0 ≤ P.overrunProbability U Q ψ ∧ P.overrunProbability U Q ψ ≤ ‖ψ‖ ^ 2 := by
  induction P generalizing Q ψ with
  | halt reject => simp [Protocol.overrunProbability, sq_nonneg]
  | free V next ih => simpa [Protocol.overrunProbability] using ih Q (V ψ)
  | query direction next ih =>
    cases Q with
    | zero => exact ⟨sq_nonneg _, le_rfl⟩
    | succ Q => simpa [Protocol.overrunProbability] using ih Q (queryUnitary U direction ψ)
  | measure P acceptBranch rejectBranch ihA ihR =>
    obtain ⟨ha0,ha1⟩ := ihA Q (P.accept ψ)
    obtain ⟨hr0,hr1⟩ := ihR Q (P.reject ψ)
    exact ⟨add_nonneg ha0 hr0, (add_le_add ha1 hr1).trans_eq (P.pythagoras ψ).symm⟩

/-- The truncated tree has at most `Q` actual queries on every branch,
including branches arising only on inputs outside the promise. -/
theorem Protocol.truncateQueries_depth (P : Protocol H) (Q : ℕ) :
    (P.truncateQueries Q).worstQueries ≤ Q := by
  induction P generalizing Q with
  | halt reject => simp [Protocol.truncateQueries, Protocol.worstQueries]
  | free V next ih => exact ih Q
  | query direction next ih =>
    cases Q with
    | zero => exact le_rfl
    | succ Q => exact Nat.succ_le_succ (ih Q)
  | measure P acceptBranch rejectBranch ihA ihR =>
    exact max_le (ihA Q) (ihR Q)

/-- Changing the output only after exceeding the query budget changes its
probability by at most the total Born mass of those histories. -/
theorem Protocol.truncateQueries_error (P : Protocol H) (U : H ≃ₗᵢ[ℂ] H)
    (Q : ℕ) (ψ : H) :
    |(P.truncateQueries Q).outputReject U ψ - P.outputReject U ψ| ≤
      P.overrunProbability U Q ψ := by
  induction P generalizing Q ψ with
  | halt reject => simp [Protocol.truncateQueries, Protocol.outputReject, Protocol.overrunProbability]
  | free V next ih => exact ih Q (V ψ)
  | query direction next ih =>
    cases Q with
    | zero =>
      have h := (Protocol.query direction next).outputReject_bounds U ψ
      change |0 - (Protocol.query direction next).outputReject U ψ| ≤ ‖ψ‖ ^ 2
      rw [zero_sub, abs_neg, abs_of_nonneg h.1]
      exact h.2
    | succ Q => exact ih Q (queryUnitary U direction ψ)
  | measure P acceptBranch rejectBranch ihA ihR =>
    let a := (acceptBranch.truncateQueries Q).outputReject U (P.accept ψ)
    let b := (rejectBranch.truncateQueries Q).outputReject U (P.reject ψ)
    let c := acceptBranch.outputReject U (P.accept ψ)
    let d := rejectBranch.outputReject U (P.reject ψ)
    change |(a+b)-(c+d)| ≤
      acceptBranch.overrunProbability U Q (P.accept ψ) +
        rejectBranch.overrunProbability U Q (P.reject ψ)
    calc
      |(a+b)-(c+d)| = |(a-c)+(b-d)| := by congr 1; ring
      _ ≤ |a-c| + |b-d| := abs_add_le _ _
      _ ≤ _ := add_le_add (ihA Q (P.accept ψ)) (ihR Q (P.reject ψ))

/-- Almost-sure query boundedness is sufficient for exact output preservation. -/
theorem Protocol.truncateQueries_eq_of_zero (P : Protocol H) (U : H ≃ₗᵢ[ℂ] H)
    (Q : ℕ) (ψ : H) (h : P.overrunProbability U Q ψ = 0) :
    (P.truncateQueries Q).outputReject U ψ = P.outputReject U ψ := by
  have he := P.truncateQueries_error U Q ψ
  rw [h] at he
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm he (abs_nonneg _)))

/-- Overrun mass of an actual normalized tester on a specified full oracle. -/
def AdaptiveTesterFamily.overrunProbability {d : ℕ} (A : AdaptiveTesterFamily d)
    {M : ℕ} (U : PreparationOracle d M) (Q : ℕ) : ℝ :=
  (A.protocol M).overrunProbability (A.oracle U) Q (A.initial M)

/-- The source bound applies only on the uniform/nonuniform promise. No
behavior or query bound is imposed on valid oracles outside that promise. -/
def AdaptiveTesterFamily.PromiseBoundedTests {d : ℕ} (A : AdaptiveTesterFamily d)
    (ε : ℝ) (Q : ℕ) : Prop :=
  A.Tests ε ∧ ∀ (M : ℕ) (U : PreparationOracle d M),
    ((∀ i, U.probability i = (1 : ℝ)/d) ∨ ε < tvDist U.probability (uniform d)) →
      A.overrunProbability U Q = 0

/-- A concrete, globally bounded tester obtained by truncating the protocol. -/
def AdaptiveTesterFamily.truncate {d : ℕ} (A : AdaptiveTesterFamily d) (Q : ℕ) :
    AdaptiveTesterFamily d where
  workspace := A.workspace
  initial := A.initial
  initial_norm := A.initial_norm
  protocol := fun M => (A.protocol M).truncateQueries Q

theorem AdaptiveTesterFamily.truncate_bounded {d : ℕ} (A : AdaptiveTesterFamily d) (Q : ℕ) :
    (A.truncate Q).BoundedQueries Q := fun M => (A.protocol M).truncateQueries_depth Q

theorem AdaptiveTesterFamily.truncate_probability_eq {d : ℕ} (A : AdaptiveTesterFamily d)
    (Q : ℕ) {M : ℕ} (U : PreparationOracle d M) (h : A.overrunProbability U Q = 0) :
    (A.truncate Q).rejectProbability U = A.rejectProbability U :=
  (A.protocol M).truncateQueries_eq_of_zero (A.oracle U) Q (A.initial M) h

/-- The promise-only worst-case bound really yields a globally bounded
successful tester, by a proved truncation rather than an external assumption. -/
theorem AdaptiveTesterFamily.truncate_boundedTests {d : ℕ} (A : AdaptiveTesterFamily d)
    {ε : ℝ} {Q : ℕ} (h : A.PromiseBoundedTests ε Q) :
    (A.truncate Q).BoundedTests ε Q := by
  refine ⟨?_, A.truncate_bounded Q⟩
  intro M U
  constructor
  · intro hu
    rw [A.truncate_probability_eq Q U (h.2 M U (Or.inl hu))]
    exact (h.1 M U).1 hu
  · intro hfar
    rw [A.truncate_probability_eq Q U (h.2 M U (Or.inr hfar))]
    exact (h.1 M U).2 hfar

theorem AdaptiveTesterFamily.exists_bounded_of_promise {d : ℕ} (A : AdaptiveTesterFamily d)
    {ε : ℝ} {Q : ℕ} (h : A.PromiseBoundedTests ε Q) :
    ∃ B : AdaptiveTesterFamily d, B.BoundedTests ε Q ∧
      ∀ (M : ℕ) (U : PreparationOracle d M),
        ((∀ i, U.probability i = (1 : ℝ)/d) ∨ ε < tvDist U.probability (uniform d)) →
          B.rejectProbability U = A.rejectProbability U := by
  refine ⟨A.truncate Q, A.truncate_boundedTests h, ?_⟩
  intro M U hpromise
  exact A.truncate_probability_eq Q U (h.2 M U hpromise)

/-- Source Theorem 1 with the actual promise-only worst-case query convention. -/
def PromiseAdaptiveTheorem1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (ε : ℝ),
    2 ≤ d → 0 < ε → ε < 1/2 →
    ∀ (A : AdaptiveTesterFamily d) (Q : ℕ), A.PromiseBoundedTests ε Q →
      theorem1Bound c d ε ≤ (Q : ℝ)

/-- Truncation costs no additional queries. Consequently the constant is the
same `c/2` from adaptive normalization, with no new external theorem input. -/
theorem promise_adaptive_lower_of_normalized (hNormal : PUT.External.AdaptiveNormalizationLaw)
    (hMain : SourceTargets.Theorem1) : PromiseAdaptiveTheorem1 := by
  obtain ⟨c,hc,hAdaptive⟩ := adaptive_lower_of_normalized hNormal hMain
  refine ⟨c,hc,?_⟩
  intro d ε hd hε hεhalf A Q hA
  exact hAdaptive d ε hd hε hεhalf (A.truncate Q) Q (A.truncate_boundedTests hA)

end PUT.AdaptiveModel
