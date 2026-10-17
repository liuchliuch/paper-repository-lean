import Paper36.Posterior

/-! Posterior confidence transfer and adaptive row-prefix union bookkeeping.
The concentration input in this file is explicitly a per-row, per-prefix
probability inequality; the method-of-types and Weissman inequalities are not
asserted or introduced as axioms here. -/
namespace Paper36.Confidence
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The finite row-prefix union bound does not require independent rows. -/
theorem prefix_union_bound {Row : Type*} [Fintype Row] (T : ℕ)
    (E : Row → Fin T → Set Ω) {ε : ℝ≥0∞} (hE : ∀ r n, μ (E r n) ≤ ε) :
    μ (⋃ i : Row × Fin T, E i.1 i.2) ≤ (Fintype.card Row : ℝ≥0∞) * T * ε := by
  calc
    μ (⋃ i : Row × Fin T, E i.1 i.2) ≤ ∑ i : Row × Fin T, μ (E i.1 i.2) :=
      measure_iUnion_fintype_le μ _
    _ ≤ ∑ _i : Row × Fin T, ε := Finset.sum_le_sum fun i _ => hE i.1 i.2
    _ = (Fintype.card Row : ℝ≥0∞) * T * ε := by
      simp [Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul, mul_assoc]

/-- A currently revealed row prefix is one of the fixed tape prefixes. This
inclusion is proved from the observed-prefix/tape compatibility, rather than
being an assumed confidence guarantee. Prefix zero is unrestricted. -/
theorem current_prefix_failure_subset {Row History Model : Type*} [Fintype Row]
    {T : ℕ} (history : Ω → History) (latent : Ω → Model)
    (count : Ω → Row → ℕ) (prefixBall : Ω → Row → ℕ → Set Model)
    (currentSet : Set (History × Model))
    (hcount : ∀ ω r, count ω r ≤ T)
    (hzero : ∀ ω r θ, θ ∈ prefixBall ω r 0)
    (hcompat : ∀ ω θ, (history ω, θ) ∈ currentSet ↔
      ∀ r, θ ∈ prefixBall ω r (count ω r)) :
    {ω | (history ω, latent ω) ∉ currentSet} ⊆
      ⋃ i : Row × Fin T, {ω | latent ω ∉ prefixBall ω i.1 (i.2.val + 1)} := by
  classical
  intro ω hω
  have hnot : ¬ ∀ r, latent ω ∈ prefixBall ω r (count ω r) := by
    intro hall
    exact hω ((hcompat ω (latent ω)).2 hall)
  obtain ⟨r, hr⟩ := not_forall.mp hnot
  have hn : 1 ≤ count ω r := by
    by_contra hn
    have hz : count ω r = 0 := by omega
    rw [hz] at hr
    exact hr (hzero ω r (latent ω))
  let n : Fin T := ⟨count ω r - 1, by have := hcount ω r; omega⟩
  refine Set.mem_iUnion.mpr ⟨(r,n), ?_⟩
  change latent ω ∉ prefixBall ω r (n.val + 1)
  simpa only [n, Nat.sub_add_cancel hn] using hr

section Posterior

variable [IsProbabilityMeasure μ]
  {History Model : Type*} [MeasurableSpace History] [MeasurableSpace Model]
  [StandardBorelSpace Model] [Nonempty Model]

/-- Fixed tape-prefix concentration transfers to the current posterior draw,
even when the selected prefix lengths depend on the observations. The only
probability input is the displayed individual-prefix concentration inequality. -/
theorem posterior_prefix_failure_bound {Row : Type*} [Fintype Row] {T : ℕ}
    (history : Ω → History) (latent sampled : Ω → Model)
    (count : Ω → Row → ℕ) (prefixBall : Ω → Row → ℕ → Set Model)
    (currentSet : Set (History × Model)) (hcurrent : MeasurableSet currentSet)
    (hh : AEMeasurable history μ) (hl : AEMeasurable latent μ) (hs : AEMeasurable sampled μ)
    (hposterior : condDistrib latent history μ =ᵐ[μ.map history] condDistrib sampled history μ)
    (hcount : ∀ ω r, count ω r ≤ T)
    (hzero : ∀ ω r θ, θ ∈ prefixBall ω r 0)
    (hcompat : ∀ ω θ, (history ω, θ) ∈ currentSet ↔
      ∀ r, θ ∈ prefixBall ω r (count ω r))
    {ε : ℝ≥0∞}
    (hprefix : ∀ r (n : Fin T), μ {ω | latent ω ∉ prefixBall ω r (n.val + 1)} ≤ ε) :
    μ {ω | (history ω, latent ω) ∉ currentSet} ≤ (Fintype.card Row : ℝ≥0∞) * T * ε ∧
    μ {ω | (history ω, sampled ω) ∉ currentSet} ≤ (Fintype.card Row : ℝ≥0∞) * T * ε := by
  have hunion := prefix_union_bound T
    (fun r n => {ω | latent ω ∉ prefixBall ω r (n.val+1)}) hprefix
  have htrue := (measure_mono (current_prefix_failure_subset history latent count prefixBall
    currentSet hcount hzero hcompat)).trans hunion
  refine ⟨htrue, ?_⟩
  rw [Paper36.Posterior.posterior_failure_probability hh hl hs hposterior hcurrent]
  exact htrue

/-- The joint true-prefix and episodewise sampled-kernel failure bound. Its
`1 + #episodes` factor is the bookkeeping used in Appendix C's expectation
and fixed-horizon certificate proofs. -/
theorem posterior_joint_failure_bound {Episode I : Type*} [Fintype Episode] [Fintype I]
    (history : Episode → Ω → History) (latent : Ω → Model) (sampled : Episode → Ω → Model)
    (currentSet : Episode → Set (History × Model)) (prefixFailure : I → Set Ω)
    (hcurrent : ∀ k, MeasurableSet (currentSet k))
    (hh : ∀ k, AEMeasurable (history k) μ) (hl : AEMeasurable latent μ)
    (hs : ∀ k, AEMeasurable (sampled k) μ)
    (hposterior : ∀ k, condDistrib latent (history k) μ =ᵐ[μ.map (history k)]
      condDistrib (sampled k) (history k) μ)
    (hcompat : ∀ k, {ω | (history k ω, latent ω) ∉ currentSet k} ⊆ ⋃ i, prefixFailure i)
    {ε : ℝ≥0∞} (hprefix : ∀ i, μ (prefixFailure i) ≤ ε) :
    μ ((⋃ i, prefixFailure i) ∪ ⋃ k, {ω | (history k ω, sampled k ω) ∉ currentSet k}) ≤
      (1 + (Fintype.card Episode : ℝ≥0∞)) * (Fintype.card I : ℝ≥0∞) * ε := by
  have hpref : μ (⋃ i, prefixFailure i) ≤ (Fintype.card I : ℝ≥0∞) * ε := by
    calc
      μ (⋃ i, prefixFailure i) ≤ ∑ i, μ (prefixFailure i) := measure_iUnion_fintype_le μ _
      _ ≤ ∑ _i : I, ε := Finset.sum_le_sum fun i _ => hprefix i
      _ = (Fintype.card I : ℝ≥0∞) * ε := by simp [nsmul_eq_mul]
  have hsample : ∀ k, μ {ω | (history k ω, sampled k ω) ∉ currentSet k} ≤
      (Fintype.card I : ℝ≥0∞) * ε := by
    intro k
    rw [Paper36.Posterior.posterior_failure_probability (hh k) hl (hs k) (hposterior k) (hcurrent k)]
    exact (measure_mono (hcompat k)).trans hpref
  calc
    μ ((⋃ i, prefixFailure i) ∪ ⋃ k, {ω | (history k ω, sampled k ω) ∉ currentSet k}) ≤
        μ (⋃ i, prefixFailure i) + μ (⋃ k, {ω | (history k ω, sampled k ω) ∉ currentSet k}) :=
      measure_union_le _ _
    _ ≤ (Fintype.card I : ℝ≥0∞) * ε +
        ∑ k, μ {ω | (history k ω, sampled k ω) ∉ currentSet k} :=
      add_le_add hpref (measure_iUnion_fintype_le μ _)
    _ ≤ (Fintype.card I : ℝ≥0∞) * ε +
        ∑ _k : Episode, (Fintype.card I : ℝ≥0∞) * ε :=
      add_le_add_left (Finset.sum_le_sum fun k _ => hsample k) _
    _ = (1 + (Fintype.card Episode : ℝ≥0∞)) * (Fintype.card I : ℝ≥0∞) * ε := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end Posterior
end Paper36.Confidence
