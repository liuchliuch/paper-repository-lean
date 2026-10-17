import Paper36.Trajectories
import Paper36.Divergence
import Paper36.Confidence
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Exact external categorical concentration inputs and their transfer through
an arbitrary latent-model prior. No posterior confidence conclusion is assumed.
The external statements are the iid finite-sample inequalities cited as [12]
(method of types) and [34] (Weissman et al.) in Appendix C of P36. -/
namespace Paper36.RowTapes
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
noncomputable section

variable {S : Type*} [Fintype S]

/-- The actual iid categorical law on n successive row-tape observations. -/
def iidLaw (P : Law S) (n : ℕ) : Law (Fin n → S) where
  mass word := ∏ i, P.mass (word i)
  nonneg word := Finset.prod_nonneg fun i _ => P.nonneg (word i)
  total := by rw [← Fintype.sum_pow]; simp [P.total]

/-- The empirical law includes zero counts exactly and has total mass one. -/
def empirical [DecidableEq S] {n : ℕ} (hn : 0 < n) (word : Fin n → S) : Law S where
  mass s := (∑ i, if word i = s then (1 : ℝ) else 0) / n
  nonneg s := div_nonneg (Finset.sum_nonneg fun i _ => by split <;> norm_num) (Nat.cast_nonneg _)
  total := by
    classical
    rw [← Finset.sum_div, Finset.sum_comm]
    simp [ne_of_gt hn]

section Measurability
variable {M : Type*} [MeasurableSpace M]

/-- Finite KL is Borel, including its infinite support-mismatch branch. -/
lemma measurable_kl_of_masses (P Q : M → Law S)
    (hP : ∀ s, Measurable (fun m => (P m).mass s))
    (hQ : ∀ s, Measurable (fun m => (Q m).mass s)) :
    Measurable (fun m => kl (P m) (Q m)) := by
  classical
  have hs : MeasurableSet {m | SupportDominated (P m) (Q m)} := by
    simp only [SupportDominated, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro s
    have h1 : MeasurableSet {m | (0 : ℝ) < (P m).mass s} :=
      measurableSet_lt measurable_const (hP s)
    have h2 : MeasurableSet {m | (0 : ℝ) < (Q m).mass s} :=
      measurableSet_lt measurable_const (hQ s)
    simpa only [imp_iff_not_or] using h1.compl.union h2
  apply Measurable.ite hs
  · apply Measurable.ennreal_ofReal
    unfold klReal
    exact Finset.measurable_sum _ fun s _ => (hP s).mul (((hP s).div (hQ s)).log)
  · exact measurable_const

lemma measurable_tv_of_masses (P Q : M → Law S)
    (hP : ∀ s, Measurable (fun m => (P m).mass s))
    (hQ : ∀ s, Measurable (fun m => (Q m).mass s)) :
    Measurable (fun m => tv (P m) (Q m)) := by
  unfold tv
  have hs := Finset.measurable_sum Finset.univ (fun s _ => ((hP s).sub (hQ s)).norm)
  simpa only [Real.norm_eq_abs] using hs.div_const (2 : ℝ)

end Measurability

section ConcentrationInputs
variable [MeasurableSpace S] [DiscreteMeasurableSpace S] [DecidableEq S]

/-- Precisely the two published iid inequalities imported by Appendix C.

* `methodTypes`: Cover--Thomas [12], Elements of Information Theory, 2nd ed.
  (2006), method-of-types bound; no positivity restriction is imposed on P.
* `weissman`: Weissman et al. [34], HP Labs HPL-2003-97R1 (2003), finite
  categorical L1 deviation inequality, in the paper's TV normalization.

This is an explicit external theorem input, not an axiom or a confidence-event
assumption. Its hypotheses and all quantifiers are retained verbatim in scale. -/
structure ExternalCategoricalConcentration : Prop where
  methodTypes : ∀ (P : Law S) (n : ℕ) (hn : 0 < n) (Λ : ℝ), 0 ≤ Λ →
    lawMeasure (iidLaw P n)
      {word | ENNReal.ofReal (Λ / n) < kl (empirical hn word) P} ≤
        ENNReal.ofReal (((n+1 : ℕ) : ℝ) ^ Fintype.card S * Real.exp (-Λ))
  weissman : ∀ (P : Law S) (n : ℕ) (hn : 0 < n) (L : ℝ), 0 ≤ L →
    lawMeasure (iidLaw P n)
      {word | Real.sqrt (L / (2 * n)) < tv (empirical hn word) P} ≤
        ENNReal.ofReal (((2 : ℝ) ^ Fintype.card S - 2) * Real.exp (-L))

variable {M : Type*} [MeasurableSpace M]

/-- The measurable iid-row sampling kernel, constructed from its categorical rows. -/
def iidKernel (row : M → Law S)
    (hrow : ∀ s, Measurable (fun m => (row m).mass s)) (n : ℕ) :
    ProbabilityTheory.Kernel M (Fin n → S) :=
  lawKernel (fun m => iidLaw (row m) n)
    (fun word => by
      change Measurable (fun m => ∏ i, (row m).mass (word i))
      exact Finset.measurable_prod _ fun i _ => hrow (word i))

instance iidKernel_markov (row : M → Law S)
    (hrow : ∀ s, Measurable (fun m => (row m).mass s)) (n : ℕ) :
    IsMarkovKernel (iidKernel row hrow n) := lawKernel_markov _ _

variable {Ω W : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

/-- Integrating a conditional sampling bound over any latent prior preserves
that bound. This derives the arbitrary-prior step; no prior factorization is used. -/
theorem prior_mixture_failure_le (latent : Ω → M) (sample : Ω → W)
    (hl : Measurable latent) (hs : AEMeasurable sample μ)
    (κ : ProbabilityTheory.Kernel M W) [IsMarkovKernel κ]
    (hcond : condDistrib sample latent μ =ᵐ[μ.map latent] κ)
    (E : Set (M × W)) (hE : MeasurableSet E) {ε : ℝ≥0∞}
    (hbound : ∀ m, κ m (Prod.mk m ⁻¹' E) ≤ ε) :
    μ {ω | (latent ω, sample ω) ∈ E} ≤ ε := by
  have hmap : μ.map (fun ω => (latent ω, sample ω)) = (μ.map latent) ⊗ₘ κ :=
    (condDistrib_ae_eq_iff_measure_eq_compProd latent hs κ).mp hcond
  haveI : IsProbabilityMeasure (μ.map latent) := Measure.isProbabilityMeasure_map hl.aemeasurable
  calc
    μ {ω | (latent ω, sample ω) ∈ E} =
        (μ.map (fun ω => (latent ω, sample ω))) E :=
      (Measure.map_apply_of_aemeasurable (hl.aemeasurable.prodMk hs) hE).symm
    _ = ((μ.map latent) ⊗ₘ κ) E := by rw [hmap]
    _ = ∫⁻ m, κ m (Prod.mk m ⁻¹' E) ∂μ.map latent := Measure.compProd_apply hE
    _ ≤ ∫⁻ _m, ε ∂μ.map latent := lintegral_mono hbound
    _ = ε := by simp

/-- The method-of-types row-prefix bound under an arbitrary latent-model prior. -/
theorem method_types_arbitrary_prior [Nonempty S]
    (external : ExternalCategoricalConcentration (S := S))
    (row : M → Law S) (hrow : ∀ s, Measurable (fun m => (row m).mass s))
    (latent : Ω → M) (hl : Measurable latent) (n : ℕ) (hn : 0 < n)
    (sample : Ω → Fin n → S) (hs : AEMeasurable sample μ)
    (hcond : condDistrib sample latent μ =ᵐ[μ.map latent] iidKernel row hrow n)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    μ {ω | ENNReal.ofReal (Λ / n) < kl (empirical hn (sample ω)) (row (latent ω))} ≤
      ENNReal.ofReal (((n+1 : ℕ) : ℝ) ^ Fintype.card S * Real.exp (-Λ)) := by
  let E : Set (M × (Fin n → S)) :=
    {x | ENNReal.ofReal (Λ / n) < kl (empirical hn x.2) (row x.1)}
  have hE : MeasurableSet E := by
    apply measurableSet_lt measurable_const
    apply measurable_from_prod_countable_left
    intro word
    exact measurable_kl_of_masses (fun _ => empirical hn word) row
      (fun _ => measurable_const) hrow
  exact prior_mixture_failure_le latent sample hl hs (iidKernel row hrow n) hcond E hE
    (fun m => external.methodTypes (row m) n hn Λ hΛ)

/-- The Weissman row-prefix bound under an arbitrary latent-model prior. -/
theorem weissman_arbitrary_prior [Nonempty S]
    (external : ExternalCategoricalConcentration (S := S))
    (row : M → Law S) (hrow : ∀ s, Measurable (fun m => (row m).mass s))
    (latent : Ω → M) (hl : Measurable latent) (n : ℕ) (hn : 0 < n)
    (sample : Ω → Fin n → S) (hs : AEMeasurable sample μ)
    (hcond : condDistrib sample latent μ =ᵐ[μ.map latent] iidKernel row hrow n)
    (L : ℝ) (hL : 0 ≤ L) :
    μ {ω | Real.sqrt (L / (2 * n)) < tv (empirical hn (sample ω)) (row (latent ω))} ≤
      ENNReal.ofReal (((2 : ℝ) ^ Fintype.card S - 2) * Real.exp (-L)) := by
  let E : Set (M × (Fin n → S)) :=
    {x | Real.sqrt (L / (2 * n)) < tv (empirical hn x.2) (row x.1)}
  have hE : MeasurableSet E := by
    apply measurableSet_lt measurable_const
    apply measurable_from_prod_countable_left
    intro word
    exact measurable_tv_of_masses (fun _ => empirical hn word) row
      (fun _ => measurable_const) hrow
  exact prior_mixture_failure_le latent sample hl hs (iidKernel row hrow n) hcond E hE
    (fun m => external.weissman (row m) n hn L hL)

end ConcentrationInputs

/-- The paper's KL exponent, parametrized by the reciprocal failure budget M. -/
def klThreshold (dimension T : ℕ) (M : ℝ) : ℝ :=
  dimension * Real.log (T+1) + Real.log M

theorem klThreshold_nonneg (dimension T : ℕ) {M : ℝ} (hM : 1 ≤ M) :
    0 ≤ klThreshold dimension T M := by
  unfold klThreshold
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T; linarith)))
    (Real.log_nonneg hM)

/-- The exact scalar budget calculation used after the method-of-types inequality. -/
theorem method_types_budget (dimension T n : ℕ) (hn : n ≤ T) {M : ℝ} (hM : 0 < M) :
    ((n+1 : ℕ) : ℝ) ^ dimension * Real.exp (-klThreshold dimension T M) ≤ 1 / M := by
  have hT : 0 < (T : ℝ) + 1 := by positivity
  have hpow : 0 < ((T : ℝ)+1)^dimension := pow_pos hT _
  have heq : klThreshold dimension T M = Real.log ((((T : ℝ)+1)^dimension)*M) := by
    rw [Real.log_mul (ne_of_gt hpow) (ne_of_gt hM), Real.log_pow]
    simp only [klThreshold, Nat.cast_add, Nat.cast_one]
  rw [heq, Real.exp_neg, Real.exp_log (mul_pos hpow hM)]
  have hnp : ((n+1 : ℕ) : ℝ)^dimension ≤ ((T : ℝ)+1)^dimension := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right hn 1
  calc
    ((n+1 : ℕ) : ℝ)^dimension * ((((T : ℝ)+1)^dimension)*M)⁻¹ ≤
        (((T : ℝ)+1)^dimension) * ((((T : ℝ)+1)^dimension)*M)⁻¹ :=
      mul_le_mul_of_nonneg_right hnp (inv_nonneg.mpr (mul_pos hpow hM).le)
    _ = 1 / M := by field_simp

/-- The paper's TV exponent, with the same reciprocal failure budget. -/
def tvThreshold (dimension : ℕ) (M : ℝ) : ℝ :=
  dimension * Real.log 2 + Real.log M

theorem tvThreshold_nonneg (dimension : ℕ) {M : ℝ} (hM : 1 ≤ M) :
    0 ≤ tvThreshold dimension M := by
  unfold tvThreshold
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
    (Real.log_nonneg hM)

theorem weissman_budget (dimension : ℕ) {M : ℝ} (hM : 0 < M) :
    ((2 : ℝ)^dimension - 2) * Real.exp (-tvThreshold dimension M) ≤ 1 / M := by
  have hp : 0 < (2 : ℝ)^dimension := pow_pos (by norm_num) _
  have heq : tvThreshold dimension M = Real.log (((2 : ℝ)^dimension)*M) := by
    rw [Real.log_mul (ne_of_gt hp) (ne_of_gt hM), Real.log_pow]
    rfl
  rw [heq, Real.exp_neg, Real.exp_log (mul_pos hp hM)]
  calc
    ((2 : ℝ)^dimension-2) * (((2 : ℝ)^dimension)*M)⁻¹ ≤
        ((2 : ℝ)^dimension) * (((2 : ℝ)^dimension)*M)⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr (mul_pos hp hM).le)
    _ = 1 / M := by field_simp

section PosteriorConfidence
variable [MeasurableSpace S] [DiscreteMeasurableSpace S] [DecidableEq S] [Nonempty S]
  {Row M Hist Ω : Type*} [Fintype Row] [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Hist] {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Reverse-KL confidence ball at a fixed prefix of a pre-generated row tape. -/
def tapeKLBall (row : M → Row → Law S) (tape : Ω → Row → ℕ → S) (Λ : ℝ)
    (ω : Ω) (r : Row) (n : ℕ) : Set M := by
  classical
  exact if hn : n = 0 then Set.univ else
    {m | kl (empirical (Nat.pos_of_ne_zero hn) (fun i : Fin n => tape ω r i.val)) (row m r) ≤
      ENNReal.ofReal (Λ / n)}

/-- The current confidence set uses only the observed history. -/
def currentKLSet (row : M → Row → Law S) (N : Hist → Row → ℕ)
    (observed : Hist → Row → Law S) (Λ : ℝ) : Set (Hist × M) :=
  {x | ∀ r, N x.1 r = 0 ∨ kl (observed x.1 r) (row x.2 r) ≤ ENNReal.ofReal (Λ / N x.1 r)}

lemma currentKLSet_measurable (row : M → Row → Law S) (N : Hist → Row → ℕ)
    (observed : Hist → Row → Law S) (Λ : ℝ)
    (hrow : ∀ r s, Measurable (fun m => (row m r).mass s))
    (hN : ∀ r, Measurable (fun h => N h r))
    (ho : ∀ r s, Measurable (fun h => (observed h r).mass s)) :
    MeasurableSet (currentKLSet row N observed Λ) := by
  unfold currentKLSet
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro r
  have hz : MeasurableSet {x : Hist × M | N x.1 r = 0} :=
    ((hN r).comp measurable_fst) (measurableSet_singleton (0 : ℕ))
  have hk := measurable_kl_of_masses (fun x : Hist × M => observed x.1 r)
    (fun x => row x.2 r) (fun s => (ho r s).comp measurable_fst)
    (fun s => (hrow r s).comp measurable_snd)
  have hNr : Measurable (fun x : Hist × M => (N x.1 r : ℝ)) :=
    (Measurable.of_discrete : Measurable (fun n : ℕ => (n : ℝ))).comp ((hN r).comp measurable_fst)
  have hr : Measurable (fun x : Hist × M => ENNReal.ofReal (Λ / N x.1 r)) :=
    (measurable_const.div hNr).ennreal_ofReal
  exact hz.union (measurableSet_le hk hr)

/-- At the actually revealed prefix, the empirical tape and observed empirical
law agree. This proves the current-set/tape compatibility used in the adaptive
union bound, for both the latent and sampled model. -/
lemma currentKLSet_compatibility (row : M → Row → Law S) (N : Hist → Row → ℕ)
    (observed : Hist → Row → Law S) (history : Ω → Hist) (tape : Ω → Row → ℕ → S)
    (Λ : ℝ)
    (hobs : ∀ ω r (hn : 0 < N (history ω) r), observed (history ω) r =
      empirical hn (fun i : Fin (N (history ω) r) => tape ω r i.val)) :
    ∀ ω m, (history ω, m) ∈ currentKLSet row N observed Λ ↔
      ∀ r, m ∈ tapeKLBall row tape Λ ω r (N (history ω) r) := by
  classical
  intro ω m
  change (∀ r, N (history ω) r = 0 ∨ _) ↔ _
  apply forall_congr'
  intro r
  by_cases hn : N (history ω) r = 0
  · simp [tapeKLBall, hn]
  · have hpos := Nat.pos_of_ne_zero hn
    simp only [tapeKLBall, hn, ↓reduceDIte, Set.mem_setOf_eq, false_or]
    rw [hobs ω r hpos]

/-- The individual fixed-prefix KL failure bound, with the paper's logarithmic
threshold and the exact 1/M allocation, integrated over an arbitrary prior. -/
theorem tape_kl_prefix_failure_bound
    (external : ExternalCategoricalConcentration (S := S))
    (row : M → Row → Law S) (hrow : ∀ r s, Measurable (fun m => (row m r).mass s))
    (latent : Ω → M) (hl : Measurable latent) (tape : Ω → Row → ℕ → S)
    (ht : ∀ r n, Measurable (fun ω => tape ω r n))
    (hcond : ∀ r n, condDistrib (fun ω => (fun i : Fin n => tape ω r i.val)) latent μ =ᵐ[μ.map latent]
      iidKernel (fun m => row m r) (hrow r) n)
    (T : ℕ) {budget : ℝ} (hb : 1 ≤ budget) (r : Row) (n : Fin T) :
    μ {ω | latent ω ∉ tapeKLBall row tape (klThreshold (Fintype.card S) T budget)
      ω r (n.val+1)} ≤ ENNReal.ofReal (1 / budget) := by
  have hsample : Measurable (fun ω => (fun i : Fin (n.val+1) => tape ω r i.val)) :=
    measurable_pi_lambda _ (fun i => ht r i.val)
  have hraw := method_types_arbitrary_prior external (fun m => row m r) (hrow r) latent hl
    (n.val+1) (by omega) _ hsample.aemeasurable (hcond r (n.val+1))
    (klThreshold (Fintype.card S) T budget) (klThreshold_nonneg _ _ hb)
  have hbudget := method_types_budget (Fintype.card S) T (n.val+1)
    (by have := n.isLt; omega) (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hb)
  have hstep := hraw.trans (ENNReal.ofReal_le_ofReal hbudget)
  simpa only [tapeKLBall, Nat.succ_ne_zero, ↓reduceDIte, Set.mem_setOf_eq, not_le] using hstep

/-- Confidence-set failure probabilities under any prior and any adaptive
history-measurable prefix choice. All probability work after the external iid
inequality is proved here. -/
theorem current_kl_failure_bound
    (external : ExternalCategoricalConcentration (S := S))
    (row : M → Row → Law S) (hrow : ∀ r s, Measurable (fun m => (row m r).mass s))
    (N : Hist → Row → ℕ) (hN : ∀ r, Measurable (fun h => N h r))
    (observed : Hist → Row → Law S) (ho : ∀ r s, Measurable (fun h => (observed h r).mass s))
    (history : Ω → Hist) (hh : AEMeasurable history μ)
    (latent sampled : Ω → M) (hl : Measurable latent) (hs : AEMeasurable sampled μ)
    (hpost : condDistrib latent history μ =ᵐ[μ.map history] condDistrib sampled history μ)
    (tape : Ω → Row → ℕ → S) (ht : ∀ r n, Measurable (fun ω => tape ω r n))
    (hcond : ∀ r n, condDistrib (fun ω => (fun i : Fin n => tape ω r i.val)) latent μ =ᵐ[μ.map latent]
      iidKernel (fun m => row m r) (hrow r) n)
    (hobs : ∀ ω r (hn : 0 < N (history ω) r), observed (history ω) r =
      empirical hn (fun i : Fin (N (history ω) r) => tape ω r i.val))
    (T : ℕ) (hcount : ∀ ω r, N (history ω) r ≤ T) {budget : ℝ} (hb : 1 ≤ budget) :
    μ {ω | (history ω, latent ω) ∉ currentKLSet row N observed (klThreshold (Fintype.card S) T budget)} ≤
      (Fintype.card Row : ℝ≥0∞) * T * ENNReal.ofReal (1 / budget) ∧
    μ {ω | (history ω, sampled ω) ∉ currentKLSet row N observed (klThreshold (Fintype.card S) T budget)} ≤
      (Fintype.card Row : ℝ≥0∞) * T * ENNReal.ofReal (1 / budget) := by
  apply Paper36.Confidence.posterior_prefix_failure_bound history latent sampled
    (fun ω => N (history ω)) (tapeKLBall row tape (klThreshold (Fintype.card S) T budget))
    (currentKLSet row N observed (klThreshold (Fintype.card S) T budget))
    (currentKLSet_measurable row N observed _ hrow hN ho) hh hl.aemeasurable hs hpost hcount
  · intro ω r m
    simp [tapeKLBall]
  · exact currentKLSet_compatibility row N observed history tape _ hobs
  · exact tape_kl_prefix_failure_bound external row hrow latent hl tape ht hcond T hb

/-- Both actual KL-ball memberships give the source's C.5 Hellinger-squared
radius on each nonzero-count row. -/
theorem current_hellinger_radius (row : M → Row → Law S) (N : Hist → Row → ℕ)
    (observed : Hist → Row → Law S) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (history : Ω → Hist) (latent sampled : Ω → M) (ω : Ω)
    (htrue : (history ω, latent ω) ∈ currentKLSet row N observed Λ)
    (hsample : (history ω, sampled ω) ∈ currentKLSet row N observed Λ)
    (r : Row) (hn : 0 < N (history ω) r) :
    hellingerSq (row (latent ω) r) (row (sampled ω) r) ≤ 2 * Λ / N (history ω) r := by
  have htr := (htrue r).resolve_left (Nat.ne_of_gt hn)
  have hsa := (hsample r).resolve_left (Nat.ne_of_gt hn)
  have heps : 0 ≤ Λ / N (history ω) r := div_nonneg hΛ (Nat.cast_nonneg _)
  have hh := hellinger_le_of_two_kl_same (row (latent ω) r) (row (sampled ω) r)
    (observed (history ω) r) heps htr hsa
  have hsqrt := Real.sq_sqrt (show 0 ≤ 2 * (Λ / N (history ω) r) by positivity)
  have hnonneg := hellinger_nonneg (row (latent ω) r) (row (sampled ω) r)
  have hsq := hellinger_sq (row (latent ω) r) (row (sampled ω) r)
  have hsqle := pow_le_pow_left₀ hnonneg hh 2
  rw [hsq, hsqrt] at hsqle
  simpa only [mul_div_assoc] using hsqle

/-- The probability of any true tape-prefix failure, before selecting adaptive counts. -/
theorem kl_true_prefix_failure_bound
    (external : ExternalCategoricalConcentration (S := S))
    (row : M → Row → Law S) (hrow : ∀ r s, Measurable (fun m => (row m r).mass s))
    (latent : Ω → M) (hl : Measurable latent) (tape : Ω → Row → ℕ → S)
    (ht : ∀ r n, Measurable (fun ω => tape ω r n))
    (hcond : ∀ r n, condDistrib (fun ω => (fun i : Fin n => tape ω r i.val)) latent μ =ᵐ[μ.map latent]
      iidKernel (fun m => row m r) (hrow r) n)
    (T : ℕ) {budget : ℝ} (hb : 1 ≤ budget) :
    μ (⋃ i : Row × Fin T, {ω | latent ω ∉ tapeKLBall row tape
      (klThreshold (Fintype.card S) T budget) ω i.1 (i.2.val+1)}) ≤
        (Fintype.card Row : ℝ≥0∞) * T * ENNReal.ofReal (1 / budget) :=
  Paper36.Confidence.prefix_union_bound T _
    (tape_kl_prefix_failure_bound external row hrow latent hl tape ht hcond T hb)

/-- The true-prefix and all posterior-current KL confidence failures at a fixed
finite number of episodes. This is the confidence part of Theorem 5.6. -/
theorem all_episodes_kl_failure_bound {Episode : Type*} [Fintype Episode]
    (external : ExternalCategoricalConcentration (S := S))
    (row : M → Row → Law S) (hrow : ∀ r s, Measurable (fun m => (row m r).mass s))
    (N : Hist → Row → ℕ) (hN : ∀ r, Measurable (fun h => N h r))
    (observed : Hist → Row → Law S) (ho : ∀ r s, Measurable (fun h => (observed h r).mass s))
    (history : Episode → Ω → Hist) (hh : ∀ k, AEMeasurable (history k) μ)
    (latent : Ω → M) (sampled : Episode → Ω → M)
    (hl : Measurable latent) (hs : ∀ k, AEMeasurable (sampled k) μ)
    (hpost : ∀ k, condDistrib latent (history k) μ =ᵐ[μ.map (history k)]
      condDistrib (sampled k) (history k) μ)
    (tape : Ω → Row → ℕ → S) (ht : ∀ r n, Measurable (fun ω => tape ω r n))
    (hcond : ∀ r n, condDistrib (fun ω => (fun i : Fin n => tape ω r i.val)) latent μ =ᵐ[μ.map latent]
      iidKernel (fun m => row m r) (hrow r) n)
    (hobs : ∀ k ω r (hn : 0 < N (history k ω) r), observed (history k ω) r =
      empirical hn (fun i : Fin (N (history k ω) r) => tape ω r i.val))
    (T : ℕ) (hcount : ∀ k ω r, N (history k ω) r ≤ T) {budget : ℝ} (hb : 1 ≤ budget) :
    μ ((⋃ i : Row × Fin T, {ω | latent ω ∉ tapeKLBall row tape
      (klThreshold (Fintype.card S) T budget) ω i.1 (i.2.val+1)}) ∪
      ⋃ k, {ω | (history k ω, sampled k ω) ∉
        currentKLSet row N observed (klThreshold (Fintype.card S) T budget)}) ≤
      (1 + (Fintype.card Episode : ℝ≥0∞)) * (Fintype.card Row : ℝ≥0∞) * T *
        ENNReal.ofReal (1 / budget) := by
  have hbound := Paper36.Confidence.posterior_joint_failure_bound history latent sampled
    (fun _ => currentKLSet row N observed (klThreshold (Fintype.card S) T budget))
    (fun i : Row × Fin T => {ω | latent ω ∉ tapeKLBall row tape
      (klThreshold (Fintype.card S) T budget) ω i.1 (i.2.val+1)})
    (fun _ => currentKLSet_measurable row N observed _ hrow hN ho) hh hl.aemeasurable hs hpost
    (fun k => Paper36.Confidence.current_prefix_failure_subset (history k) latent
      (fun ω => N (history k ω)) (tapeKLBall row tape (klThreshold (Fintype.card S) T budget))
      (currentKLSet row N observed (klThreshold (Fintype.card S) T budget)) (hcount k)
      (by intro ω r m; simp [tapeKLBall])
      (currentKLSet_compatibility row N observed (history k) tape _ (hobs k)))
    (fun i => tape_kl_prefix_failure_bound external row hrow latent hl tape ht hcond T hb i.1 i.2)
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, mul_assoc] using hbound

/-- A global true-prefix good event guarantees current latent-ball membership,
for every adaptively chosen count up to T. -/
theorem true_current_kl_of_prefix_good
    (row : M → Row → Law S) (N : Hist → Row → ℕ) (observed : Hist → Row → Law S)
    (history : Ω → Hist) (latent : Ω → M) (tape : Ω → Row → ℕ → S)
    (Λ : ℝ) (T : ℕ) (hcount : ∀ ω r, N (history ω) r ≤ T)
    (hobs : ∀ ω r (hn : 0 < N (history ω) r), observed (history ω) r =
      empirical hn (fun i : Fin (N (history ω) r) => tape ω r i.val))
    {ω : Ω} (hgood : ω ∉ ⋃ i : Row × Fin T,
      {ω | latent ω ∉ tapeKLBall row tape Λ ω i.1 (i.2.val+1)}) :
    (history ω, latent ω) ∈ currentKLSet row N observed Λ := by
  by_contra hbad
  exact hgood (Paper36.Confidence.current_prefix_failure_subset history latent
    (fun ω => N (history ω)) (tapeKLBall row tape Λ) (currentKLSet row N observed Λ)
    hcount (by intro ω r m; simp [tapeKLBall])
    (currentKLSet_compatibility row N observed history tape Λ hobs) hbad)

/-- Total-variation tape ball, with the precise Weissman radius. -/
def tapeTVBall (row : M → Row → Law S) (tape : Ω → Row → ℕ → S) (L : ℝ)
    (ω : Ω) (r : Row) (n : ℕ) : Set M := by
  classical
  exact if hn : n = 0 then Set.univ else
    {m | tv (empirical (Nat.pos_of_ne_zero hn) (fun i : Fin n => tape ω r i.val)) (row m r) ≤
      Real.sqrt (L / (2 * n))}

def currentTVSet (row : M → Row → Law S) (N : Hist → Row → ℕ)
    (observed : Hist → Row → Law S) (L : ℝ) : Set (Hist × M) :=
  {x | ∀ r, N x.1 r = 0 ∨ tv (observed x.1 r) (row x.2 r) ≤ Real.sqrt (L / (2 * N x.1 r))}

lemma currentTVSet_measurable (row : M → Row → Law S) (N : Hist → Row → ℕ)
    (observed : Hist → Row → Law S) (L : ℝ)
    (hrow : ∀ r s, Measurable (fun m => (row m r).mass s))
    (hN : ∀ r, Measurable (fun h => N h r))
    (ho : ∀ r s, Measurable (fun h => (observed h r).mass s)) :
    MeasurableSet (currentTVSet row N observed L) := by
  unfold currentTVSet
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro r
  have hz : MeasurableSet {x : Hist × M | N x.1 r = 0} :=
    ((hN r).comp measurable_fst) (measurableSet_singleton (0 : ℕ))
  have hk := measurable_tv_of_masses (fun x : Hist × M => observed x.1 r)
    (fun x => row x.2 r) (fun s => (ho r s).comp measurable_fst)
    (fun s => (hrow r s).comp measurable_snd)
  have hNr : Measurable (fun x : Hist × M => (N x.1 r : ℝ)) :=
    (Measurable.of_discrete : Measurable (fun n : ℕ => (n : ℝ))).comp ((hN r).comp measurable_fst)
  have hr : Measurable (fun x : Hist × M => Real.sqrt (L / (2 * N x.1 r))) :=
    Real.continuous_sqrt.measurable.comp (measurable_const.div (measurable_const.mul hNr))
  exact hz.union (measurableSet_le hk hr)

lemma currentTVSet_compatibility (row : M → Row → Law S) (N : Hist → Row → ℕ)
    (observed : Hist → Row → Law S) (history : Ω → Hist) (tape : Ω → Row → ℕ → S)
    (L : ℝ)
    (hobs : ∀ ω r (hn : 0 < N (history ω) r), observed (history ω) r =
      empirical hn (fun i : Fin (N (history ω) r) => tape ω r i.val)) :
    ∀ ω m, (history ω, m) ∈ currentTVSet row N observed L ↔
      ∀ r, m ∈ tapeTVBall row tape L ω r (N (history ω) r) := by
  classical
  intro ω m
  change (∀ r, N (history ω) r = 0 ∨ _) ↔ _
  apply forall_congr'
  intro r
  by_cases hn : N (history ω) r = 0
  · simp [tapeTVBall, hn]
  · have hpos := Nat.pos_of_ne_zero hn
    simp only [tapeTVBall, hn, ↓reduceDIte, Set.mem_setOf_eq, false_or]
    rw [hobs ω r hpos]

theorem tape_tv_prefix_failure_bound
    (external : ExternalCategoricalConcentration (S := S))
    (row : M → Row → Law S) (hrow : ∀ r s, Measurable (fun m => (row m r).mass s))
    (latent : Ω → M) (hl : Measurable latent) (tape : Ω → Row → ℕ → S)
    (ht : ∀ r n, Measurable (fun ω => tape ω r n))
    (hcond : ∀ r n, condDistrib (fun ω => (fun i : Fin n => tape ω r i.val)) latent μ =ᵐ[μ.map latent]
      iidKernel (fun m => row m r) (hrow r) n)
    (T : ℕ) {budget : ℝ} (hb : 1 ≤ budget) (r : Row) (n : Fin T) :
    μ {ω | latent ω ∉ tapeTVBall row tape (tvThreshold (Fintype.card S) budget)
      ω r (n.val+1)} ≤ ENNReal.ofReal (1 / budget) := by
  have hsample : Measurable (fun ω => (fun i : Fin (n.val+1) => tape ω r i.val)) :=
    measurable_pi_lambda _ (fun i => ht r i.val)
  have hraw := weissman_arbitrary_prior external (fun m => row m r) (hrow r) latent hl
    (n.val+1) (by omega) _ hsample.aemeasurable (hcond r (n.val+1))
    (tvThreshold (Fintype.card S) budget) (tvThreshold_nonneg _ hb)
  have hbudget := weissman_budget (Fintype.card S) (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hb)
  have hstep := hraw.trans (ENNReal.ofReal_le_ofReal hbudget)
  simpa only [tapeTVBall, Nat.succ_ne_zero, ↓reduceDIte, Set.mem_setOf_eq, not_le] using hstep

theorem current_tv_failure_bound
    (external : ExternalCategoricalConcentration (S := S))
    (row : M → Row → Law S) (hrow : ∀ r s, Measurable (fun m => (row m r).mass s))
    (N : Hist → Row → ℕ) (hN : ∀ r, Measurable (fun h => N h r))
    (observed : Hist → Row → Law S) (ho : ∀ r s, Measurable (fun h => (observed h r).mass s))
    (history : Ω → Hist) (hh : AEMeasurable history μ)
    (latent sampled : Ω → M) (hl : Measurable latent) (hs : AEMeasurable sampled μ)
    (hpost : condDistrib latent history μ =ᵐ[μ.map history] condDistrib sampled history μ)
    (tape : Ω → Row → ℕ → S) (ht : ∀ r n, Measurable (fun ω => tape ω r n))
    (hcond : ∀ r n, condDistrib (fun ω => (fun i : Fin n => tape ω r i.val)) latent μ =ᵐ[μ.map latent]
      iidKernel (fun m => row m r) (hrow r) n)
    (hobs : ∀ ω r (hn : 0 < N (history ω) r), observed (history ω) r =
      empirical hn (fun i : Fin (N (history ω) r) => tape ω r i.val))
    (T : ℕ) (hcount : ∀ ω r, N (history ω) r ≤ T) {budget : ℝ} (hb : 1 ≤ budget) :
    μ {ω | (history ω, latent ω) ∉ currentTVSet row N observed (tvThreshold (Fintype.card S) budget)} ≤
      (Fintype.card Row : ℝ≥0∞) * T * ENNReal.ofReal (1 / budget) ∧
    μ {ω | (history ω, sampled ω) ∉ currentTVSet row N observed (tvThreshold (Fintype.card S) budget)} ≤
      (Fintype.card Row : ℝ≥0∞) * T * ENNReal.ofReal (1 / budget) := by
  apply Paper36.Confidence.posterior_prefix_failure_bound history latent sampled
    (fun ω => N (history ω)) (tapeTVBall row tape (tvThreshold (Fintype.card S) budget))
    (currentTVSet row N observed (tvThreshold (Fintype.card S) budget))
    (currentTVSet_measurable row N observed _ hrow hN ho) hh hl.aemeasurable hs hpost hcount
  · intro ω r m
    simp [tapeTVBall]
  · exact currentTVSet_compatibility row N observed history tape _ hobs
  · exact tape_tv_prefix_failure_bound external row hrow latent hl tape ht hcond T hb

lemma tv_triangle (P Q R : Law S) : tv P R ≤ tv P Q + tv Q R := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ => abs_sub_le (P.mass s) (Q.mass s) (R.mass s))
  rw [Finset.sum_add_distrib] at hh
  unfold tv
  linarith

lemma tv_symm (P Q : Law S) : tv P Q = tv Q P := by
  unfold tv
  simp only [abs_sub_comm]

/-- Two observed TV balls give exactly the confidence radius C.14 used for
high-count rows in the reward simulation. -/
theorem current_tv_radius (row : M → Row → Law S) (N : Hist → Row → ℕ)
    (observed : Hist → Row → Law S) {L : ℝ} (hL : 0 ≤ L)
    (history : Ω → Hist) (latent sampled : Ω → M) (ω : Ω)
    (htrue : (history ω, latent ω) ∈ currentTVSet row N observed L)
    (hsample : (history ω, sampled ω) ∈ currentTVSet row N observed L)
    (r : Row) (hn : 0 < N (history ω) r) :
    tv (row (latent ω) r) (row (sampled ω) r) ≤ Real.sqrt (2 * L / N (history ω) r) := by
  have htr := (htrue r).resolve_left (Nat.ne_of_gt hn)
  have hsa := (hsample r).resolve_left (Nat.ne_of_gt hn)
  rw [tv_symm] at htr
  have hh := (tv_triangle (row (latent ω) r) (observed (history ω) r) (row (sampled ω) r)).trans
    (add_le_add htr hsa)
  have heq : Real.sqrt (L / (2 * N (history ω) r)) + Real.sqrt (L / (2 * N (history ω) r)) =
      Real.sqrt (2 * L / N (history ω) r) := by
    have h1 := Real.sq_sqrt (show 0 ≤ L / (2 * N (history ω) r) by positivity)
    have h2 := Real.sq_sqrt (show 0 ≤ 2 * L / N (history ω) r by positivity)
    have hdiv : 4 * (L / (2 * N (history ω) r)) = 2 * L / N (history ω) r := by ring
    nlinarith [Real.sqrt_nonneg (L / (2 * N (history ω) r)), Real.sqrt_nonneg (2 * L / N (history ω) r)]
  exact hh.trans_eq heq

end PosteriorConfidence


end
end Paper36.RowTapes
