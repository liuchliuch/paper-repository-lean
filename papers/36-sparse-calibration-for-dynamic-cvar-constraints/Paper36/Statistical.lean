import Paper36.RowTapes
import Paper36.StatisticalCounts
import Paper36.HybridCharging
import Paper36.Measurability
import Paper36.Target
import Paper36.Bounds

/-! Posterior simulation on an arbitrary probability space. The experiment
contains only the source's posterior/dynamics and observed row-tape identities;
the source's simulation, confidence, count and expectation conclusions are derived. -/
namespace Paper36.Statistical
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.RowTapes Paper36.StatisticalCounts
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ} {s₀ : S}

/-- A row-tape realization of the source's posterior-sampling experiment.
Only raw sampling laws and observed-prefix compatibility are fields. -/
structure PosteriorSystem (E : EpisodeSystem μ Info S A T s₀) where
  decode : Model → Simulation.Kernel S A
  decode_meas : ∀ s a t, Measurable (fun m => (decode m s a).mass t)
  latent : Ω → Model
  latent_meas : Measurable latent
  latent_match : ∀ ω, E.latent ω = decode (latent ω)
  sampled : ℕ → Ω → Model
  sampled_meas : ∀ k, Measurable (sampled k)
  history : ℕ → Ω → Hist
  history_meas : ∀ k, Measurable (history k)
  posterior : ∀ k, condDistrib latent (history k) μ =ᵐ[μ.map (history k)]
    condDistrib (sampled k) (history k) μ
  count : Hist → S × A → ℕ
  count_meas : ∀ row, Measurable (fun h => count h row)
  count_match : ∀ k ω row, count (history k ω) row = E.count k (E.info k ω) row
  observed : Hist → S × A → Law S
  observed_meas : ∀ row t, Measurable (fun h => (observed h row).mass t)
  tape : Ω → S × A → ℕ → S
  tape_meas : ∀ row n, Measurable (fun ω => tape ω row n)
  tape_model : ∀ row n,
    condDistrib (fun ω => (fun i : Fin n => tape ω row i.val)) latent μ =ᵐ[μ.map latent]
      iidKernel (fun m => decode m row.1 row.2) (fun t => decode_meas row.1 row.2 t) n
  observed_prefix : ∀ k ω row (hn : 0 < count (history k ω) row), observed (history k ω) row =
    empirical hn (fun i : Fin (count (history k ω) row) => tape ω row i.val)

namespace PosteriorSystem
variable {E : EpisodeSystem μ Info S A T s₀} (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

def row : Model → S × A → Law S := fun m r => P.decode m r.1 r.2

def policies (_P : PosteriorSystem (Model := Model) (Hist := Hist) E) (ω : Ω) : ℕ → Policy S A := fun k => E.policy k (E.info k ω)
def counts (_P : PosteriorSystem (Model := Model) (Hist := Hist) E) (ω : Ω) : ℕ → S × A → ℕ := fun k => E.count k (E.info k ω)
def sampledKernels (ω : Ω) : ℕ → Simulation.Kernel S A := fun k => P.decode (P.sampled k ω)

def goodKL (Λ : ℝ) (k : ℕ) : Set Ω :=
  {ω | (P.history k ω, P.latent ω) ∈ currentKLSet P.row P.count P.observed Λ ∧
    (P.history k ω, P.sampled k ω) ∈ currentKLSet P.row P.count P.observed Λ}

def goodTV (L : ℝ) (k : ℕ) : Set Ω :=
  {ω | (P.history k ω, P.latent ω) ∈ currentTVSet P.row P.count P.observed L ∧
    (P.history k ω, P.sampled k ω) ∈ currentTVSet P.row P.count P.observed L}

lemma goodKL_measurable (Λ : ℝ) (k : ℕ) : MeasurableSet (P.goodKL Λ k) := by
  have hC := currentKLSet_measurable P.row P.count P.observed Λ
    (fun r t => P.decode_meas r.1 r.2 t) P.count_meas P.observed_meas
  exact (hC.preimage ((P.history_meas k).prodMk P.latent_meas)).inter
    (hC.preimage ((P.history_meas k).prodMk (P.sampled_meas k)))

lemma goodTV_measurable (L : ℝ) (k : ℕ) : MeasurableSet (P.goodTV L k) := by
  have hC := currentTVSet_measurable P.row P.count P.observed L
    (fun r t => P.decode_meas r.1 r.2 t) P.count_meas P.observed_meas
  exact (hC.preimage ((P.history_meas k).prodMk P.latent_meas)).inter
    (hC.preimage ((P.history_meas k).prodMk (P.sampled_meas k)))

lemma count_bound (K k : ℕ) (hk : k < K) (ω : Ω) (r : S × A) :
    P.count (P.history k ω) r ≤ K * T := by
  rw [P.count_match, E.count_prefix]
  exact (Counts.before_bound (fun j => visitCount_le r T (E.path j ω)) k).trans
    (Nat.mul_le_mul_right T hk.le)

include P in
lemma true_mass_measurable (s : S) (a : A) (t : S) :
    Measurable (fun ω => (E.latent ω s a).mass t) := by
  simpa only [P.latent_match] using (P.decode_meas s a t).comp P.latent_meas

lemma policy_mass_measurable (k h : ℕ) (s : S) (a : A) :
    Measurable (fun ω => (P.policies ω k h s).mass a) :=
  (E.policy_meas k h s a).comp (E.info_meas k)

lemma sampled_mass_measurable (k : ℕ) (s : S) (a : A) (t : S) :
    Measurable (fun ω => (P.sampledKernels ω k s a).mass t) :=
  (P.decode_meas s a t).comp (P.sampled_meas k)

/-- The reciprocal failure budget appearing in (4.2)--(4.3). -/
def expectedBudget (_P : PosteriorSystem (Model := Model) (Hist := Hist) E) (K : ℕ) : ℝ := 8 * (Fintype.card (S × A) : ℝ) * T * (K : ℝ)^2

lemma expectedBudget_one_le (hT : 1 ≤ T) {K : ℕ} (hK : 1 ≤ K) : 1 ≤ P.expectedBudget K := by
  have hR : (1 : ℝ) ≤ Fintype.card (S × A) := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty (S × A))
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hRT : 1 ≤ (Fintype.card (S × A) : ℝ) * T := one_le_mul_of_one_le_of_one_le hR hT'
  have hK2 : (1 : ℝ) ≤ (K : ℝ)^2 := by nlinarith
  have hRTK : 1 ≤ ((Fintype.card (S × A) : ℝ) * T) * (K : ℝ)^2 :=
    one_le_mul_of_one_le_of_one_le hRT hK2
  unfold expectedBudget
  nlinarith

/-- Current KL confidence has its exact 1/(8K) failure allocation, derived from
raw iid row-prefix concentration and posterior symmetry under this prior. -/
theorem current_kl_failure_probability
    (external : ExternalCategoricalConcentration (S := S)) (hT : 1 ≤ T)
    {K : ℕ} (hK : 1 ≤ K) (k : ℕ) (hk : k < K) :
    μ.real (P.goodKL (klThreshold (Fintype.card S) (K*T) (P.expectedBudget K)) k)ᶜ ≤
      1 / (4 * (K : ℝ)) := by
  let Λ := klThreshold (Fintype.card S) (K*T) (P.expectedBudget K)
  have hb := P.expectedBudget_one_le hT hK
  have hpair := current_kl_failure_bound external P.row (fun r t => P.decode_meas r.1 r.2 t)
    P.count P.count_meas P.observed P.observed_meas (P.history k) (P.history_meas k).aemeasurable
    P.latent (P.sampled k) P.latent_meas (P.sampled_meas k).aemeasurable (P.posterior k)
    P.tape P.tape_meas P.tape_model (P.observed_prefix k) (K*T) (P.count_bound K k hk) hb
  have hR : (0 : ℝ) < Fintype.card (S × A) := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty (S × A))
  have hT0 : (0 : ℝ) < T := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hT
  have hK0 : (0 : ℝ) < K := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hK
  have hB : 0 < P.expectedBudget K := by unfold expectedBudget; positivity
  have hprob (B : Set Ω) (hbound : μ B ≤ (Fintype.card (S × A) : ℝ≥0∞) * (K*T) *
      ENNReal.ofReal (1 / P.expectedBudget K)) : μ.real B ≤ 1 / (8 * (K : ℝ)) := by
    have hreal := ENNReal.toReal_mono (by finiteness :
      (Fintype.card (S × A) : ℝ≥0∞) * (K*T) * ENNReal.ofReal (1 / P.expectedBudget K) ≠ ⊤) hbound
    have heq : (Fintype.card (S × A) : ℝ) * (K*T) * (1 / P.expectedBudget K) = 1 / (8 * (K : ℝ)) := by
      unfold expectedBudget
      field_simp
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / P.expectedBudget K), heq] using hreal
  have htrue := hprob _ (by simpa only [Nat.cast_mul] using hpair.1)
  have hsample := hprob _ (by simpa only [Nat.cast_mul] using hpair.2)
  have hset : (P.goodKL Λ k)ᶜ =
      {ω | (P.history k ω, P.latent ω) ∉ currentKLSet P.row P.count P.observed Λ} ∪
      {ω | (P.history k ω, P.sampled k ω) ∉ currentKLSet P.row P.count P.observed Λ} := by
    ext ω
    simp only [goodKL, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, Set.mem_union]
  rw [hset]
  have hu := measureReal_union_le (μ := μ)
    {ω | (P.history k ω, P.latent ω) ∉ currentKLSet P.row P.count P.observed Λ}
    {ω | (P.history k ω, P.sampled k ω) ∉ currentKLSet P.row P.count P.observed Λ}
  exact hu.trans ((add_le_add htrue hsample).trans_eq (by ring))

/-- The identical posterior allocation for the separate total-variation balls. -/
theorem current_tv_failure_probability
    (external : ExternalCategoricalConcentration (S := S)) (hT : 1 ≤ T)
    {K : ℕ} (hK : 1 ≤ K) (k : ℕ) (hk : k < K) :
    μ.real (P.goodTV (tvThreshold (Fintype.card S) (P.expectedBudget K)) k)ᶜ ≤
      1 / (4 * (K : ℝ)) := by
  let Λ := tvThreshold (Fintype.card S) (P.expectedBudget K)
  have hb := P.expectedBudget_one_le hT hK
  have hpair := current_tv_failure_bound external P.row (fun r t => P.decode_meas r.1 r.2 t)
    P.count P.count_meas P.observed P.observed_meas (P.history k) (P.history_meas k).aemeasurable
    P.latent (P.sampled k) P.latent_meas (P.sampled_meas k).aemeasurable (P.posterior k)
    P.tape P.tape_meas P.tape_model (P.observed_prefix k) (K*T) (P.count_bound K k hk) hb
  have hR : (0 : ℝ) < Fintype.card (S × A) := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty (S × A))
  have hT0 : (0 : ℝ) < T := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hT
  have hK0 : (0 : ℝ) < K := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hK
  have hB : 0 < P.expectedBudget K := by unfold expectedBudget; positivity
  have hprob (B : Set Ω) (hbound : μ B ≤ (Fintype.card (S × A) : ℝ≥0∞) * (K*T) *
      ENNReal.ofReal (1 / P.expectedBudget K)) : μ.real B ≤ 1 / (8 * (K : ℝ)) := by
    have hreal := ENNReal.toReal_mono (by finiteness :
      (Fintype.card (S × A) : ℝ≥0∞) * (K*T) * ENNReal.ofReal (1 / P.expectedBudget K) ≠ ⊤) hbound
    have heq : (Fintype.card (S × A) : ℝ) * (K*T) * (1 / P.expectedBudget K) = 1 / (8 * (K : ℝ)) := by
      unfold expectedBudget
      field_simp
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / P.expectedBudget K), heq] using hreal
  have htrue := hprob _ (by simpa only [Nat.cast_mul] using hpair.1)
  have hsample := hprob _ (by simpa only [Nat.cast_mul] using hpair.2)
  have hset : (P.goodTV Λ k)ᶜ =
      {ω | (P.history k ω, P.latent ω) ∉ currentTVSet P.row P.count P.observed Λ} ∪
      {ω | (P.history k ω, P.sampled k ω) ∉ currentTVSet P.row P.count P.observed Λ} := by
    ext ω
    simp only [goodTV, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, Set.mem_union]
  rw [hset]
  have hu := measureReal_union_le (μ := μ)
    {ω | (P.history k ω, P.latent ω) ∉ currentTVSet P.row P.count P.observed Λ}
    {ω | (P.history k ω, P.sampled k ω) ∉ currentTVSet P.row P.count P.observed Λ}
  exact hu.trans ((add_le_add htrue hsample).trans_eq (by ring))

/-- Fixed-budget current confidence failure, without committing to a particular
value of delta. It supplies the probability allocation in Theorem 5.6. -/
theorem current_kl_failure_probability_budget
    (external : ExternalCategoricalConcentration (S := S)) (K k : ℕ) (hk : k < K)
    {budget : ℝ} (hb : 1 ≤ budget) :
    μ.real (P.goodKL (klThreshold (Fintype.card S) (K*T) budget) k)ᶜ ≤
      2 * ((Fintype.card (S × A) : ℝ) * (K : ℝ) * T * (1 / budget)) := by
  let Λ := klThreshold (Fintype.card S) (K*T) budget
  have hpair := current_kl_failure_bound external P.row (fun r t => P.decode_meas r.1 r.2 t)
    P.count P.count_meas P.observed P.observed_meas (P.history k) (P.history_meas k).aemeasurable
    P.latent (P.sampled k) P.latent_meas (P.sampled_meas k).aemeasurable (P.posterior k)
    P.tape P.tape_meas P.tape_model (P.observed_prefix k) (K*T) (P.count_bound K k hk) hb
  have hprob (B : Set Ω) (hbound : μ B ≤ (Fintype.card (S × A) : ℝ≥0∞) * (K*T : ℕ) *
      ENNReal.ofReal (1 / budget)) :
      μ.real B ≤ (Fintype.card (S × A) : ℝ) * (K : ℝ) * T * (1 / budget) := by
    have hreal := ENNReal.toReal_mono (by finiteness :
      (Fintype.card (S × A) : ℝ≥0∞) * (K*T : ℕ) * ENNReal.ofReal (1 / budget) ≠ ⊤) hbound
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_natCast, Nat.cast_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / budget), mul_assoc] using hreal
  have htrue := hprob _ hpair.1
  have hsample := hprob _ hpair.2
  have hset : (P.goodKL Λ k)ᶜ =
      {ω | (P.history k ω, P.latent ω) ∉ currentKLSet P.row P.count P.observed Λ} ∪
      {ω | (P.history k ω, P.sampled k ω) ∉ currentKLSet P.row P.count P.observed Λ} := by
    ext ω
    simp only [goodKL, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, Set.mem_union]
  rw [hset]
  exact (measureReal_union_le _ _).trans ((add_le_add htrue hsample).trans_eq (by ring))

/-- A posterior-good episode satisfies the actual rowwise Hellinger condition
needed by hybrid simulation; the radius is derived from its two KL balls. -/
lemma goodKL_radius {Λ : ℝ} (hΛ : 0 ≤ Λ) (k : ℕ) (ω : Ω) (hg : ω ∈ P.goodKL Λ k)
    (r : S × A) (hn : 0 < P.counts ω k r) :
    hellingerSq (E.latent ω r.1 r.2) (P.sampledKernels ω k r.1 r.2) ≤
      2 * Λ / P.counts ω k r := by
  rw [P.latent_match]
  have hh := current_hellinger_radius P.row P.count P.observed hΛ (P.history k)
    P.latent (P.sampled k) ω hg.1 hg.2 r
  simpa only [row, counts, sampledKernels, P.count_match] using hh (by simpa [counts, P.count_match] using hn)

/-- The complete pathwise masked source risk decomposition, with local
confidence proved from the posterior/row-prefix model. -/
theorem masked_risk_bound {H : ℕ} (E' : EpisodeSystem μ Info S A (H+1) s₀)
    (P' : PosteriorSystem (Model := Model) (Hist := Hist) E')
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (K : ℕ) (ω : Ω) :
    (∑ k ∈ Finset.range K, if ω ∈ P'.goodKL Λ k then
      (risk α c (P'.policies ω k) (E'.latent ω) (H+1) 0 s₀ -
        risk α c (P'.policies ω k) (P'.sampledKernels ω k) (H+1) 0 s₀) else 0) ≤
      Weights.w α (H+1) * HybridCharging.Ylo (P'.policies ω) (E'.latent ω) s₀ (P'.counts ω) K H +
      4 * Weights.W α (H+1) * Real.sqrt (Λ * (K : ℝ) *
        HybridCharging.Yhi (P'.policies ω) (E'.latent ω) s₀ (P'.counts ω) K H) := by
  classical
  apply HybridCharging.masked_risk_hybrid_sum_bound α hα hα1 c hc
    (P'.policies ω) (E'.latent ω) (P'.sampledKernels ω) s₀ (P'.counts ω) hΛ K H
    (fun k => ω ∈ P'.goodKL Λ k)
  intro k _ hg s a hn
  exact P'.goodKL_radius hΛ k ω hg (s,a) (by omega)

end PosteriorSystem

/-- Integrating a signed upper-bounded error splits off only the probability
of a bad event. Its negative values do not require an absolute-error assumption. -/
theorem integral_le_masked_add_failure {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : Integrable F μ)
    (good : Set Ω) (hg : MeasurableSet good) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ ω, F ω ≤ b) :
    (∫ ω, F ω ∂μ) ≤ (∫ ω, good.indicator F ω ∂μ) + b * μ.real goodᶜ := by
  have hsplit : F = good.indicator F + goodᶜ.indicator F := by
    funext ω
    by_cases hω : ω ∈ good <;> simp [hω]
  have hbad : (∫ ω, goodᶜ.indicator F ω ∂μ) ≤ b * μ.real goodᶜ := by
    have hi := integral_mono_ae (hF.indicator hg.compl) ((integrable_const b).indicator hg.compl)
      (ae_of_all _ fun ω => by by_cases hω : ω ∈ goodᶜ <;> simp [hω, hbound ω])
    simpa only [integral_indicator hg.compl, setIntegral_const, smul_eq_mul, mul_comm] using hi
  calc
    (∫ ω, F ω ∂μ) = ∫ ω, good.indicator F ω + goodᶜ.indicator F ω ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => congrFun hsplit ω)
    _ = (∫ ω, good.indicator F ω ∂μ) + ∫ ω, goodᶜ.indicator F ω ∂μ :=
      integral_add (hF.indicator hg) (hF.indicator hg.compl)
    _ ≤ _ := add_le_add_left hbad _

namespace PosteriorSystem
variable {E : EpisodeSystem μ Info S A T s₀} (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

def riskError (α : ℝ) (c : ℕ → S → A → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  risk α c (P.policies ω k) (E.latent ω) T 0 s₀ -
    risk α c (P.policies ω k) (P.sampledKernels ω k) T 0 s₀

def maskedRisk (α : ℝ) (c : ℕ → S → A → ℝ) (Λ : ℝ) (K : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range K, (P.goodKL Λ k).indicator (P.riskError α c k) ω

lemma riskError_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1) (k : ℕ) :
    Integrable (P.riskError α c k) μ := by
  exact (Measurability.integrable_risk μ α hα hα1 c hc (fun ω => P.policies ω k) E.latent
    (P.policy_mass_measurable k) P.true_mass_measurable T 0 s₀).sub
    (Measurability.integrable_risk μ α hα hα1 c hc (fun ω => P.policies ω k)
      (fun ω => P.sampledKernels ω k) (P.policy_mass_measurable k)
      (P.sampled_mass_measurable k) T 0 s₀)

lemma riskError_upper (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (k : ℕ) (ω : Ω) : P.riskError α c k ω ≤ T := by
  have hp := risk_bounds α hα hα1 c hc (P.policies ω k) (E.latent ω) T 0 s₀
  have hq := risk_bounds α hα hα1 c hc (P.policies ω k) (P.sampledKernels ω k) T 0 s₀
  dsimp [riskError]
  linarith [hp.2, hq.1]

lemma maskedRisk_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1) (Λ : ℝ) (K : ℕ) :
    Integrable (P.maskedRisk α c Λ K) μ :=
  integrable_finset_sum _ fun k _ =>
    (P.riskError_integrable α hα hα1 c hc k).indicator (P.goodKL_measurable Λ k)

/-- The complete expected confidence-failure allowance: it is at most T/4,
so the paper's convenient T/2 allowance is retained without changing its constant. -/
theorem risk_expectation_le_masked
    (external : ExternalCategoricalConcentration (S := S)) (hT : 1 ≤ T)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Finset.range K, ∫ ω, P.riskError α c k ω ∂μ) ≤
      (∫ ω, P.maskedRisk α c (klThreshold (Fintype.card S) (K*T) (P.expectedBudget K)) K ω ∂μ) +
        (T : ℝ)/4 := by
  let Λ := klThreshold (Fintype.card S) (K*T) (P.expectedBudget K)
  have hstep : ∀ k < K, (∫ ω, P.riskError α c k ω ∂μ) ≤
      (∫ ω, (P.goodKL Λ k).indicator (P.riskError α c k) ω ∂μ) +
        (T : ℝ) * (1 / (4 * (K : ℝ))) := by
    intro k hk
    have hi := integral_le_masked_add_failure (P.riskError_integrable α hα hα1 c hc k)
      (P.goodKL Λ k) (P.goodKL_measurable Λ k) (Nat.cast_nonneg T)
      (P.riskError_upper α hα hα1 c hc k)
    have hp := P.current_kl_failure_probability external hT hK k hk
    exact hi.trans (add_le_add_left (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg T)) _)
  calc
    _ ≤ ∑ k ∈ Finset.range K,
        ((∫ ω, (P.goodKL Λ k).indicator (P.riskError α c k) ω ∂μ) +
          (T : ℝ) * (1 / (4 * (K : ℝ)))) :=
      Finset.sum_le_sum fun k hk => hstep k (Finset.mem_range.mp hk)
    _ = (∫ ω, P.maskedRisk α c Λ K ω ∂μ) + (T : ℝ)/4 := by
      rw [Finset.sum_add_distrib]
      rw [show (∫ ω, P.maskedRisk α c Λ K ω ∂μ) =
        ∑ k ∈ Finset.range K, ∫ ω, (P.goodKL Λ k).indicator (P.riskError α c k) ω ∂μ from
        integral_finset_sum _ (fun k _ =>
          (P.riskError_integrable α hα hα1 c hc k).indicator (P.goodKL_measurable Λ k))]
      congr 1
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
      field_simp

lemma klThreshold_expected_eq_target (K : ℕ) :
    klThreshold (Fintype.card S) (K*T) (P.expectedBudget K) =
      Target.Lambda (Fintype.card S) (Fintype.card A) T K := by
  unfold klThreshold expectedBudget Target.Lambda
  simp only [Fintype.card_prod, Nat.cast_mul]
  congr 1
  ring


def rewardError (r : ℕ → S → A → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  HybridCharging.ordinaryReward r (P.policies ω k) (P.sampledKernels ω k) T 0 s₀ -
    HybridCharging.ordinaryReward r (P.policies ω k) (E.latent ω) T 0 s₀

def maskedReward (r : ℕ → S → A → ℝ) (L : ℝ) (K : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range K, (P.goodTV L k).indicator (P.rewardError r k) ω

lemma rewardError_integrable (r : ℕ → S → A → ℝ)
    (hr : ∀ h s a, 0 ≤ r h s a ∧ r h s a ≤ 1) (k : ℕ) :
    Integrable (P.rewardError r k) μ := by
  exact (Measurability.integrable_risk μ 1 (by norm_num) le_rfl r hr
    (fun ω => P.policies ω k) (fun ω => P.sampledKernels ω k)
    (P.policy_mass_measurable k) (P.sampled_mass_measurable k) T 0 s₀).sub
    (Measurability.integrable_risk μ 1 (by norm_num) le_rfl r hr
      (fun ω => P.policies ω k) E.latent (P.policy_mass_measurable k) P.true_mass_measurable T 0 s₀)

lemma rewardError_upper (r : ℕ → S → A → ℝ)
    (hr : ∀ h s a, 0 ≤ r h s a ∧ r h s a ≤ 1) (k : ℕ) (ω : Ω) : P.rewardError r k ω ≤ T := by
  have hp := risk_bounds 1 (by norm_num) le_rfl r hr (P.policies ω k) (E.latent ω) T 0 s₀
  have hq := risk_bounds 1 (by norm_num) le_rfl r hr (P.policies ω k) (P.sampledKernels ω k) T 0 s₀
  dsimp [rewardError, HybridCharging.ordinaryReward]
  linarith [hp.1, hq.2]

lemma maskedReward_integrable (r : ℕ → S → A → ℝ)
    (hr : ∀ h s a, 0 ≤ r h s a ∧ r h s a ≤ 1) (L : ℝ) (K : ℕ) :
    Integrable (P.maskedReward r L K) μ :=
  integrable_finset_sum _ fun k _ =>
    (P.rewardError_integrable r hr k).indicator (P.goodTV_measurable L k)

lemma goodTV_radius {L : ℝ} (hL : 0 ≤ L) (k : ℕ) (ω : Ω) (hg : ω ∈ P.goodTV L k)
    (r : S × A) (hn : 0 < P.counts ω k r) :
    tv (E.latent ω r.1 r.2) (P.sampledKernels ω k r.1 r.2) ≤ Real.sqrt (2 * L / P.counts ω k r) := by
  rw [P.latent_match]
  have hh := current_tv_radius P.row P.count P.observed hL (P.history k)
    P.latent (P.sampled k) ω hg.1 hg.2 r
  simpa only [row, counts, sampledKernels, P.count_match] using hh (by simpa [counts, P.count_match] using hn)

theorem reward_expectation_le_masked
    (external : ExternalCategoricalConcentration (S := S)) (hT : 1 ≤ T)
    (r : ℕ → S → A → ℝ) (hr : ∀ h s a, 0 ≤ r h s a ∧ r h s a ≤ 1)
    {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Finset.range K, ∫ ω, P.rewardError r k ω ∂μ) ≤
      (∫ ω, P.maskedReward r (tvThreshold (Fintype.card S) (P.expectedBudget K)) K ω ∂μ) +
        (T : ℝ)/4 := by
  let L := tvThreshold (Fintype.card S) (P.expectedBudget K)
  have hstep : ∀ k < K, (∫ ω, P.rewardError r k ω ∂μ) ≤
      (∫ ω, (P.goodTV L k).indicator (P.rewardError r k) ω ∂μ) +
        (T : ℝ) * (1 / (4 * (K : ℝ))) := by
    intro k hk
    have hi := integral_le_masked_add_failure (P.rewardError_integrable r hr k)
      (P.goodTV L k) (P.goodTV_measurable L k) (Nat.cast_nonneg T) (P.rewardError_upper r hr k)
    have hp := P.current_tv_failure_probability external hT hK k hk
    exact hi.trans (add_le_add_left (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg T)) _)
  calc
    _ ≤ ∑ k ∈ Finset.range K,
        ((∫ ω, (P.goodTV L k).indicator (P.rewardError r k) ω ∂μ) +
          (T : ℝ) * (1 / (4 * (K : ℝ)))) :=
      Finset.sum_le_sum fun k hk => hstep k (Finset.mem_range.mp hk)
    _ = (∫ ω, P.maskedReward r L K ω ∂μ) + (T : ℝ)/4 := by
      rw [Finset.sum_add_distrib]
      rw [show (∫ ω, P.maskedReward r L K ω ∂μ) =
        ∑ k ∈ Finset.range K, ∫ ω, (P.goodTV L k).indicator (P.rewardError r k) ω ∂μ from
        integral_finset_sum _ (fun k _ =>
          (P.rewardError_integrable r hr k).indicator (P.goodTV_measurable L k))]
      congr 1
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
      field_simp

section SourceHorizon
variable {H : ℕ} (E' : EpisodeSystem μ Info S A (H+1) s₀)
  (P' : PosteriorSystem (Model := Model) (Hist := Hist) E')

/-- The full expected posterior risk-simulation bound before the final
square-root identity rewrites it as C_K sqrt K. Every confidence, count and
Jensen step is derived from the source protocol and the two external iid facts. -/
theorem risk_expectation_bound_raw
    (external : ExternalCategoricalConcentration (S := S))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1) {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Finset.range K, ∫ ω, P'.riskError α c k ω ∂μ) ≤
      2 * (Fintype.card (S × A) : ℝ) * (H+1) * Weights.w α (H+1) +
      4 * Weights.W α (H+1) * Real.sqrt
        (klThreshold (Fintype.card S) (K*(H+1)) (P'.expectedBudget K) * (K : ℝ) *
          (2 * (Fintype.card (S × A) : ℝ) * Real.log (Real.exp 1 * (K : ℝ) * (H+1)))) +
      (H+1 : ℝ) / 4 := by
  let Λ := klThreshold (Fintype.card S) (K*(H+1)) (P'.expectedBudget K)
  have hΛ : 0 ≤ Λ := klThreshold_nonneg _ _ (P'.expectedBudget_one_le (by omega) hK)
  have hpath : ∀ᵐ ω ∂μ, P'.maskedRisk α c Λ K ω ≤
      Weights.w α (H+1) * HybridCharging.Ylo (P'.policies ω) (E'.latent ω) s₀ (P'.counts ω) K H +
      4 * Weights.W α (H+1) * Real.sqrt (Λ * (K : ℝ) *
        HybridCharging.Yhi (P'.policies ω) (E'.latent ω) s₀ (P'.counts ω) K H) := by
    apply ae_of_all
    intro ω
    simpa only [maskedRisk, riskError, Set.indicator_apply] using
      masked_risk_bound E' P' α hα hα1 c hc hΛ K ω
  have hexpect := HybridCharging.expected_charging_bound μ
    (P'.maskedRisk_integrable α hα hα1 c hc Λ K) (E'.Ylo_integrable K) (E'.Yhi_integrable K)
    (ae_of_all _ fun ω => E'.Yhi_nonneg K ω) (Weights.W_nonneg α (H+1)) hΛ K hpath
  have hlow := mul_le_mul_of_nonneg_left (E'.integral_Ylo_le K) (Weights.w_nonneg α (H+1))
  have hhigh := mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (E'.integral_Yhi_le hK)
      (show 0 ≤ Λ * (K : ℝ) by positivity)))
    (show 0 ≤ 4 * Weights.W α (H+1) from mul_nonneg (by norm_num) (Weights.W_nonneg α (H+1)))
  have hmask := hexpect.trans (add_le_add hlow hhigh)
  have hfail := P'.risk_expectation_le_masked external (by omega) α hα hα1 c hc hK
  change _ ≤ _
  dsimp [Λ] at hmask
  have htotal := hfail.trans (add_le_add_right hmask (((H+1 : ℕ) : ℝ) / 4))
  -- The next line only normalizes products and the natural horizon cast.
  convert htotal using 1 <;> simp only [Nat.cast_add, Nat.cast_one] <;> ring

/-- The full fixed-K certificate before substituting the prescribed delta
budget. The only exceptional terms are the proved posterior-row union bound
and the two applications of the proved predictable-to-realized conversion. -/
theorem risk_certificate_probability_raw
    (external : ExternalCategoricalConcentration (S := S))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (E'.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (E'.path k))
    {K : ℕ} (hK : 1 ≤ K) {budget ell : ℝ} (hb : 1 ≤ budget) (hell : 0 < ell) :
    μ.real {ω | Weights.w α (H+1) *
        (4 * (Fintype.card (S × A) : ℝ) * (H+1) + 2 * (H+1) * ell) +
      4 * Weights.W α (H+1) * Real.sqrt
        (klThreshold (Fintype.card S) (K*(H+1)) budget * (K : ℝ) *
          (4 * (Fintype.card (S × A) : ℝ) * Real.log (Real.exp 1 * (K : ℝ) * (H+1)) + 2 * ell)) <
      ∑ k ∈ Finset.range K, P'.riskError α c k ω} ≤
      2 * (K : ℝ) * ((Fintype.card (S × A) : ℝ) * (K : ℝ) * (H+1) * (1 / budget)) +
        2 * Real.exp (-ell) := by
  let Λ := klThreshold (Fintype.card S) (K*(H+1)) budget
  let Bconf : Set Ω := ⋃ k ∈ Finset.range K, (P'.goodKL Λ k)ᶜ
  let Blow := 4 * (Fintype.card (S × A) : ℝ) * (H+1) + 2 * (H+1) * ell
  let Bhi := 4 * (Fintype.card (S × A) : ℝ) * Real.log (Real.exp 1 * (K : ℝ) * (H+1)) + 2 * ell
  let Ylo := fun ω => HybridCharging.Ylo (P'.policies ω) (E'.latent ω) s₀ (P'.counts ω) K H
  let Yhi := fun ω => HybridCharging.Yhi (P'.policies ω) (E'.latent ω) s₀ (P'.counts ω) K H
  let Btotal : Set Ω := Bconf ∪ ({ω | Blow < Ylo ω} ∪ {ω | Bhi < Yhi ω})
  have hΛ : 0 ≤ Λ := klThreshold_nonneg _ _ hb
  have hconf : μ.real Bconf ≤ 2 * (K : ℝ) *
      ((Fintype.card (S × A) : ℝ) * (K : ℝ) * (H+1) * (1 / budget)) := by
    apply (measureReal_biUnion_finset_le (Finset.range K) (fun k => (P'.goodKL Λ k)ᶜ)).trans
    calc
      _ ≤ ∑ _k ∈ Finset.range K, 2 *
          ((Fintype.card (S × A) : ℝ) * (K : ℝ) * (H+1) * (1 / budget)) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa only [Nat.cast_add, Nat.cast_one] using
          P'.current_kl_failure_probability_budget external K k (Finset.mem_range.mp hk) hb
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hlo : μ.real {ω | Blow < Ylo ω} ≤ Real.exp (-ell) :=
    E'.Ylo_probability_bound ℱ hinfo hpath K hell
  have hhi : μ.real {ω | Bhi < Yhi ω} ≤ Real.exp (-ell) :=
    E'.Yhi_probability_bound ℱ hinfo hpath hK hell
  have htotal : μ.real Btotal ≤ 2 * (K : ℝ) *
      ((Fintype.card (S × A) : ℝ) * (K : ℝ) * (H+1) * (1 / budget)) + 2 * Real.exp (-ell) := by
    have hu := (measureReal_union_le Bconf ({ω | Blow < Ylo ω} ∪ {ω | Bhi < Yhi ω})).trans
      (add_le_add hconf (measureReal_union_le {ω | Blow < Ylo ω} {ω | Bhi < Yhi ω}))
    exact hu.trans (by linarith)
  apply le_trans (measureReal_mono ?_ (measure_ne_top μ _)) htotal
  intro ω herr
  by_cases hbc : ω ∈ Bconf
  · exact Or.inl hbc
  by_cases hbl : Blow < Ylo ω
  · exact Or.inr (Or.inl hbl)
  by_cases hbh : Bhi < Yhi ω
  · exact Or.inr (Or.inr hbh)
  have hgood : ∀ k < K, ω ∈ P'.goodKL Λ k := by
    intro k hk
    by_contra hbad
    apply hbc
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hk, hbad⟩⟩
  have hrow : ∀ k, k < K → ∀ s a, H+1 ≤ P'.counts ω k (s,a) →
      hellingerSq (E'.latent ω s a) (P'.sampledKernels ω k s a) ≤ 2 * Λ / P'.counts ω k (s,a) := by
    intro k hk s a hn
    exact P'.goodKL_radius hΛ k ω (hgood k hk) (s,a) (by omega)
  have hs := HybridCharging.risk_hybrid_sum_bound α hα hα1 c hc
    (P'.policies ω) (E'.latent ω) (P'.sampledKernels ω) s₀ (P'.counts ω) hΛ K H hrow
  have hbnd : Weights.w α (H+1) * Ylo ω + 4 * Weights.W α (H+1) *
      Real.sqrt (Λ * (K : ℝ) * Yhi ω) ≤
      Weights.w α (H+1) * Blow + 4 * Weights.W α (H+1) * Real.sqrt (Λ * (K : ℝ) * Bhi) := by
    exact add_le_add (mul_le_mul_of_nonneg_left (le_of_not_gt hbl) (Weights.w_nonneg α (H+1)))
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left (le_of_not_gt hbh) (by positivity)))
        (show 0 ≤ 4 * Weights.W α (H+1) from mul_nonneg (by norm_num) (Weights.W_nonneg α (H+1))))
  have hs' : (∑ k ∈ Finset.range K, P'.riskError α c k ω) ≤
      Weights.w α (H+1) * Blow + 4 * Weights.W α (H+1) * Real.sqrt (Λ * (K : ℝ) * Bhi) :=
    hs.trans hbnd
  exact False.elim (not_lt_of_ge hs' herr)

/-- Complete policy-uniform expected reward simulation before the numerical
constant-8 envelope. It uses the separate Weissman balls and actual visits. -/
theorem reward_expectation_bound_raw
    (external : ExternalCategoricalConcentration (S := S))
    (r : ℕ → S → A → ℝ) (hr : ∀ h s a, 0 ≤ r h s a ∧ r h s a ≤ 1)
    {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Finset.range K, ∫ ω, P'.rewardError r k ω ∂μ) ≤
      min ((H+1 : ℝ) * K)
        (2 * (Fintype.card (S × A) : ℝ) * (H+1)^2 +
          (H+1) * Real.sqrt (2 * tvThreshold (Fintype.card S) (P'.expectedBudget K)) *
            (3 * Real.sqrt ((Fintype.card (S × A) : ℝ) * (K : ℝ) * (H+1)))) + (H+1 : ℝ)/4 := by
  let L := tvThreshold (Fintype.card S) (P'.expectedBudget K)
  have hL : 0 ≤ L := tvThreshold_nonneg _ (P'.expectedBudget_one_le (by omega) hK)
  have hpath : ∀ᵐ ω ∂μ, P'.maskedReward r L K ω ≤
      ((H+1 : ℕ) : ℝ) * HybridCharging.Ylo (P'.policies ω) (E'.latent ω) s₀ (P'.counts ω) K H +
      ((H+1 : ℕ) : ℝ) * Real.sqrt (2*L) *
        HybridCharging.Ysqrt (P'.policies ω) (E'.latent ω) s₀ (P'.counts ω) K H := by
    apply ae_of_all
    intro ω
    have hrow : ∀ k, k < K → ω ∈ P'.goodTV L k → ∀ s a, H+1 ≤ P'.counts ω k (s,a) →
        tv (E'.latent ω s a) (P'.sampledKernels ω k s a) ≤ Real.sqrt (2*L / P'.counts ω k (s,a)) := by
      intro k _ hg s a hn
      exact P'.goodTV_radius hL k ω hg (s,a) (by omega)
    simpa only [maskedReward, rewardError, Set.indicator_apply] using
      HybridCharging.masked_reward_charging_bound r hr (P'.policies ω) (E'.latent ω)
        (P'.sampledKernels ω) s₀ (P'.counts ω) hL K H (fun k => ω ∈ P'.goodTV L k) hrow
  have hi := integral_mono_ae (P'.maskedReward_integrable r hr L K)
    (((E'.Ylo_integrable K).const_mul ((H+1 : ℕ) : ℝ)).add
      ((E'.Ysqrt_integrable K).const_mul (((H+1 : ℕ) : ℝ) * Real.sqrt (2*L)))) hpath
  simp only [Pi.add_apply] at hi
  rw [integral_add ((E'.Ylo_integrable K).const_mul ((H+1 : ℕ) : ℝ))
    ((E'.Ysqrt_integrable K).const_mul (((H+1 : ℕ) : ℝ) * Real.sqrt (2*L))),
    integral_const_mul, integral_const_mul] at hi
  have hl := mul_le_mul_of_nonneg_left (E'.integral_Ylo_le K) (Nat.cast_nonneg (H+1))
  have hs := mul_le_mul_of_nonneg_left (E'.integral_Ysqrt_le K)
    (show 0 ≤ ((H+1 : ℕ) : ℝ) * Real.sqrt (2*L) by positivity)
  have hmask := hi.trans (add_le_add hl hs)
  have hfail := P'.reward_expectation_le_masked external (by omega) r hr hK
  have hlarge : (∑ k ∈ Finset.range K, ∫ ω, P'.rewardError r k ω ∂μ) ≤
      2 * (Fintype.card (S × A) : ℝ) * (H+1)^2 +
        (H+1) * Real.sqrt (2*L) * (3 * Real.sqrt ((Fintype.card (S × A) : ℝ) * (K : ℝ) * (H+1))) +
          (H+1 : ℝ)/4 := by
    have hh := hfail.trans (add_le_add_right hmask (((H+1 : ℕ) : ℝ)/4))
    convert hh using 1 <;> simp only [Nat.cast_add, Nat.cast_one] <;> ring
  have hsmall : (∑ k ∈ Finset.range K, ∫ ω, P'.rewardError r k ω ∂μ) ≤ (H+1 : ℝ) * K := by
    calc
      _ ≤ ∑ _k ∈ Finset.range K, (H+1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        have hh := integral_mono_ae (P'.rewardError_integrable r hr k) (integrable_const ((H+1 : ℕ) : ℝ))
          (ae_of_all _ fun ω => P'.rewardError_upper r hr k ω)
        simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul,
          Nat.cast_add, Nat.cast_one] using hh
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hmin := le_min
    (show (∑ k ∈ Finset.range K, ∫ ω, P'.rewardError r k ω ∂μ) - (H+1 : ℝ)/4 ≤ (H+1 : ℝ)*K by linarith)
    (show (∑ k ∈ Finset.range K, ∫ ω, P'.rewardError r k ω ∂μ) - (H+1 : ℝ)/4 ≤
      2 * (Fintype.card (S × A) : ℝ) * (H+1)^2 +
        (H+1) * Real.sqrt (2*L) * (3 * Real.sqrt ((Fintype.card (S × A) : ℝ) * (K : ℝ) * (H+1))) by linarith)
  dsimp [L] at hmin
  linarith

/-- Lemma 5.5 with the exact C_K and D of (4.3) and (5.8). -/
theorem lemma_5_5
    (external : ExternalCategoricalConcentration (S := S))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1) {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Finset.range K, ∫ ω, P'.riskError α c k ω ∂μ) ≤
      Target.confidence (Target.scale (Weights.W α (H+1)) (Fintype.card S) (Fintype.card A))
        (Fintype.card S) (Fintype.card A) (H+1) K * Real.sqrt (K : ℝ) +
      (2 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (H+1) * Weights.w α (H+1) + (H+1 : ℝ)/2) := by
  have hs : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty S)
  have ha : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty A)
  have hh : (1 : ℝ) ≤ (H+1 : ℝ) := by have := Nat.cast_nonneg (α := ℝ) H; linarith
  have hraw := risk_expectation_bound_raw E' P' external α hα hα1 c hc hK
  rw [P'.klThreshold_expected_eq_target K] at hraw
  simp only [Fintype.card_prod, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hraw
  rw [Bounds.expected_high_eq_confidence hs ha hh K hK] at hraw
  linarith

lemma tvThreshold_expected_eq_rewardLog (K : ℕ) :
    tvThreshold (Fintype.card S) (P'.expectedBudget K) =
      Bounds.rewardLog (Fintype.card S) (Fintype.card A) (H+1) K := by
  unfold tvThreshold expectedBudget Bounds.rewardLog Bounds.budget
  simp only [Fintype.card_prod, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  congr 2
  ring

/-- Lemma 5.8 with the paper's literal numerical constant 8 and T/2 allowance. -/
theorem lemma_5_8
    (external : ExternalCategoricalConcentration (S := S))
    (r : ℕ → S → A → ℝ) (hr : ∀ h s a, 0 ≤ r h s a ∧ r h s a ≤ 1)
    {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Finset.range K, ∫ ω, P'.rewardError r k ω ∂μ) ≤
      8 * (H+1) * Real.sqrt (H+1) * Real.sqrt
        ((Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K : ℝ) *
          Bounds.rewardLog (Fintype.card S) (Fintype.card A) (H+1) K) + (H+1 : ℝ)/2 := by
  let R : ℝ := (Fintype.card S : ℝ) * (Fintype.card A : ℝ)
  let L := Bounds.rewardLog (Fintype.card S) (Fintype.card A) (H+1) K
  have hs : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty S)
  have ha : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty A)
  have hh : (1 : ℝ) ≤ (H+1 : ℝ) := by have := Nat.cast_nonneg (α := ℝ) H; linarith
  have hL : 1 ≤ L := Bounds.rewardLog_one_le hs ha hh hK
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hraw := reward_expectation_bound_raw E' P' external r hr hK
  rw [tvThreshold_expected_eq_rewardLog E' P' K] at hraw
  simp only [Fintype.card_prod, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hraw
  have hfactor := Bounds.reward_high_factor hR (show 0 ≤ (H+1 : ℝ) by positivity)
    (Nat.cast_nonneg K) (show 0 ≤ L by linarith)
  have hnum := HybridCharging.reward_numerical_envelope hR (show 0 ≤ (H+1 : ℝ) by positivity)
    (Nat.cast_nonneg K) hL
  change (H+1) * Real.sqrt (2*L) * (3*Real.sqrt (R*(K:ℝ)*(H+1))) = _ at hfactor
  change min ((H+1)*(K:ℝ)) (2*R*(H+1)^2+3*Real.sqrt 2*((H+1)*Real.sqrt (H+1)*Real.sqrt (R*(K:ℝ)*L))) ≤ _ at hnum
  rw [← hfactor] at hnum
  have hfinal := hraw.trans (add_le_add_right hnum ((H+1 : ℝ)/4))
  dsimp [R, L] at hfinal
  nlinarith

/-- Theorem 5.6, equation (5.11), at its prescribed fixed (K,delta). -/
theorem theorem_5_6
    (external : ExternalCategoricalConcentration (S := S))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (E'.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (E'.path k))
    {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    μ.real {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1)
      (Weights.W α (H+1)) (Weights.w α (H+1)) δ K <
        ∑ k ∈ Finset.range K, P'.riskError α c k ω} ≤ δ := by
  have hs : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty S)
  have ha : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty A)
  have hh : (1 : ℝ) ≤ (H+1 : ℝ) := by have := Nat.cast_nonneg (α := ℝ) H; linarith
  let budget := Bounds.certificateBudget (Fintype.card S) (Fintype.card A) (H+1) δ K
  have hb : 1 ≤ budget := Bounds.certificateBudget_one_le hs ha hh hδ hδ1 hK
  have hell : 0 < Bounds.ell δ := Bounds.ell_pos hδ hδ1
  have hraw := risk_certificate_probability_raw E' P' external α hα hα1 c hc ℱ hinfo hpath hK hb hell
  have hcharge := Bounds.certificate_budget_charge (show (0:ℝ)<Fintype.card S by linarith)
    (show (0:ℝ)<Fintype.card A by linarith) (show (0:ℝ)<(H+1:ℝ) by linarith) hδ
    (show 0 < K by omega)
  have hbudget : (Fintype.card (S × A) : ℝ) * (K:ℝ) * (H+1) * (1 / budget) =
      δ / (4 * (K:ℝ)) := by
    convert hcharge using 1 <;> simp only [Fintype.card_prod, Nat.cast_mul, budget] <;> ring
  rw [hbudget, Bounds.exp_neg_ell hδ] at hraw
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have hprob : 2 * (K:ℝ) * (δ/(4*(K:ℝ))) + 2*(δ/4) = δ := by field_simp; ring
  rw [hprob] at hraw
  convert hraw using 1
  congr 1
  ext ω
  congr 1
  unfold Bounds.certificate Bounds.certificateLog klThreshold
  simp only [Fintype.card_prod, Nat.cast_mul, Nat.cast_add, Nat.cast_one, budget]
  ring

end SourceHorizon
end PosteriorSystem

end
end Paper36.Statistical
