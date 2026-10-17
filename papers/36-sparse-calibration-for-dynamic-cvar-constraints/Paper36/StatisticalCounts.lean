import Paper36.Trajectories
import Paper36.Counts
import Paper36.HybridCharging
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! Actual trajectory counts, their conditional occupancy means, and frozen-count charging.
The count at the beginning of an episode is the prefix sum of observed trajectory visits. -/
namespace Paper36.StatisticalCounts
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories
noncomputable section

universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A]

/-- Every physical trajectory has exactly T state-action row visits. -/
theorem sum_visitCount (T : ℕ) (path : Trajectory S A T) :
    (∑ row : S × A, visitCount row T path) = T := by
  induction T with
  | zero => simp [visitCount]
  | succ T ih =>
    simp only [visitCount, Finset.sum_add_distrib]
    have h : (∑ row : S × A, if (path.1,path.2.1)=row then 1 else 0) = 1 := by simp
    rw [h, ih path.2.2]
    omega

variable {Ω Info : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The pre-episode information fixes the policy, the true transition model and
frozen counts. The only dynamics premise is its actual conditional trajectory law. -/
structure EpisodeSystem (μ : Measure Ω) [IsProbabilityMeasure μ] (Info : Type*) (S A : Type u)
    [MeasurableSpace Info] [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
    [DecidableEq S] [DecidableEq A]
    (T : ℕ) (s₀ : S) where
  policy : ℕ → Info → Policy S A
  transition : ℕ → Info → Simulation.Kernel S A
  latent : Ω → Simulation.Kernel S A
  info : ℕ → Ω → Info
  path : ℕ → Ω → Trajectory S A T
  policy_meas : ∀ k h s a, Measurable (fun i => (policy k i h s).mass a)
  transition_meas : ∀ k s a t, Measurable (fun i => (transition k i s a).mass t)
  info_meas : ∀ k, Measurable (info k)
  path_meas : ∀ k, AEMeasurable (path k) μ
  model : ∀ k, condDistrib (path k) (info k) μ =ᵐ[μ.map (info k)]
    trajectoryKernel (policy k) (transition k) (policy_meas k) (transition_meas k) T s₀
  transition_match : ∀ k ω, transition k (info k ω) = latent ω
  count : ℕ → Info → S × A → ℕ
  count_meas : ∀ k row, Measurable (fun i => count k i row)
  count_prefix : ∀ k ω row, count k (info k ω) row =
    Counts.before (fun j => visitCount row T (path j ω)) k

namespace EpisodeSystem

variable {T : ℕ} {s₀ : S} (E : EpisodeSystem μ Info S A T s₀)

abbrev Weight := ℕ → Info → S × A → ℝ

def visits (ω : Ω) (row : S × A) (k : ℕ) : ℕ := visitCount row T (E.path k ω)

def realizedEpisode (w : Weight (Info := Info) (S := S) (A := A)) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ row, w k (E.info k ω) row * (E.visits ω row k : ℝ)

def nominalEpisode (w : Weight (Info := Info) (S := S) (A := A)) (L k : ℕ) (ω : Ω) : ℝ :=
  ∑ row, w k (E.info k ω) row *
    nominalVisits (E.policy k (E.info k ω)) (E.transition k (E.info k ω)) s₀ L row

def totalRealized (w : Weight (Info := Info) (S := S) (A := A)) (K : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range K, E.realizedEpisode w k ω

def totalNominal (w : Weight (Info := Info) (S := S) (A := A)) (K L : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range K, E.nominalEpisode w L k ω

lemma row_count_integrable (k : ℕ) (row : S × A) :
    Integrable (fun ω => (E.visits ω row k : ℝ)) μ := by
  apply Integrable.of_bound
    (((Measurable.of_discrete : Measurable (fun p : Trajectory S A T =>
      (visitCount row T p : ℝ))).comp_aemeasurable (E.path_meas k)).aestronglyMeasurable) T
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  change (visitCount row T (E.path k ω) : ℝ) ≤ T
  exact_mod_cast visitCount_le row T (E.path k ω)

lemma weighted_count_integrable (w : Weight (Info := Info) (S := S) (A := A))
    (hw : ∀ k row, Measurable (fun i => w k i row))
    (hb : ∀ k i row, 0 ≤ w k i row ∧ w k i row ≤ 1) (k : ℕ) (row : S × A) :
    Integrable (fun ω => w k (E.info k ω) row * (E.visits ω row k : ℝ)) μ := by
  apply Integrable.of_bound
    (((hw k row).comp (E.info_meas k)).aestronglyMeasurable.mul
      (E.row_count_integrable k row).aestronglyMeasurable) T
  filter_upwards with ω
  change ‖w k (E.info k ω) row * (E.visits ω row k : ℝ)‖ ≤ (T : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hb _ _ _).1 (Nat.cast_nonneg _))]
  have hc : (E.visits ω row k : ℝ) ≤ T := by exact_mod_cast visitCount_le row T (E.path k ω)
  exact (mul_le_mul_of_nonneg_right (hb _ _ _).2 (Nat.cast_nonneg _)).trans (by simpa using hc)

lemma weighted_nominal_integrable (w : Weight (Info := Info) (S := S) (A := A))
    (hw : ∀ k row, Measurable (fun i => w k i row))
    (hb : ∀ k i row, 0 ≤ w k i row ∧ w k i row ≤ 1) (L k : ℕ) (row : S × A) :
    Integrable (fun ω => w k (E.info k ω) row *
      nominalVisits (E.policy k (E.info k ω)) (E.transition k (E.info k ω)) s₀ L row) μ := by
  apply Integrable.of_bound
    (((hw k row).comp (E.info_meas k)).mul
      ((measurable_nominalVisits (E.policy k) (E.transition k) (E.policy_meas k)
        (E.transition_meas k) s₀ L row).comp (E.info_meas k))).aestronglyMeasurable L
  filter_upwards with ω
  change ‖w k (E.info k ω) row * nominalVisits (E.policy k (E.info k ω))
    (E.transition k (E.info k ω)) s₀ L row‖ ≤ (L : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hb _ _ _).1 (nominalVisits_nonneg _ _ _ _ _))]
  exact (mul_le_mul_of_nonneg_right (hb _ _ _).2 (nominalVisits_nonneg _ _ _ _ _)).trans
    (by simpa using (nominalVisits_le (E.policy k (E.info k ω)) (E.transition k (E.info k ω)) s₀ L row))

lemma realized_integrable (w : Weight (Info := Info) (S := S) (A := A))
    (hw : ∀ k row, Measurable (fun i => w k i row))
    (hb : ∀ k i row, 0 ≤ w k i row ∧ w k i row ≤ 1) (k : ℕ) :
    Integrable (E.realizedEpisode w k) μ :=
  integrable_finset_sum _ fun row _ => E.weighted_count_integrable w hw hb k row

lemma nominal_integrable (w : Weight (Info := Info) (S := S) (A := A))
    (hw : ∀ k row, Measurable (fun i => w k i row))
    (hb : ∀ k i row, 0 ≤ w k i row ∧ w k i row ≤ 1) (L k : ℕ) :
    Integrable (E.nominalEpisode w L k) μ :=
  integrable_finset_sum _ fun row _ => E.weighted_nominal_integrable w hw hb L k row

lemma totalNominal_integrable (w : Weight (Info := Info) (S := S) (A := A))
    (hw : ∀ k row, Measurable (fun i => w k i row))
    (hb : ∀ k i row, 0 ≤ w k i row ∧ w k i row ≤ 1) (K L : ℕ) :
    Integrable (E.totalNominal w K L) μ :=
  integrable_finset_sum _ fun k _ => E.nominal_integrable w hw hb L k

lemma totalRealized_integrable (w : Weight (Info := Info) (S := S) (A := A))
    (hw : ∀ k row, Measurable (fun i => w k i row))
    (hb : ∀ k i row, 0 ≤ w k i row ∧ w k i row ≤ 1) (K : ℕ) :
    Integrable (E.totalRealized w K) μ :=
  integrable_finset_sum _ fun k _ => E.realized_integrable w hw hb k

lemma totalNominal_nonneg (w : Weight (Info := Info) (S := S) (A := A))
    (hb : ∀ k i row, 0 ≤ w k i row ∧ w k i row ≤ 1) (K L : ℕ) (ω : Ω) :
    0 ≤ E.totalNominal w K L ω := by
  exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun row _ =>
    mul_nonneg (hb k (E.info k ω) row).1 (nominalVisits_nonneg _ _ _ _ _)

/-- All-row C.8, derived from the canonical trajectory kernel and the weighted tower property. -/
theorem integral_nominalEpisode_eq (w : Weight (Info := Info) (S := S) (A := A))
    (hw : ∀ k row, Measurable (fun i => w k i row))
    (hb : ∀ k i row, 0 ≤ w k i row ∧ w k i row ≤ 1) (k : ℕ) :
    (∫ ω, E.nominalEpisode w T k ω ∂μ) = ∫ ω, E.realizedEpisode w k ω ∂μ := by
  unfold nominalEpisode realizedEpisode
  rw [integral_finset_sum _ (fun row _ => E.weighted_nominal_integrable w hw hb T k row),
    integral_finset_sum _ (fun row _ => E.weighted_count_integrable w hw hb k row)]
  apply Finset.sum_congr rfl
  intro row _
  exact weighted_visit_identity (E.policy k) (E.transition k) (E.policy_meas k)
    (E.transition_meas k) T s₀ (E.info k) (E.path k) (E.info_meas k)
    (E.path_meas k) (E.model k) (fun i => w k i row) (hw k row) (fun i => hb k i row) row

/-- Partial nominal sums contain only L≤T error-producing stages. -/
theorem integral_totalNominal_le (w : Weight (Info := Info) (S := S) (A := A))
    (hw : ∀ k row, Measurable (fun i => w k i row))
    (hb : ∀ k i row, 0 ≤ w k i row ∧ w k i row ≤ 1) (K L : ℕ) (hLT : L ≤ T) :
    (∫ ω, E.totalNominal w K L ω ∂μ) ≤ ∫ ω, E.totalRealized w K ω ∂μ := by
  unfold totalNominal totalRealized
  rw [integral_finset_sum _ (fun k _ => E.nominal_integrable w hw hb L k),
    integral_finset_sum _ (fun k _ => E.realized_integrable w hw hb k)]
  apply Finset.sum_le_sum
  intro k _
  unfold nominalEpisode realizedEpisode
  rw [integral_finset_sum _ (fun row _ => E.weighted_nominal_integrable w hw hb L k row),
    integral_finset_sum _ (fun row _ => E.weighted_count_integrable w hw hb k row)]
  apply Finset.sum_le_sum
  intro row _
  exact weighted_partial_visit_le (E.policy k) (E.transition k) (E.policy_meas k)
    (E.transition_meas k) T L hLT s₀ (E.info k) (E.path k) (E.info_meas k)
    (E.path_meas k) (E.model k) (fun i => w k i row) (hw k row) (fun i => hb k i row) row

def lowWeight : Weight (Info := Info) (S := S) (A := A) :=
  fun k i row => if E.count k i row < T then 1 else 0

def logWeight : Weight (Info := Info) (S := S) (A := A) :=
  fun k i row => if T ≤ E.count k i row then 1/(E.count k i row : ℝ) else 0

def sqrtWeight : Weight (Info := Info) (S := S) (A := A) :=
  fun k i row => if T ≤ E.count k i row then 1/Real.sqrt (E.count k i row) else 0

lemma lowWeight_meas (k : ℕ) (row : S × A) : Measurable (fun i => E.lowWeight k i row) :=
  (Measurable.of_discrete : Measurable (fun n : ℕ => if n < T then (1:ℝ) else 0)).comp
    (E.count_meas k row)

lemma logWeight_meas (k : ℕ) (row : S × A) : Measurable (fun i => E.logWeight k i row) :=
  (Measurable.of_discrete : Measurable (fun n : ℕ => if T ≤ n then 1/(n:ℝ) else 0)).comp
    (E.count_meas k row)

lemma sqrtWeight_meas (k : ℕ) (row : S × A) : Measurable (fun i => E.sqrtWeight k i row) :=
  (Measurable.of_discrete : Measurable (fun n : ℕ => if T ≤ n then 1/Real.sqrt n else 0)).comp
    (E.count_meas k row)

lemma lowWeight_bounds : ∀ k i row, 0 ≤ E.lowWeight k i row ∧ E.lowWeight k i row ≤ 1 := by
  intro k i row
  dsimp [lowWeight]
  split_ifs <;> norm_num

lemma logWeight_bounds (hT : 0 < T) :
    ∀ k i row, 0 ≤ E.logWeight k i row ∧ E.logWeight k i row ≤ 1 := by
  intro k i row
  dsimp [logWeight]
  split_ifs with hn
  · have hN : (1:ℝ) ≤ E.count k i row := by exact_mod_cast (show 1 ≤ E.count k i row by omega)
    exact ⟨by positivity, (div_le_one (by linarith)).2 hN⟩
  · norm_num

lemma sqrtWeight_bounds (hT : 0 < T) :
    ∀ k i row, 0 ≤ E.sqrtWeight k i row ∧ E.sqrtWeight k i row ≤ 1 := by
  intro k i row
  dsimp [sqrtWeight]
  split_ifs with hn
  · have hN : (1:ℝ) ≤ E.count k i row := by exact_mod_cast (show 1 ≤ E.count k i row by omega)
    have hs : (1:ℝ) ≤ Real.sqrt (E.count k i row) := by
      simpa using Real.sqrt_le_sqrt hN
    exact ⟨by positivity, (div_le_one (by linarith)).2 hs⟩
  · norm_num

lemma visits_total (ω : Ω) (k : ℕ) : (∑ row : S × A, E.visits ω row k) = T :=
  sum_visitCount T (E.path k ω)

lemma totalRealized_low_eq (ω : Ω) (K : ℕ) :
    E.totalRealized E.lowWeight K ω =
      (∑ row : S × A, (Counts.lowCharge (E.visits ω row) T K : ℝ)) := by
  unfold totalRealized realizedEpisode lowWeight
  simp only [E.count_prefix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro row _
  simp only [Counts.lowCharge, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro k _
  change (if Counts.before (E.visits ω row) k < T then 1 else 0) * (E.visits ω row k : ℝ) = _
  split_ifs <;> simp_all

lemma totalRealized_log_eq (ω : Ω) (K : ℕ) :
    E.totalRealized E.logWeight K ω =
      ∑ row : S × A, Counts.highLogCharge (E.visits ω row) T K := by
  unfold totalRealized realizedEpisode logWeight
  simp only [E.count_prefix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro row _
  unfold Counts.highLogCharge
  apply Finset.sum_congr rfl
  intro k _
  change (if T ≤ Counts.before (E.visits ω row) k then 1/_ else 0) * (E.visits ω row k : ℝ) = _
  split_ifs <;> simp_all [visits, Counts.before, div_eq_mul_inv, mul_comm]

lemma totalRealized_sqrt_eq (ω : Ω) (K : ℕ) :
    E.totalRealized E.sqrtWeight K ω =
      ∑ row : S × A, Counts.highSqrtCharge (E.visits ω row) T K := by
  unfold totalRealized realizedEpisode sqrtWeight
  simp only [E.count_prefix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro row _
  unfold Counts.highSqrtCharge
  apply Finset.sum_congr rfl
  intro k _
  change (if T ≤ Counts.before (E.visits ω row) k then 1/_ else 0) * (E.visits ω row k : ℝ) = _
  split_ifs <;> simp_all [visits, Counts.before, div_eq_mul_inv, mul_comm]

/-- Frozen low counts are bounded pathwise using the actual random trajectory counts. -/
theorem totalRealized_low_le (hT : 0 < T) (ω : Ω) (K : ℕ) :
    E.totalRealized E.lowWeight K ω ≤ 2*(Fintype.card (S × A):ℝ)*T := by
  rw [E.totalRealized_low_eq]
  have h := Counts.all_rows_low_charge (rows := Finset.univ) (v := E.visits ω)
    (by exact Finset.univ_nonempty) hT (fun k => le_of_eq (E.visits_total ω k)) K
  have hh : (∑ row : S × A, (Counts.lowCharge (E.visits ω row) T K : ℝ)) <
      2*(Fintype.card (S × A):ℝ)*T := by exact_mod_cast h
  exact hh.le

theorem totalRealized_log_le (hT : 0 < T) {K : ℕ} (hK : 1 ≤ K) (ω : Ω) :
    E.totalRealized E.logWeight K ω ≤
      2*(Fintype.card (S × A):ℝ)*Real.log (Real.exp 1*(K:ℝ)*T) := by
  rw [E.totalRealized_log_eq]
  exact Counts.all_rows_log_charge hT (fun k => le_of_eq (E.visits_total ω k)) hK

theorem totalRealized_sqrt_le (hT : 0 < T) (ω : Ω) (K : ℕ) :
    E.totalRealized E.sqrtWeight K ω ≤
      3*Real.sqrt ((Fintype.card (S × A):ℝ)*(K:ℝ)*T) := by
  rw [E.totalRealized_sqrt_eq]
  exact Counts.all_rows_sqrt_charge hT (fun k => le_of_eq (E.visits_total ω k)) K

/-- The low-count occupancy expectation in the proof of Lemma 5.5. -/
theorem integral_low_le (hT : 0 < T) (K L : ℕ) (hLT : L ≤ T) :
    (∫ ω, E.totalNominal E.lowWeight K L ω ∂μ) ≤ 2*(Fintype.card (S × A):ℝ)*T := by
  apply (E.integral_totalNominal_le E.lowWeight E.lowWeight_meas E.lowWeight_bounds K L hLT).trans
  calc
    _ ≤ ∫ _ω, 2*(Fintype.card (S × A):ℝ)*T ∂μ :=
      integral_mono_ae (E.totalRealized_integrable _ E.lowWeight_meas E.lowWeight_bounds K)
        (integrable_const _) (ae_of_all _ fun ω => E.totalRealized_low_le hT ω K)
    _ = _ := by simp

/-- E Y_hi ≤ 2 S A log(e K T), with frozen counts and all true stages included. -/
theorem integral_log_le (hT : 0 < T) {K : ℕ} (hK : 1 ≤ K) (L : ℕ) (hLT : L ≤ T) :
    (∫ ω, E.totalNominal E.logWeight K L ω ∂μ) ≤
      2*(Fintype.card (S × A):ℝ)*Real.log (Real.exp 1*(K:ℝ)*T) := by
  apply (E.integral_totalNominal_le E.logWeight E.logWeight_meas (E.logWeight_bounds hT) K L hLT).trans
  calc
    _ ≤ ∫ _ω, 2*(Fintype.card (S × A):ℝ)*Real.log (Real.exp 1*(K:ℝ)*T) ∂μ :=
      integral_mono_ae (E.totalRealized_integrable _ E.logWeight_meas (E.logWeight_bounds hT) K)
        (integrable_const _) (ae_of_all _ fun ω => E.totalRealized_log_le hT hK ω)
    _ = _ := by simp

/-- The reward proof's square-root-count expectation is charged to real visits. -/
theorem integral_sqrt_le (hT : 0 < T) (K L : ℕ) (hLT : L ≤ T) :
    (∫ ω, E.totalNominal E.sqrtWeight K L ω ∂μ) ≤
      3*Real.sqrt ((Fintype.card (S × A):ℝ)*(K:ℝ)*T) := by
  apply (E.integral_totalNominal_le E.sqrtWeight E.sqrtWeight_meas (E.sqrtWeight_bounds hT) K L hLT).trans
  calc
    _ ≤ ∫ _ω, 3*Real.sqrt ((Fintype.card (S × A):ℝ)*(K:ℝ)*T) ∂μ :=
      integral_mono_ae (E.totalRealized_integrable _ E.sqrtWeight_meas (E.sqrtWeight_bounds hT) K)
        (integrable_const _) (ae_of_all _ fun ω => E.totalRealized_sqrt_le hT ω K)
    _ = _ := by simp

/-- The conditional mean of a weighted row count is derived from the episode law. -/
theorem conditional_weighted_row
    (w : Weight (Info := Info) (S := S) (A := A))
    (hw : ∀ k row, Measurable (fun i => w k i row))
    (hb : ∀ k i row, 0 ≤ w k i row ∧ w k i row ≤ 1) (k : ℕ) (row : S × A) :
    μ[fun ω => w k (E.info k ω) row*(E.visits ω row k : ℝ) |
      MeasurableSpace.comap (E.info k) inferInstance] =ᵐ[μ]
      fun ω => w k (E.info k ω) row*
        nominalVisits (E.policy k (E.info k ω)) (E.transition k (E.info k ω)) s₀ T row := by
  have hwsm : StronglyMeasurable[MeasurableSpace.comap (E.info k) inferInstance]
      (fun ω => w k (E.info k ω) row) :=
    (hw k row).stronglyMeasurable.comp_measurable (Measurable.of_comap_le le_rfl)
  have hp := condExp_mul_of_stronglyMeasurable_left hwsm
    (E.weighted_count_integrable w hw hb k row) (E.row_count_integrable k row)
  have hc := conditional_visitCount_of_trajectoryKernel (E.policy k) (E.transition k)
    (E.policy_meas k) (E.transition_meas k) T s₀ (E.info k) (E.path k)
    (E.info_meas k) (E.path_meas k) (E.model k) row
  filter_upwards [hp, hc] with ω hp hc
  change (μ[fun ω => w k (E.info k ω) row*(E.visits ω row k : ℝ) |
      MeasurableSpace.comap (E.info k) inferInstance]) ω = _
  change (μ[fun ω => w k (E.info k ω) row*(E.visits ω row k : ℝ) |
      MeasurableSpace.comap (E.info k) inferInstance]) ω =
      w k (E.info k ω) row * (μ[fun ω => (E.visits ω row k : ℝ) |
        MeasurableSpace.comap (E.info k) inferInstance]) ω at hp
  change (μ[fun ω => (E.visits ω row k : ℝ) |
      MeasurableSpace.comap (E.info k) inferInstance]) ω =
      nominalVisits (E.policy k (E.info k ω)) (E.transition k (E.info k ω)) s₀ T row at hc
  exact hp.trans (congrArg (w k (E.info k ω) row * ·) hc)

/-- Both source conditional all-row identities before applying C.3. -/
theorem conditional_realizedEpisode
    (w : Weight (Info := Info) (S := S) (A := A))
    (hw : ∀ k row, Measurable (fun i => w k i row))
    (hb : ∀ k i row, 0 ≤ w k i row ∧ w k i row ≤ 1) (k : ℕ) :
    μ[E.realizedEpisode w k | MeasurableSpace.comap (E.info k) inferInstance] =ᵐ[μ]
      E.nominalEpisode w T k := by
  have hsum := condExp_finset_sum (s := Finset.univ)
    (f := fun row ω => w k (E.info k ω) row*(E.visits ω row k : ℝ))
    (fun row _ => E.weighted_count_integrable w hw hb k row)
    (MeasurableSpace.comap (E.info k) inferInstance)
  simp only [Finset.sum_fn] at hsum
  have hall : ∀ᵐ ω ∂μ, ∀ row : S × A,
      (μ[fun ω => w k (E.info k ω) row*(E.visits ω row k : ℝ) |
        MeasurableSpace.comap (E.info k) inferInstance]) ω =
        w k (E.info k ω) row*
          nominalVisits (E.policy k (E.info k ω)) (E.transition k (E.info k ω)) s₀ T row :=
    ae_all_iff.2 fun row => E.conditional_weighted_row w hw hb k row
  filter_upwards [hsum, hall] with ω hs hall
  change (μ[E.realizedEpisode w k | MeasurableSpace.comap (E.info k) inferInstance]) ω = _
  change (μ[fun ω => ∑ row, w k (E.info k ω) row*(E.visits ω row k : ℝ) |
      MeasurableSpace.comap (E.info k) inferInstance]) ω = _
  rw [hs]
  exact Finset.sum_congr rfl fun row _ => hall row

lemma nominalEpisode_mono (w : Weight (Info := Info) (S := S) (A := A))
    (hb : ∀ k i row, 0 ≤ w k i row ∧ w k i row ≤ 1)
    {L : ℕ} (hLT : L ≤ T) (k : ℕ) (ω : Ω) :
    E.nominalEpisode w L k ω ≤ E.nominalEpisode w T k ω := by
  exact Finset.sum_le_sum fun row _ =>
    mul_le_mul_of_nonneg_left (nominalVisits_mono _ _ _ hLT row) (hb _ _ _).1

lemma realized_low_bounds (k : ℕ) (ω : Ω) :
    0 ≤ E.realizedEpisode E.lowWeight k ω ∧ E.realizedEpisode E.lowWeight k ω ≤ T := by
  have h := Counts.low_episode_bounds (rows := Finset.univ) (v := E.visits ω)
    (fun j => le_of_eq (E.visits_total ω j)) k
  simpa [realizedEpisode, lowWeight, E.count_prefix, visits, Counts.before,
    ite_mul] using h

lemma realized_log_bounds (hT : 0 < T) (k : ℕ) (ω : Ω) :
    0 ≤ E.realizedEpisode E.logWeight k ω ∧ E.realizedEpisode E.logWeight k ω ≤ 1 := by
  have h := Counts.high_log_episode_le_one (rows := Finset.univ) (v := E.visits ω)
    hT (fun j => le_of_eq (E.visits_total ω j)) k
  simpa [realizedEpisode, logWeight, E.count_prefix, visits, Counts.before,
    ite_mul, div_eq_mul_inv, mul_comm] using h

/-- Adaptation of the realized row charge to the actual analytic filtration. -/
lemma realized_stronglyMeasurable
    (w : Weight (Info := Info) (S := S) (A := A))
    (hw : ∀ k row, Measurable (fun i => w k i row))
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (E.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (E.path k)) (k : ℕ) :
    StronglyMeasurable[ℱ (k+1)] (E.realizedEpisode w k) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro row _
  have hwsm : StronglyMeasurable[MeasurableSpace.comap (E.info k) inferInstance]
      (fun ω => w k (E.info k ω) row) :=
    (hw k row).stronglyMeasurable.comp_measurable (Measurable.of_comap_le le_rfl)
  rw [hinfo] at hwsm
  have hc : StronglyMeasurable[ℱ (k+1)] (fun ω => (E.visits ω row k : ℝ)) :=
    ((Measurable.of_discrete : Measurable (fun p : Trajectory S A T =>
      (visitCount row T p : ℝ))).comp (hpath k)).stronglyMeasurable
  exact (hwsm.mono (ℱ.mono (Nat.le_succ k))).mul hc

/-- The partial-stage nominal total is dominated by the actual predictable means. -/
theorem totalNominal_le_predictable
    (w : Weight (Info := Info) (S := S) (A := A))
    (hw : ∀ k row, Measurable (fun i => w k i row))
    (hb : ∀ k i row, 0 ≤ w k i row ∧ w k i row ≤ 1)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (E.info k) inferInstance = ℱ k)
    (K L : ℕ) (hLT : L ≤ T) :
    E.totalNominal w K L ≤ᵐ[μ] fun ω =>
      ∑ k ∈ Finset.range K, Paper36.Posterior.predictableMean (μ := μ) ℱ
        (E.realizedEpisode w) k ω := by
  have hall : ∀ᵐ ω ∂μ, ∀ k,
      Paper36.Posterior.predictableMean (μ := μ) ℱ (E.realizedEpisode w) k ω =
        E.nominalEpisode w T k ω := by
    apply ae_all_iff.2
    intro k
    have hc := E.conditional_realizedEpisode w hw hb k
    rw [hinfo] at hc
    exact hc
  filter_upwards [hall] with ω hω
  apply Finset.sum_le_sum
  intro k _
  rw [hω k]
  exact E.nominalEpisode_mono w hb hLT k ω

/-- C.11 for actual trajectory counts. No aggregate occupancy bound is a premise. -/
theorem low_probability_bound (hT : 0 < T)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (E.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (E.path k))
    (K L : ℕ) (hLT : L ≤ T) {ell : ℝ} (hell : 0 < ell) :
    μ.real {ω | 4*(Fintype.card (S × A):ℝ)*T+2*T*ell <
      E.totalNominal E.lowWeight K L ω} ≤ Real.exp (-ell) := by
  have hc := Paper36.Posterior.predictable_to_realized (μ := μ) ℱ
    (E.realizedEpisode E.lowWeight) K (b := T) (Nat.cast_nonneg _) hell
    (fun k _ => E.realized_stronglyMeasurable E.lowWeight E.lowWeight_meas ℱ hinfo hpath k)
    (fun k _ => ae_of_all _ fun ω => E.realized_low_bounds k ω)
  have hm := E.totalNominal_le_predictable E.lowWeight E.lowWeight_meas E.lowWeight_bounds
    ℱ hinfo K L hLT
  have hsub : {ω | 4*(Fintype.card (S × A):ℝ)*T+2*T*ell < E.totalNominal E.lowWeight K L ω} ≤ᵐ[μ]
      {ω | 2*(∑ k ∈ Finset.range K, E.realizedEpisode E.lowWeight k ω)+2*T*ell <
        ∑ k ∈ Finset.range K, Paper36.Posterior.predictableMean (μ := μ) ℱ
          (E.realizedEpisode E.lowWeight) k ω} := by
    filter_upwards [hm] with ω hm hω
    have hz := E.totalRealized_low_le hT ω K
    change E.totalRealized E.lowWeight K ω ≤ _ at hz
    change _ < _ at hω ⊢
    change E.totalNominal E.lowWeight K L ω ≤ _ at hm
    change 2*E.totalRealized E.lowWeight K ω+2*T*ell < _
    linarith
  exact (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)).trans hc

/-- C.12 for actual trajectory counts and the frozen logarithmic potential. -/
theorem log_probability_bound (hT : 0 < T)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (E.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (E.path k))
    {K : ℕ} (hK : 1 ≤ K) (L : ℕ) (hLT : L ≤ T) {ell : ℝ} (hell : 0 < ell) :
    μ.real {ω | 4*(Fintype.card (S × A):ℝ)*Real.log (Real.exp 1*(K:ℝ)*T)+2*ell <
      E.totalNominal E.logWeight K L ω} ≤ Real.exp (-ell) := by
  have hc := Paper36.Posterior.predictable_to_realized (μ := μ) ℱ
    (E.realizedEpisode E.logWeight) K (b := 1) (by norm_num) hell
    (fun k _ => E.realized_stronglyMeasurable E.logWeight E.logWeight_meas ℱ hinfo hpath k)
    (fun k _ => ae_of_all _ fun ω => E.realized_log_bounds hT k ω)
  have hm := E.totalNominal_le_predictable E.logWeight E.logWeight_meas (E.logWeight_bounds hT)
    ℱ hinfo K L hLT
  have hsub : {ω | 4*(Fintype.card (S × A):ℝ)*Real.log (Real.exp 1*(K:ℝ)*T)+2*ell <
      E.totalNominal E.logWeight K L ω} ≤ᵐ[μ]
      {ω | 2*(∑ k ∈ Finset.range K, E.realizedEpisode E.logWeight k ω)+2*1*ell <
        ∑ k ∈ Finset.range K, Paper36.Posterior.predictableMean (μ := μ) ℱ
          (E.realizedEpisode E.logWeight) k ω} := by
    filter_upwards [hm] with ω hm hω
    have hz := E.totalRealized_log_le hT hK ω
    change _ < _ at hω ⊢
    change E.totalNominal E.logWeight K L ω ≤ _ at hm
    change 2*E.totalRealized E.logWeight K ω+2*1*ell < _
    linarith
  exact (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)).trans hc

/-- The actual selected physical-state Markov policy in each episode. -/
def selectedPolicy (ω : Ω) (k : ℕ) : Policy S A := E.policy k (E.info k ω)

def frozenCounts (ω : Ω) (k : ℕ) (row : S × A) : ℕ := E.count k (E.info k ω) row

section SourceHorizon
variable {H : ℕ} (F : EpisodeSystem μ Info S A (H+1) s₀)

/-- The low-count variable here is exactly the source's Y_lo in C.10. -/
theorem totalNominal_low_eq_Ylo (K : ℕ) (ω : Ω) :
    F.totalNominal F.lowWeight K H ω =
      HybridCharging.Ylo (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H := by
  unfold totalNominal nominalEpisode lowWeight nominalVisits HybridCharging.Ylo
    HybridCharging.nominalLow HybridCharging.nominalMass selectedPolicy frozenCounts
  apply Finset.sum_congr rfl
  intro k _
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro row _
  rw [F.transition_match]
  split_ifs <;> simp_all

/-- The high-count variable here is exactly the source's Y_hi in C.10. -/
theorem totalNominal_log_eq_Yhi (K : ℕ) (ω : Ω) :
    F.totalNominal F.logWeight K H ω =
      HybridCharging.Yhi (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H := by
  unfold totalNominal nominalEpisode logWeight nominalVisits HybridCharging.Yhi
    HybridCharging.nominalHigh HybridCharging.nominalMass selectedPolicy frozenCounts
  apply Finset.sum_congr rfl
  intro k _
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro row _
  rw [F.transition_match]
  split_ifs <;> simp_all [div_eq_mul_inv, mul_comm]

/-- The reward square-root variable uses the same actual frozen counts. -/
theorem totalNominal_sqrt_eq_Ysqrt (K : ℕ) (ω : Ω) :
    F.totalNominal F.sqrtWeight K H ω =
      HybridCharging.Ysqrt (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H := by
  unfold totalNominal nominalEpisode sqrtWeight nominalVisits HybridCharging.Ysqrt
    HybridCharging.nominalMass selectedPolicy frozenCounts
  apply Finset.sum_congr rfl
  intro k _
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro row _
  rw [F.transition_match]
  split_ifs <;> simp_all [div_eq_mul_inv, mul_comm]

lemma Ylo_integrable (K : ℕ) :
    Integrable (fun ω => HybridCharging.Ylo (F.selectedPolicy ω) (F.latent ω)
      s₀ (F.frozenCounts ω) K H) μ := by
  exact (F.totalNominal_integrable F.lowWeight F.lowWeight_meas F.lowWeight_bounds K H).congr
    (ae_of_all _ fun ω => F.totalNominal_low_eq_Ylo K ω)

lemma Yhi_integrable (K : ℕ) :
    Integrable (fun ω => HybridCharging.Yhi (F.selectedPolicy ω) (F.latent ω)
      s₀ (F.frozenCounts ω) K H) μ := by
  exact (F.totalNominal_integrable F.logWeight F.logWeight_meas (F.logWeight_bounds (by omega)) K H).congr
    (ae_of_all _ fun ω => F.totalNominal_log_eq_Yhi K ω)

lemma Ysqrt_integrable (K : ℕ) :
    Integrable (fun ω => HybridCharging.Ysqrt (F.selectedPolicy ω) (F.latent ω)
      s₀ (F.frozenCounts ω) K H) μ := by
  exact (F.totalNominal_integrable F.sqrtWeight F.sqrtWeight_meas (F.sqrtWeight_bounds (by omega)) K H).congr
    (ae_of_all _ fun ω => F.totalNominal_sqrt_eq_Ysqrt K ω)

lemma Ylo_nonneg (K : ℕ) (ω : Ω) :
    0 ≤ HybridCharging.Ylo (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H := by
  simpa only [F.totalNominal_low_eq_Ylo] using
    F.totalNominal_nonneg F.lowWeight F.lowWeight_bounds K H ω

lemma Yhi_nonneg (K : ℕ) (ω : Ω) :
    0 ≤ HybridCharging.Yhi (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H := by
  simpa only [F.totalNominal_log_eq_Yhi] using
    F.totalNominal_nonneg F.logWeight (F.logWeight_bounds (by omega)) K H ω

lemma Ysqrt_nonneg (K : ℕ) (ω : Ω) :
    0 ≤ HybridCharging.Ysqrt (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H := by
  simpa only [F.totalNominal_sqrt_eq_Ysqrt] using
    F.totalNominal_nonneg F.sqrtWeight (F.sqrtWeight_bounds (by omega)) K H ω

theorem integral_Ylo_le (K : ℕ) :
    (∫ ω, HybridCharging.Ylo (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H ∂μ) ≤
      2*(Fintype.card (S × A):ℝ)*(H+1) := by
  simpa only [F.totalNominal_low_eq_Ylo, Nat.cast_add, Nat.cast_one] using
    F.integral_low_le (by omega) K H (by omega)

theorem integral_Yhi_le {K : ℕ} (hK : 1 ≤ K) :
    (∫ ω, HybridCharging.Yhi (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H ∂μ) ≤
      2*(Fintype.card (S × A):ℝ)*Real.log (Real.exp 1*(K:ℝ)*(H+1)) := by
  simpa only [F.totalNominal_log_eq_Yhi, Nat.cast_add, Nat.cast_one] using
    F.integral_log_le (by omega) hK H (by omega)

theorem integral_Ysqrt_le (K : ℕ) :
    (∫ ω, HybridCharging.Ysqrt (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H ∂μ) ≤
      3*Real.sqrt ((Fintype.card (S × A):ℝ)*(K:ℝ)*(H+1)) := by
  simpa only [F.totalNominal_sqrt_eq_Ysqrt, Nat.cast_add, Nat.cast_one] using
    F.integral_sqrt_le (by omega) K H (by omega)

theorem Ylo_probability_bound
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (F.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (F.path k))
    (K : ℕ) {ell : ℝ} (hell : 0 < ell) :
    μ.real {ω | 4*(Fintype.card (S × A):ℝ)*(H+1)+2*(H+1)*ell <
      HybridCharging.Ylo (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H} ≤
      Real.exp (-ell) := by
  simpa only [F.totalNominal_low_eq_Ylo, Nat.cast_add, Nat.cast_one] using
    F.low_probability_bound (by omega) ℱ hinfo hpath K H (by omega) hell

theorem Yhi_probability_bound
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (F.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (F.path k))
    {K : ℕ} (hK : 1 ≤ K) {ell : ℝ} (hell : 0 < ell) :
    μ.real {ω | 4*(Fintype.card (S × A):ℝ)*Real.log (Real.exp 1*(K:ℝ)*(H+1))+2*ell <
      HybridCharging.Yhi (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H} ≤
      Real.exp (-ell) := by
  simpa only [F.totalNominal_log_eq_Yhi, Nat.cast_add, Nat.cast_one] using
    F.log_probability_bound (by omega) ℱ hinfo hpath hK H (by omega) hell

end SourceHorizon

end EpisodeSystem
end
end Paper36.StatisticalCounts
