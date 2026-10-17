import CalibrationDistance.Deterministic
import CalibrationDistance.ProtocolLoss

/-! Injection of the outcome-prefix deterministic strategy class into behavioral
kernels, and the pathwise support identity under arbitrary randomized adversaries. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CalibrationDistance.Protocol

noncomputable section

def deterministicPrediction {T : ℕ} (F : DeterministicForecaster T)
    (n : ℕ) (h : History n) : Probability :=
  if hn : n < T then F ⟨n, hn⟩ (binaryOutcomes n h)
  else ⟨1 / 2, by constructor <;> norm_num⟩

theorem measurable_deterministicPrediction {T : ℕ} (F : DeterministicForecaster T) (n : ℕ) :
    Measurable (deterministicPrediction F n) := by
  by_cases hn : n < T
  · change Measurable (fun h : History n => deterministicPrediction F n h)
    simp only [deterministicPrediction, dif_pos hn]
    exact (measurable_of_countable (F ⟨n, hn⟩)).comp (measurable_binaryOutcomes n)
  · change Measurable (fun h : History n => deterministicPrediction F n h)
    simp only [deterministicPrediction, dif_neg hn]
    exact measurable_const

def deterministicBehavioral {T : ℕ} (F : DeterministicForecaster T) : BehavioralForecaster where
  kernel n := Kernel.deterministic (deterministicPrediction F n) (measurable_deterministicPrediction F n)
  markov n := inferInstance

@[simp] theorem deterministicBehavioral_apply {T : ℕ} (F : DeterministicForecaster T)
    (n : ℕ) (h : History n) :
    (deterministicBehavioral F).kernel n h = Measure.dirac (deterministicPrediction F n h) := rfl

theorem deterministicBehavioral_mean {T : ℕ} (F : DeterministicForecaster T)
    (n : ℕ) (h : History n) :
    mean (deterministicBehavioral F) n h = (deterministicPrediction F n h : ℝ) := by
  simp [mean]

theorem deterministicBehavioral_variance {T : ℕ} (F : DeterministicForecaster T)
    (n : ℕ) (h : History n) : variance (deterministicBehavioral F) n h = 0 := by
  simp [variance, deterministicBehavioral_mean]

def FollowsForecaster {T : ℕ} (F : DeterministicForecaster T) : (n : ℕ) → History n → Prop
  | 0, _ => True
  | n+1, h => FollowsForecaster F n h.1 ∧
      (h.2.1 : ℝ) = (deterministicPrediction F n h.1 : ℝ)

theorem measurableSet_followsForecaster {T : ℕ} (F : DeterministicForecaster T) :
    ∀ n, MeasurableSet {h : History n | FollowsForecaster F n h}
  | 0 => MeasurableSet.univ
  | n+1 => by
    change MeasurableSet {h : History n × Round |
      FollowsForecaster F n h.1 ∧ (h.2.1 : ℝ) = (deterministicPrediction F n h.1 : ℝ)}
    exact ((measurableSet_followsForecaster F n).preimage measurable_fst).inter
      (measurableSet_eq_fun (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd))
        (measurable_subtype_coe.comp ((measurable_deterministicPrediction F n).comp measurable_fst)))

/-- The deterministic forecast prescribed by F is obeyed at every realized round,
even when the simultaneous adversary randomizes. -/
theorem ae_followsForecaster {T : ℕ} (F : DeterministicForecaster T)
    (B : RandomizedAdversary) : ∀ n,
    ∀ᵐ h ∂law (deterministicBehavioral F) B n, FollowsForecaster F n h
  | 0 => Filter.Eventually.of_forall (fun _ => trivial)
  | n+1 => by
    change ∀ᵐ h ∂(law (deterministicBehavioral F) B n).compProd
      (transition (deterministicBehavioral F) B n), FollowsForecaster F (n+1) h
    apply Measure.ae_compProd_of_ae_ae (measurableSet_followsForecaster F (n+1))
    filter_upwards [ae_followsForecaster F B n] with h hh
    rw [transition_apply, deterministicBehavioral_apply, Measure.dirac_prod]
    have hm : MeasurableSet {r : Round | FollowsForecaster F (n+1) (h,r)} :=
      (measurableSet_followsForecaster F (n+1)).preimage measurable_prodMk_left
    apply (ae_map_iff measurable_prodMk_left.aemeasurable hm).mpr
    exact Filter.Eventually.of_forall (fun _ => ⟨hh, rfl⟩)

@[simp] theorem roundAt_castSucc (n : ℕ) (h : History (n+1)) (i : Fin n) :
    roundAt (n+1) h i.castSucc = roundAt n h.1 i := by simp [roundAt]

@[simp] theorem roundAt_last (n : ℕ) (h : History (n+1)) :
    roundAt (n+1) h (Fin.last n) = h.2 := by simp [roundAt]

theorem followsForecaster_forecasts {T : ℕ} (F : DeterministicForecaster T) :
    ∀ n (hn : n ≤ T) (h : History n), FollowsForecaster F n h → ∀ i : Fin n,
      forecasts n h i =
        (F ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
          (fun j => binaryOutcomes n h ⟨j.val, lt_trans j.isLt i.isLt⟩) : ℝ)
  | 0, hn, h, hh, i => Fin.elim0 i
  | n+1, hn, h, hh, i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [forecasts, roundAt_last]
      rw [hh.2]
      have hnT : n < T := lt_of_lt_of_le (Nat.lt_succ_self n) hn
      simp only [deterministicPrediction, dif_pos hnT]
      congr 2
      funext j
      exact (roundAt_castSucc n h j).symm |> congrArg Prod.snd
    · have hj := followsForecaster_forecasts F n (Nat.le_of_succ_le hn) h.1 hh.1 j
      simp only [forecasts] at hj
      simp only [forecasts, roundAt_castSucc]
      rw [hj]
      congr 2
      funext k
      exact (roundAt_castSucc n h ⟨k.val, lt_trans k.isLt j.isLt⟩).symm |> congrArg Prod.snd

theorem ae_forecasts_eq_deterministicPath {T : ℕ} (F : DeterministicForecaster T)
    (B : RandomizedAdversary) :
    ∀ᵐ h ∂law (deterministicBehavioral F) B T,
      forecasts T h = deterministicPath F (binaryOutcomes T h) := by
  filter_upwards [ae_followsForecaster F B T] with h hh
  funext i
  exact followsForecaster_forecasts F T le_rfl h hh i

theorem ae_pathLoss_eq_deterministicLoss {T : ℕ} (F : DeterministicForecaster T)
    (B : RandomizedAdversary) :
    ∀ᵐ h ∂law (deterministicBehavioral F) B T,
      pathLoss T h = deterministicLoss F (binaryOutcomes T h) := by
  filter_upwards [ae_forecasts_eq_deterministicPath F B] with h hh
  unfold pathLoss deterministicLoss
  rw [hh]
  rfl

/-- A deterministic uniform pathwise guarantee transfers to the actual behavioral
trajectory expectation against every past-adaptive adversary. -/
theorem integral_calDist_deterministic_le {T : ℕ} (F : DeterministicForecaster T)
    (B : RandomizedAdversary) {C : ℝ} (hC : ∀ y, deterministicLoss F y ≤ C) :
    (∫ h, pathLoss T h ∂law (deterministicBehavioral F) B T) ≤ C := by
  calc
    (∫ h, pathLoss T h ∂law (deterministicBehavioral F) B T) ≤
        ∫ _h : History T, C ∂law (deterministicBehavioral F) B T := by
      apply integral_mono_ae (integrable_pathLoss _ _ _) (integrable_const C)
      filter_upwards [ae_pathLoss_eq_deterministicLoss F B] with h hh
      rw [hh]
      exact hC _
    _ = C := by simp

theorem expectedCalDist_deterministic_le {T : ℕ} (F : DeterministicForecaster T)
    (A : Adversary) {C : ℝ} (hC : ∀ y, deterministicLoss F y ≤ C) :
    expectedCalDist (deterministicBehavioral F) A T ≤ C := by
  exact integral_calDist_deterministic_le F A.randomized hC

theorem exists_string_of_integral_calDist_le {T : ℕ} (F : DeterministicForecaster T)
    (B : RandomizedAdversary) {C : ℝ}
    (hC : C ≤ ∫ h, pathLoss T h ∂law (deterministicBehavioral F) B T) :
    ∃ y, C ≤ deterministicLoss F y := by
  classical
  by_contra h
  have hlt : ∀ y, deterministicLoss F y < C := by
    intro y
    exact lt_of_not_ge (fun hy => h ⟨y, hy⟩)
  obtain ⟨ymax, hymax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin T → Bool)) (deterministicLoss F) Finset.univ_nonempty
  have hb : (∫ h, pathLoss T h ∂law (deterministicBehavioral F) B T) ≤ deterministicLoss F ymax :=
    integral_calDist_deterministic_le F B (fun y => hymax.2 y (Finset.mem_univ y))
  exact (not_lt_of_ge (hC.trans hb)) (hlt ymax)

/-- Any expected lower bound for a deterministic forecaster yields a single fixed
binary string. The finite maximum makes this extraction independent of a tape. -/
theorem exists_string_of_expectedCalDist_le {T : ℕ} (F : DeterministicForecaster T)
    (A : Adversary) {C : ℝ}
    (hC : C ≤ expectedCalDist (deterministicBehavioral F) A T) :
    ∃ y, C ≤ deterministicLoss F y := by
  exact exists_string_of_integral_calDist_le F A.randomized hC

end

end CalibrationDistance.Protocol
