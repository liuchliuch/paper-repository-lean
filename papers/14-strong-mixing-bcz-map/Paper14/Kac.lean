import Paper14.ReturnCombinatorics
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Measure Filter Set Function Topology
open scoped ENNReal
namespace Paper14
noncomputable section

lemma firstReturn_spec {α : Type*} {T : α → α} {Y : Set α} {x : α}
    (h : ∃ k, 0 < k ∧ T^[k] x ∈ Y) :
    0 < firstReturnTime T Y x ∧ T^[firstReturnTime T Y x] x ∈ Y := by
  rw [firstReturnTime_eq_find h]
  exact @Nat.find_spec (fun k => 0 < k ∧ T^[k] x ∈ Y) (Classical.decPred _) h

lemma firstReturn_le {α : Type*} {T : α → α} {Y : Set α} {x : α}
    {k : ℕ} (hk : 0 < k) (hx : T^[k] x ∈ Y) : firstReturnTime T Y x ≤ k := by
  let h : ∃ k, 0 < k ∧ T^[k] x ∈ Y := ⟨k, hk, hx⟩
  rw [firstReturnTime_eq_find h]
  exact @Nat.find_min' (fun k => 0 < k ∧ T^[k] x ∈ Y) (Classical.decPred _) h k ⟨hk, hx⟩

lemma firstReturn_eq_zero_iff {α : Type*} {T : α → α} {Y : Set α} {x : α} :
    firstReturnTime T Y x = 0 ↔ ¬ ∃ k, 0 < k ∧ T^[k] x ∈ Y := by
  constructor
  · intro hz he
    have h := (firstReturn_spec he).1
    omega
  · exact firstReturnTime_of_not_exists

lemma firstReturn_eq_succ_iff {α : Type*} {T : α → α} {Y : Set α} {x : α} {n : ℕ} :
    firstReturnTime T Y x = n + 1 ↔ T^[n + 1] x ∈ Y ∧
      ∀ k < n + 1, 0 < k → T^[k] x ∉ Y := by
  constructor
  · intro h
    have he : ∃ k, 0 < k ∧ T^[k] x ∈ Y := by
      by_contra hn
      have hz := firstReturnTime_of_not_exists hn
      omega
    have hs := firstReturn_spec he
    refine ⟨by simpa only [h] using hs.2, ?_⟩
    intro k hk hk0 hmem
    have hle := firstReturn_le hk0 hmem
    omega
  · rintro ⟨hmem, hmin⟩
    have hs := firstReturn_spec (T := T) (x := x) ⟨n + 1, by omega, hmem⟩
    have hle := firstReturn_le (by omega : 0 < n + 1) hmem
    have hge : n + 1 ≤ firstReturnTime T Y x := by
      by_contra hn
      exact hmin _ (by omega) hs.1 hs.2
    omega

lemma measurable_firstReturn {α : Type*} [MeasurableSpace α] {T : α → α} {Y : Set α}
    (hT : Measurable T) (hY : MeasurableSet Y) : Measurable (firstReturnTime T Y) := by
  classical
  apply measurable_to_countable'
  intro n
  change MeasurableSet {x | firstReturnTime T Y x = n}
  cases n with
  | zero =>
    simp only [firstReturn_eq_zero_iff, not_exists, not_and, setOf_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk => (hT.iterate k hY).compl
  | succ n =>
    simp only [firstReturn_eq_succ_iff, setOf_and, setOf_forall]
    exact (hT.iterate (n + 1) hY).inter
      (MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk =>
        MeasurableSet.iInter fun hk0 => (hT.iterate k hY).compl)

lemma measurable_inducedMap {α : Type*} [MeasurableSpace α] {T : α → α} {Y : Set α}
    (hT : Measurable T) (hY : MeasurableSet Y) : Measurable (inducedMap T Y) := by
  have hi : Measurable (fun p : ℕ × α => T^[p.1] p.2) :=
    measurable_from_prod_countable_right (fun n => hT.iterate n)
  exact hi.comp ((measurable_firstReturn hT hY).prodMk measurable_id)

lemma ae_return_exists {α : Type*} [MeasurableSpace α] {T : α → α} {Y : Set α}
    {μ : Measure α} [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hY : MeasurableSet Y) : ∀ᵐ x ∂μ, x ∈ Y → ∃ k, 0 < k ∧ T^[k] x ∈ Y := by
  filter_upwards [hT.conservative.ae_mem_imp_frequently_image_mem hY.nullMeasurableSet] with x hx hxy
  obtain ⟨k, hk, hmem⟩ := frequently_atTop.mp (hx hxy) 1
  exact ⟨k, by omega, hmem⟩

def avoidReturn {α : Type*} (T : α → α) (Y : Set α) (n : ℕ) : Set α :=
  {x | ∀ k < n, T^[k] x ∉ Y}

def returnSurvival {α : Type*} (T : α → α) (Y : Set α) (n : ℕ) : Set α :=
  {x ∈ Y | ∀ k, 0 < k → k ≤ n → T^[k] x ∉ Y}

lemma measurable_avoidReturn {α : Type*} [MeasurableSpace α] {T : α → α} {Y : Set α}
    (hT : Measurable T) (hY : MeasurableSet Y) (n : ℕ) : MeasurableSet (avoidReturn T Y n) := by
  simp only [avoidReturn, setOf_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk => (hT.iterate k hY).compl

lemma avoidReturn_antitone {α : Type*} (T : α → α) (Y : Set α) : Antitone (avoidReturn T Y) := by
  intro m n hmn x hx k hk
  exact hx k (lt_of_lt_of_le hk hmn)

lemma avoidReturn_succ {α : Type*} (T : α → α) (Y : Set α) (n : ℕ) :
    avoidReturn T Y (n + 1) = Yᶜ ∩ T ⁻¹' avoidReturn T Y n := by
  ext x
  constructor
  · intro hx
    refine ⟨hx 0 (by omega), ?_⟩
    intro k hk
    simpa only [iterate_succ_apply] using hx (k + 1) (by omega)
  · rintro ⟨hx, htail⟩ k hk
    cases k with
    | zero => exact hx
    | succ k => simpa only [iterate_succ_apply] using htail k (by omega)

lemma survival_partition {α : Type*} (T : α → α) (Y : Set α) (n : ℕ) :
    returnSurvival T Y n = (T ⁻¹' avoidReturn T Y n) ∩ Y := by
  ext x
  constructor
  · rintro ⟨hx, htail⟩
    refine ⟨?_, hx⟩
    intro k hk
    simpa only [iterate_succ_apply] using htail (k + 1) (by omega) (by omega)
  · rintro ⟨htail, hx⟩
    refine ⟨hx, ?_⟩
    intro k hk0 hkn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simpa only [iterate_succ_apply] using htail j (by omega)

lemma survival_measure_step {α : Type*} [MeasurableSpace α] {T : α → α} {Y : Set α}
    {μ : Measure α} (hT : MeasurePreserving T μ μ) (hY : MeasurableSet Y) (n : ℕ) :
    μ (returnSurvival T Y n) + μ (avoidReturn T Y (n + 1)) = μ (avoidReturn T Y n) := by
  rw [survival_partition, avoidReturn_succ, inter_comm Yᶜ]
  rw [← Set.diff_eq, measure_inter_add_diff _ hY]
  exact hT.measure_preimage (measurable_avoidReturn hT.measurable hY n).nullMeasurableSet

lemma never_hit_null {α : Type*} [MeasurableSpace α] {T : α → α} {Y : Set α}
    {μ : Measure α} [IsFiniteMeasure μ] (hT : Ergodic T μ)
    (hY : MeasurableSet Y) (hpos : 0 < μ Y) :
    μ (⋂ n : ℕ, avoidReturn T Y n) = 0 := by
  let S : Set α := ⋃ n : ℕ, (T^[n]) ⁻¹' Y
  have hS : MeasurableSet S := MeasurableSet.iUnion fun n => hT.measurable.iterate n hY
  have hpre : T ⁻¹' S ⊆ S := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n + 1, by simpa only [iterate_succ_apply] using hn⟩
  have hYS : Y ⊆ S := by
    intro x hx
    exact mem_iUnion.mpr ⟨0, hx⟩
  have hSuniv : S =ᵐ[μ] univ := by
    rcases hT.ae_empty_or_univ_of_preimage_ae_le hS.nullMeasurableSet
      (Eventually.of_forall hpre) with hempty | hall
    · have hz : μ S = 0 := (measure_congr hempty).trans measure_empty
      exact False.elim (not_le_of_gt hpos (hz ▸ measure_mono hYS))
    · exact hall
  have hcomp : (⋂ n : ℕ, avoidReturn T Y n) = Sᶜ := by
    ext x
    simp only [mem_iInter, avoidReturn, mem_setOf_eq, S, mem_compl_iff,
      mem_iUnion, mem_preimage, not_exists]
    constructor
    · intro hx n
      exact hx (n + 1) n (by omega)
    · intro hx n k hk
      exact hx k
  rw [hcomp]
  calc μ Sᶜ = μ (univᶜ : Set α) := measure_congr hSuniv.compl
       _ = 0 := by simp

lemma avoidReturn_measure_tendsto_zero {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {μ : Measure α} [IsFiniteMeasure μ]
    (hT : Ergodic T μ) (hY : MeasurableSet Y) (hpos : 0 < μ Y) :
    Tendsto (fun n : ℕ => μ (avoidReturn T Y n)) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (measurable_avoidReturn hT.measurable hY n).nullMeasurableSet)
    (avoidReturn_antitone T Y) ⟨0, measure_ne_top μ _⟩
  simpa only [Function.comp_def, never_hit_null hT hY hpos] using h

lemma survival_measure_sum {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hY : MeasurableSet Y) (hpos : 0 < μ Y) :
    (∑' n : ℕ, μ (returnSurvival T Y n)) = 1 := by
  have hpartial (N : ℕ) : (∑ n ∈ Finset.range N, μ (returnSurvival T Y n)) +
      μ (avoidReturn T Y N) = 1 := by
    induction N with
    | zero => simp [avoidReturn]
    | succ N ih =>
      rw [Finset.sum_range_succ, add_assoc, survival_measure_step hT.toMeasurePreserving hY N]
      exact ih
  have hsum : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, μ (returnSurvival T Y n))
      atTop (𝓝 (∑' n : ℕ, μ (returnSurvival T Y n))) :=
    ENNReal.summable.hasSum.tendsto_sum_nat
  have hboth := hsum.add (avoidReturn_measure_tendsto_zero hT hY hpos)
  have hconst : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, μ (returnSurvival T Y n)) +
      μ (avoidReturn T Y N)) atTop (𝓝 1) := by simpa only [hpartial] using (tendsto_const_nhds (x := (1 : ℝ≥0∞)))
  simpa only [add_zero] using (tendsto_nhds_unique hboth hconst)

lemma tail_survival_measure {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {μ : Measure α} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hY : MeasurableSet Y) (n : ℕ) :
    (μ.restrict Y) {x | n < firstReturnTime T Y x} = μ (returnSurvival T Y n) := by
  have hset : MeasurableSet {x | n < firstReturnTime T Y x} :=
    measurableSet_lt measurable_const (measurable_firstReturn hT.measurable hY)
  rw [Measure.restrict_apply hset]
  apply measure_congr
  filter_upwards [ae_return_exists hT hY] with x hx
  apply propext
  change (n < firstReturnTime T Y x ∧ x ∈ Y) ↔ x ∈ Y ∧ _
  constructor
  · rintro ⟨hn, hxy⟩
    refine ⟨hxy, ?_⟩
    intro k hk0 hkn hmem
    have hle := firstReturn_le hk0 hmem
    omega
  · rintro ⟨hxy, htail⟩
    have hs := firstReturn_spec (hx hxy)
    refine ⟨?_, hxy⟩
    by_contra hn
    exact htail _ hs.1 (by omega) hs.2

lemma nat_cast_eq_tsum_indicators (r : ℕ) :
    (r : ℝ≥0∞) = ∑' n : ℕ, if n < r then (1 : ℝ≥0∞) else 0 := by
  symm
  rw [tsum_eq_sum (s := Finset.range r)]
  · have heq : (∑ n ∈ Finset.range r, if n < r then (1 : ℝ≥0∞) else 0) =
        ∑ _n ∈ Finset.range r, (1 : ℝ≥0∞) :=
      Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_range.mp hn))
    rw [heq]
    simp
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp [not_lt.mpr hn]

/-- Kac's formula for an ergodic probability-preserving map, proved by
summing survival probabilities and the decreasing avoidance sets. -/
theorem kac_lintegral {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hY : MeasurableSet Y) (hpos : 0 < μ Y) :
    (∫⁻ x in Y, (firstReturnTime T Y x : ℝ≥0∞) ∂μ) = 1 := by
  classical
  have hmeas (n : ℕ) : MeasurableSet {x | n < firstReturnTime T Y x} :=
    measurableSet_lt measurable_const (measurable_firstReturn hT.measurable hY)
  calc
    _ = ∫⁻ x in Y, ∑' n : ℕ,
        {y | n < firstReturnTime T Y y}.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
      apply lintegral_congr_ae
      exact Eventually.of_forall (fun x => by simpa only [indicator_apply, mem_setOf_eq] using nat_cast_eq_tsum_indicators (firstReturnTime T Y x))
    _ = ∑' n : ℕ, ∫⁻ x in Y,
        {y | n < firstReturnTime T Y y}.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ :=
      lintegral_tsum (fun n => (measurable_const.indicator (hmeas n)).aemeasurable)
    _ = ∑' n : ℕ, (μ.restrict Y) {x | n < firstReturnTime T Y x} := by
      congr 1
      funext n
      rw [lintegral_indicator (hmeas n)]
      simp
    _ = ∑' n : ℕ, μ (returnSurvival T Y n) :=
      tsum_congr (fun n => tail_survival_measure hT.toMeasurePreserving hY n)
    _ = 1 := survival_measure_sum hT hY hpos

theorem kac_integral {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hY : MeasurableSet Y) (hpos : 0 < μ Y) :
    (∫ x in Y, (firstReturnTime T Y x : ℝ) ∂μ) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun x => Nat.cast_nonneg _))
    ((measurable_from_nat.comp (measurable_firstReturn hT.measurable hY)).aestronglyMeasurable)]
  simpa only [ENNReal.ofReal_natCast, ENNReal.toReal_one] using
    congrArg ENNReal.toReal (kac_lintegral hT hY hpos)

/-- The previously open, independently stated Kac contract. -/
theorem KacFirstMoment : KacFirstMomentStatement := by
  intro α _ T μ Y hprob hT hY hpos
  letI := hprob
  exact kac_integral hT hY hpos

end
end Paper14
