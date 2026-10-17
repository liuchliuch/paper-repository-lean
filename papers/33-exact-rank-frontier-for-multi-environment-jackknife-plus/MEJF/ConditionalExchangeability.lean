import MEJF.Exchangeability
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Conditioning the comparison count on an invariant countable statistic

The statistic may be the unordered multiset of environment sizes. Conditional
probability is constructed by the exact cell-probability ratio (zero on null
cells). The all-subset integral identity verifies that this is a genuine
conditional probability version; the conditional bound is derived, not assumed.
-/
namespace MEJF.ConditionalExchangeability

open Finset MeasureTheory MEJF.Exchangeability
noncomputable section
attribute [local instance 2000] Classical.propDecidable

variable {I B C : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace B]
variable [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]

/-- Exact discrete conditional probability, with the usual zero-mass convention. -/
def conditionalRatio (μ : Measure (I → B)) (H : (I → B) → I → Prop)
    (M : (I → B) → C) (i : I) (c : C) : ℝ :=
  μ.real {z | H z i ∧ M z = c} / μ.real {z | M z = c}

lemma measurable_cell (M : (I → B) → C) (hM : Measurable M) (c : C) :
    MeasurableSet {z | M z = c} := (measurableSet_singleton c).preimage hM

lemma count_integrable (μ : Measure (I → B)) [IsProbabilityMeasure μ]
    (H : (I → B) → I → Prop) (hH : ∀ i, MeasurableSet {z | H z i}) :
    Integrable (fun z => ((univ.filter (H z)).card : ℝ)) μ := by
  have heq : (fun z => ((univ.filter (H z)).card : ℝ)) =
      fun z => ∑ i, Set.indicator {z | H z i} (fun _ => (1 : ℝ)) z := by
    funext z
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Finset.sum_boole]
  rw [heq]
  exact integrable_finset_sum _ (fun i _ => (integrable_const (1 : ℝ)).indicator (hH i))

/-- The invariant cell is a common label event, so localized failure events
retain equal marginal probabilities under block exchangeability. -/
lemma cell_probability_eq (μ : Measure (I → B)) (hex : Exchangeable μ)
    (H : (I → B) → I → Prop) (hH : ∀ i, MeasurableSet {z | H z i}) (heq : Equivariant H)
    (M : (I → B) → C) (hM : Measurable M)
    (hinv : ∀ e z, M (relabel e z) = M z) (c : C) (i j : I) :
    μ.real {z | H z i ∧ M z = c} = μ.real {z | H z j ∧ M z = c} := by
  apply event_probability_eq μ hex (fun z i => H z i ∧ M z = c)
    (fun i => (hH i).inter (measurable_cell M hM c))
  intro e z k
  change (H (relabel e z) (e k) ∧ M (relabel e z) = c) ↔ (H z k ∧ M z = c)
  rw [heq e z k, hinv e z]

/-- The weighted cell count gives the needed factor of the cell probability. -/
theorem cell_probability_mul_le (μ : Measure (I → B)) [IsProbabilityMeasure μ]
    (hex : Exchangeable μ) (H : (I → B) → I → Prop)
    (hH : ∀ i, MeasurableSet {z | H z i}) (heq : Equivariant H)
    (M : (I → B) → C) (hM : Measurable M) (hinv : ∀ e z, M (relabel e z) = M z)
    (s : C → ℕ) (hcount : ∀ z, (univ.filter (H z)).card ≤ s (M z)) (i : I) (c : C) :
    μ.real {z | H z i ∧ M z = c} ≤
      ((s c : ℝ) / Fintype.card I) * μ.real {z | M z = c} := by
  let G : (I → B) → I → Prop := fun z i => H z i ∧ M z = c
  have hG : ∀ i, MeasurableSet {z | G z i} := fun i => (hH i).inter (measurable_cell M hM c)
  let b : (I → B) → ℝ := Set.indicator {z | M z = c} (fun _ => (s c : ℝ))
  have hb : Integrable b μ := (integrable_const _).indicator (measurable_cell M hM c)
  have hle : (∫ z, ((univ.filter (G z)).card : ℝ) ∂μ) ≤
      (s c : ℝ) * μ.real {z | M z = c} := by
    calc
      _ ≤ ∫ z, b z ∂μ := by
        apply integral_mono (count_integrable μ G hG) hb
        intro z
        by_cases hz : M z = c
        · simpa [G, b, hz] using (Nat.cast_le (α := ℝ)).mpr (hcount z)
        · simp [G, b, hz]
      _ = _ := by
        simp only [b, integral_indicator_const _ (measurable_cell M hM c), smul_eq_mul]
        ring
  have hN : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  have havg := probability_eq_average_count μ G hG i
    (fun j => cell_probability_eq μ hex H hH heq M hM hinv c j i)
  calc
    _ = (∫ z, ((univ.filter (G z)).card : ℝ) ∂μ) / Fintype.card I := havg
    _ ≤ ((s c : ℝ) * μ.real {z | M z = c}) / Fintype.card I :=
      div_le_div_of_nonneg_right hle hN.le
    _ = _ := by ring

/-- Each actual conditional cell probability obeys the exact count bound,
including null cells, whose conditional ratio is zero by definition. -/
theorem conditionalRatio_le (μ : Measure (I → B)) [IsProbabilityMeasure μ]
    (hex : Exchangeable μ) (H : (I → B) → I → Prop)
    (hH : ∀ i, MeasurableSet {z | H z i}) (heq : Equivariant H)
    (M : (I → B) → C) (hM : Measurable M) (hinv : ∀ e z, M (relabel e z) = M z)
    (s : C → ℕ) (hcount : ∀ z, (univ.filter (H z)).card ≤ s (M z)) (i : I) (c : C) :
    conditionalRatio μ H M i c ≤ (s c : ℝ) / Fintype.card I := by
  by_cases hc : μ.real {z | M z = c} = 0
  · simp only [conditionalRatio, hc, div_zero]
    positivity
  · have hpos : 0 < μ.real {z | M z = c} :=
      lt_of_le_of_ne (measureReal_nonneg) (Ne.symm hc)
    apply (div_le_iff₀ hpos).mpr
    exact cell_probability_mul_le μ hex H hH heq M hM hinv s hcount i c

lemma conditionalRatio_nonneg (μ : Measure (I → B)) (H : (I → B) → I → Prop)
    (M : (I → B) → C) (i : I) (c : C) : 0 ≤ conditionalRatio μ H M i c :=
  div_nonneg measureReal_nonneg measureReal_nonneg

lemma conditionalRatio_le_one (μ : Measure (I → B)) [IsProbabilityMeasure μ]
    (H : (I → B) → I → Prop) (M : (I → B) → C) (i : I) (c : C) :
    conditionalRatio μ H M i c ≤ 1 := by
  have hnum : μ.real {z | H z i ∧ M z = c} ≤ μ.real {z | M z = c} :=
    measureReal_mono (fun _ h => h.2)
  by_cases hc : μ.real {z | M z = c} = 0
  · simp only [conditionalRatio, hc, div_zero, zero_le_one]
  · exact (div_le_one (lt_of_le_of_ne measureReal_nonneg (Ne.symm hc))).mpr hnum

/-- The ratio cancels on every cell, including null cells by event monotonicity. -/
lemma conditionalRatio_mul_cell (μ : Measure (I → B)) [IsProbabilityMeasure μ]
    (H : (I → B) → I → Prop) (M : (I → B) → C) (i : I) (c : C) :
    conditionalRatio μ H M i c * μ.real {z | M z = c} = μ.real {z | H z i ∧ M z = c} := by
  by_cases hc : μ.real {z | M z = c} = 0
  · have hz : μ.real {z | H z i ∧ M z = c} = 0 :=
      le_antisymm ((measureReal_mono (μ := μ) (fun _ h => h.2)).trans_eq hc) measureReal_nonneg
    simp only [conditionalRatio, hc, hz, div_zero, mul_zero]
  · exact div_mul_cancel₀ _ hc

lemma conditionalRatio_integrable (μ : Measure (I → B)) [IsProbabilityMeasure μ]
    (H : (I → B) → I → Prop) (M : (I → B) → C) (hM : Measurable M) (i : I) :
    Integrable (fun z => conditionalRatio μ H M i (M z)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_of_countable (conditionalRatio μ H M i)).comp hM).aestronglyMeasurable
  filter_upwards [] with z
  change ‖conditionalRatio μ H M i (M z)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (conditionalRatio_nonneg μ H M i _)]
  exact conditionalRatio_le_one μ H M i _

/-- The defining conditional-integral identity holds on every statistic cell. -/
lemma conditionalRatio_setIntegral_cell (μ : Measure (I → B)) [IsProbabilityMeasure μ]
    (H : (I → B) → I → Prop) (M : (I → B) → C) (hM : Measurable M) (i : I) (c : C) :
    (∫ z in {z | M z = c}, conditionalRatio μ H M i (M z) ∂μ) =
      μ.real {z | H z i ∧ M z = c} := by
  calc
    _ = ∫ _ in {z | M z = c}, conditionalRatio μ H M i c ∂μ :=
      setIntegral_congr_fun (measurable_cell M hM c) (fun z hz => by rw [hz])
    _ = conditionalRatio μ H M i c * μ.real {z | M z = c} := by
      simp only [setIntegral_const, smul_eq_mul]
      ring
    _ = _ := conditionalRatio_mul_cell μ H M i c

/-- An exact conditional-probability version: its integral agrees with the event
indicator on the preimage of every subset of the countable statistic space. -/
theorem conditionalRatio_setIntegral (μ : Measure (I → B)) [IsProbabilityMeasure μ]
    (H : (I → B) → I → Prop) (hH : ∀ i, MeasurableSet {z | H z i})
    (M : (I → B) → C) (hM : Measurable M) (i : I) (D : Set C) :
    (∫ z in M ⁻¹' D, conditionalRatio μ H M i (M z) ∂μ) =
      μ.real {z | H z i ∧ M z ∈ D} := by
  let cells : D → Set (I → B) := fun c => {z | M z = c.val}
  have hcells : ∀ c, MeasurableSet (cells c) := fun c => measurable_cell M hM c.val
  have hd : Pairwise (fun c d => Disjoint (cells c) (cells d)) := by
    intro c d hcd
    rw [Set.disjoint_left]
    intro z hzc hzd
    apply hcd
    exact Subtype.ext (hzc.symm.trans hzd)
  have hU : (⋃ c : D, cells c) = M ⁻¹' D := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_preimage, cells, Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, hc⟩
      exact hc.symm ▸ c.property
    · intro hz
      exact ⟨⟨M z, hz⟩, rfl⟩
  have hq := integral_iUnion hcells hd (conditionalRatio_integrable μ H M hM i).integrableOn
  have hind : Integrable (Set.indicator {z | H z i} (fun _ => (1 : ℝ))) μ :=
    (integrable_const _).indicator (hH i)
  have hevent := integral_iUnion hcells hd hind.integrableOn
  rw [hU] at hq hevent
  rw [hq]
  calc
    _ = ∑' c : D, ∫ z in cells c, Set.indicator {z | H z i} (fun _ => (1 : ℝ)) z ∂μ := by
      apply tsum_congr
      intro c
      rw [conditionalRatio_setIntegral_cell μ H M hM i c.val,
        setIntegral_indicator (hH i)]
      have hs : cells c ∩ {z | H z i} = {z | H z i ∧ M z = c.val} := by
        ext z
        exact and_comm
      rw [hs]
      simp only [setIntegral_const, smul_eq_mul, mul_one]
    _ = ∫ z in M ⁻¹' D, Set.indicator {z | H z i} (fun _ => (1 : ℝ)) z ∂μ := hevent.symm
    _ = _ := by
      rw [setIntegral_indicator (hH i)]
      have hs : M ⁻¹' D ∩ {z | H z i} = {z | H z i ∧ M z ∈ D} := by
        ext z
        exact and_comm
      rw [hs]
      simp only [setIntegral_const, smul_eq_mul, mul_one]

/-- Source (6.12)'s unconditional expectation bound for a random invariant size
multiset; arbitrary dependence of all other data is allowed. -/
theorem probability_le_integral_frontier (μ : Measure (I → B)) [IsProbabilityMeasure μ]
    (hex : Exchangeable μ) (H : (I → B) → I → Prop)
    (hH : ∀ i, MeasurableSet {z | H z i}) (heq : Equivariant H)
    (M : (I → B) → C) (hM : Measurable M) (s : C → ℕ)
    (hs : ∀ c, s c ≤ Fintype.card I)
    (hcount : ∀ z, (univ.filter (H z)).card ≤ s (M z)) (i : I) :
    μ.real {z | H z i} ≤ ∫ z, (s (M z) : ℝ) / Fintype.card I ∂μ := by
  have hb : Integrable (fun z => (s (M z) : ℝ)) μ := by
    apply (integrable_const (Fintype.card I : ℝ)).mono'
      ((measurable_of_countable (fun c => (s c : ℝ))).comp hM).aestronglyMeasurable
    filter_upwards [] with z
    change ‖(s (M z) : ℝ)‖ ≤ Fintype.card I
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hs (M z)
  rw [probability_eq_average_count μ H hH i (fun j => event_probability_eq μ hex H hH heq j i)]
  rw [integral_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply integral_mono (count_integrable μ H hH) hb
  intro z
  change ((univ.filter (H z)).card : ℝ) ≤ (s (M z) : ℝ)
  exact_mod_cast hcount z

/-- The conditional version is measurable for precisely the sigma algebra
generated by the statistic, not just for the full sample sigma algebra. -/
lemma conditionalRatio_sigma_measurable (μ : Measure (I → B))
    (H : (I → B) → I → Prop) (M : (I → B) → C) (i : I) :
    Measurable[(inferInstance : MeasurableSpace C).comap M]
      (fun z => conditionalRatio μ H M i (M z)) :=
  (measurable_of_countable (conditionalRatio μ H M i)).comp (comap_measurable M)

/-- Complete conditional-frontier assertion: a statistic-measurable integrable
conditional probability version, its derived pointwise bound, and its defining
integral identity on every statistic event. No conditional bound is an input. -/
theorem conditional_frontier_version (μ : Measure (I → B)) [IsProbabilityMeasure μ]
    (hex : Exchangeable μ) (H : (I → B) → I → Prop)
    (hH : ∀ i, MeasurableSet {z | H z i}) (heq : Equivariant H)
    (M : (I → B) → C) (hM : Measurable M) (hinv : ∀ e z, M (relabel e z) = M z)
    (s : C → ℕ) (hcount : ∀ z, (univ.filter (H z)).card ≤ s (M z)) (i : I) :
    Measurable[(inferInstance : MeasurableSpace C).comap M]
        (fun z => conditionalRatio μ H M i (M z)) ∧
      Integrable (fun z => conditionalRatio μ H M i (M z)) μ ∧
      (∀ c, 0 ≤ conditionalRatio μ H M i c ∧
        conditionalRatio μ H M i c ≤ (s c : ℝ) / Fintype.card I) ∧
      ∀ D : Set C, (∫ z in M ⁻¹' D, conditionalRatio μ H M i (M z) ∂μ) =
        μ.real {z | H z i ∧ M z ∈ D} :=
  ⟨conditionalRatio_sigma_measurable μ H M i,
    conditionalRatio_integrable μ H M hM i,
    fun c => ⟨conditionalRatio_nonneg μ H M i c,
      conditionalRatio_le μ hex H hH heq M hM hinv s hcount i c⟩,
    conditionalRatio_setIntegral μ H hH M hM i⟩

end
end MEJF.ConditionalExchangeability
