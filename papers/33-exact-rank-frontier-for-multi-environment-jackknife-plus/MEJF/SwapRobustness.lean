import MEJF.FiniteExchangeable
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-! # Actual total-variation degradation under block swaps

The total variation below is the variational supremum over all measurable
events. It is not an assumed eventwise error parameter.
-/

namespace MEJF.SwapRobustness
open MeasureTheory Finset
open scoped ENNReal NNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The paper's total-variation convention, `sup_A |μ(A)-ν(A)|`, with the
supremum over measurable events and probabilities expressed in `ℝ`. -/
def totalVariation (μ ν : Measure Ω) : ℝ :=
  sSup (Set.range (fun A : {A : Set Ω // MeasurableSet A} => |μ.real A - ν.real A|))

lemma tv_values_bddAbove (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    BddAbove (Set.range (fun A : {A : Set Ω // MeasurableSet A} =>
      |μ.real A - ν.real A|)) := by
  refine ⟨1, ?_⟩
  rintro x ⟨A, rfl⟩
  have hμ0 : 0 ≤ μ.real A := measureReal_nonneg
  have hν0 : 0 ≤ ν.real A := measureReal_nonneg
  have hμ1 : μ.real A ≤ 1 := measureReal_le_one
  have hν1 : ν.real A ≤ 1 := measureReal_le_one
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The defining variational property, derived from the actual bounded supremum. -/
theorem abs_event_sub_le_totalVariation (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (A : Set Ω) (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ totalVariation μ ν := by
  exact le_csSup (tv_values_bddAbove μ ν) ⟨⟨A, hA⟩, rfl⟩

theorem totalVariation_nonneg (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : 0 ≤ totalVariation μ ν := by
  have h := abs_event_sub_le_totalVariation μ ν ∅ MeasurableSet.empty
  simpa using h

theorem totalVariation_le_one (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : totalVariation μ ν ≤ 1 := by
  apply csSup_le
  · exact ⟨0, ⟨⟨∅, MeasurableSet.empty⟩, by simp⟩⟩
  · rintro x ⟨A, rfl⟩
    have hμ0 : 0 ≤ μ.real A := measureReal_nonneg
    have hν0 : 0 ≤ ν.real A := measureReal_nonneg
    have hμ1 : μ.real A ≤ 1 := measureReal_le_one
    have hν1 : ν.real A ≤ 1 := measureReal_le_one
    exact abs_le.mpr ⟨by linarith, by linarith⟩

@[simp] theorem totalVariation_self (μ : Measure Ω) : totalVariation μ μ = 0 := by
  simp [totalVariation]

theorem event_le_event_add_totalVariation (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (A : Set Ω) (hA : MeasurableSet A) :
    μ.real A ≤ ν.real A + totalVariation μ ν := by
  have h := abs_event_sub_le_totalVariation μ ν A hA
  have hl := le_abs_self (μ.real A - ν.real A)
  linarith

/-- Explicit two-level density tilt with nonnegative finite coefficients. -/
def twoLevelTilt (Q : Measure Ω) (A : Set Ω) (a b : ℝ≥0) : Measure Ω :=
  a • Q.restrict A + b • Q.restrict Aᶜ

instance twoLevelTilt_isFiniteMeasure (Q : Measure Ω) [IsFiniteMeasure Q]
    (A : Set Ω) (a b : ℝ≥0) : IsFiniteMeasure (twoLevelTilt Q A a b) := by
  unfold twoLevelTilt
  infer_instance

theorem twoLevelTilt_real_apply (Q : Measure Ω) [IsFiniteMeasure Q]
    (A : Set Ω) (a b : ℝ≥0) (C : Set Ω) (hC : MeasurableSet C) :
    (twoLevelTilt Q A a b).real C =
      (a : ℝ) * Q.real (C ∩ A) + (b : ℝ) * Q.real (C ∩ Aᶜ) := by
  unfold twoLevelTilt
  rw [measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _)]
  simp only [measureReal_nnreal_smul_apply, measureReal_restrict_apply hC]

/-- Normalizing the actual tilted measure gives a probability measure. -/
theorem twoLevelTilt_isProbabilityMeasure (Q : Measure Ω) [IsProbabilityMeasure Q]
    (A : Set Ω) (a b : ℝ≥0)
    (hnorm : (a : ℝ) * Q.real A + (b : ℝ) * Q.real Aᶜ = 1) :
    IsProbabilityMeasure (twoLevelTilt Q A a b) := by
  refine ⟨?_⟩
  apply (ENNReal.toReal_eq_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mp
  change (twoLevelTilt Q A a b).real Set.univ = (1 : ℝ≥0∞).toReal
  rw [twoLevelTilt_real_apply Q A a b Set.univ MeasurableSet.univ]
  simpa using hnorm

/-- Difference of event probabilities for two equal-level tilts. -/
theorem twoLevelTilt_real_sub (Q : Measure Ω) [IsFiniteMeasure Q]
    (A D : Set Ω) (hA : MeasurableSet A) (hD : MeasurableSet D)
    (a b : ℝ≥0) (C : Set Ω) (hC : MeasurableSet C) :
    (twoLevelTilt Q A a b).real C - (twoLevelTilt Q D a b).real C =
      ((a : ℝ)-b) * (Q.real (C ∩ A) - Q.real (C ∩ D)) := by
  rw [twoLevelTilt_real_apply Q A a b C hC, twoLevelTilt_real_apply Q D a b C hC]
  have hpartA := measureReal_inter_add_diff (μ := Q) (s := C) hA
  have hpartD := measureReal_inter_add_diff (μ := Q) (s := C) hD
  simp only [Set.diff_eq] at hpartA hpartD
  rw [show Q.real (C ∩ Aᶜ) = Q.real C - Q.real (C ∩ A) by linarith,
    show Q.real (C ∩ Dᶜ) = Q.real C - Q.real (C ∩ D) by linarith]
  ring

/-- The total variation between two equal-mass two-level tilts is attained at
`A \ D`; this proves the exact variational supremum, not only an upper estimate. -/
theorem totalVariation_twoLevelTilt (Q : Measure Ω) [IsFiniteMeasure Q]
    (A D : Set Ω) (hA : MeasurableSet A) (hD : MeasurableSet D)
    (hmass : Q.real A = Q.real D) (a b : ℝ≥0) (hab : b ≤ a) :
    totalVariation (twoLevelTilt Q A a b) (twoLevelTilt Q D a b) =
      ((a : ℝ)-b) * Q.real (A \ D) := by
  have hab' : (0 : ℝ) ≤ (a : ℝ)-b := sub_nonneg.mpr (by exact_mod_cast hab)
  have hbal : Q.real (A \ D) = Q.real (D \ A) := by
    have h₁ := measureReal_inter_add_diff (μ := Q) (s := A) hD
    have h₂ := measureReal_inter_add_diff (μ := Q) (s := D) hA
    rw [Set.inter_comm D A] at h₂
    linarith
  have hbound (C : Set Ω) (hC : MeasurableSet C) :
      |(twoLevelTilt Q A a b).real C - (twoLevelTilt Q D a b).real C| ≤
        ((a : ℝ)-b) * Q.real (A \ D) := by
    rw [twoLevelTilt_real_sub Q A D hA hD a b C hC, abs_mul, abs_of_nonneg hab']
    apply mul_le_mul_of_nonneg_left _ hab'
    have hp : Q.real (C ∩ A) - Q.real (C ∩ D) ≤ Q.real (A \ D) := by
      apply (le_measureReal_diff (μ := Q)).trans
      apply measureReal_mono ?_ (measure_ne_top _ _)
      intro x hx
      simp only [Set.mem_diff, Set.mem_inter_iff] at hx ⊢
      exact ⟨hx.1.2, fun hd => hx.2 ⟨hx.1.1, hd⟩⟩
    have hn : Q.real (C ∩ D) - Q.real (C ∩ A) ≤ Q.real (D \ A) := by
      apply (le_measureReal_diff (μ := Q)).trans
      apply measureReal_mono ?_ (measure_ne_top _ _)
      intro x hx
      simp only [Set.mem_diff, Set.mem_inter_iff] at hx ⊢
      exact ⟨hx.1.2, fun ha => hx.2 ⟨hx.1.1, ha⟩⟩
    rw [← hbal] at hn
    exact abs_le.mpr ⟨by linarith, hp⟩
  have hbdd : BddAbove (Set.range (fun C : {C : Set Ω // MeasurableSet C} =>
      |(twoLevelTilt Q A a b).real C - (twoLevelTilt Q D a b).real C|)) :=
    by
      refine ⟨((a : ℝ)-b) * Q.real (A \ D), ?_⟩
      rintro x ⟨C, rfl⟩
      exact hbound C C.property
  apply le_antisymm
  · apply csSup_le
    · exact ⟨0, ⟨⟨∅, MeasurableSet.empty⟩, by simp⟩⟩
    · rintro x ⟨C, rfl⟩
      exact hbound C C.property
  · have hat := le_csSup hbdd ⟨⟨A \ D, hA.diff hD⟩, rfl⟩
    have hCA : (A \ D) ∩ A = A \ D := by
      ext x
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, h.1⟩
    have hCD : (A \ D) ∩ D = ∅ := by
      ext x
      constructor
      · exact fun h => (h.1.2 h.2).elim
      · exact fun h => h.elim
    change |(twoLevelTilt Q A a b).real (A \ D) -
      (twoLevelTilt Q D a b).real (A \ D)| ≤
      totalVariation (twoLevelTilt Q A a b) (twoLevelTilt Q D a b) at hat
    rw [twoLevelTilt_real_sub Q A D hA hD a b _ (hA.diff hD), hCA, hCD] at hat
    simpa only [measureReal_empty, sub_zero, abs_of_nonneg
      (mul_nonneg hab' measureReal_nonneg)] using hat

/-- An invariant involution maps the tilted event to its preimage. -/
theorem map_twoLevelTilt (Q : Measure Ω) (f : Ω → Ω) (hf : Measurable f)
    (hinv : Function.Involutive f) (hQ : MeasurePreserving f Q Q)
    (A : Set Ω) (hA : MeasurableSet A) (a b : ℝ≥0) :
    (twoLevelTilt Q A a b).map f = twoLevelTilt Q (f ⁻¹' A) a b := by
  have hdouble (C : Set Ω) : f ⁻¹' (f ⁻¹' C) = C := by
    ext x
    simp only [Set.mem_preimage, hinv x]
  have hm (C : Set Ω) (hC : MeasurableSet C) :
      (Q.restrict C).map f = Q.restrict (f ⁻¹' C) := by
    simpa only [hdouble] using (hQ.restrict_preimage (hC.preimage hf)).map_eq
  unfold twoLevelTilt
  rw [Measure.map_add _ _ hf, Measure.map_smul, Measure.map_smul, hm A hA, hm Aᶜ hA.compl]
  rfl

variable {I B : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace B]

/-- Push the actual block law forward by swapping `i` with the designated label. -/
def swappedLaw (μ : Measure (I → B)) (i i₀ : I) : Measure (I → B) :=
  μ.map (Exchangeability.relabel (Equiv.swap i i₀))

instance swappedLaw_isProbabilityMeasure (μ : Measure (I → B)) [IsProbabilityMeasure μ]
    (i i₀ : I) : IsProbabilityMeasure (swappedLaw μ i i₀) := by
  unfold swappedLaw
  exact Measure.isProbabilityMeasure_map (FiniteExchangeable.measurable_relabel _).aemeasurable

/-- Actual mean total variation between the block law and its designated-label
swap pushforwards, as in paper equation (6.36). -/
def swapDefect (μ : Measure (I → B)) (i₀ : I) : ℝ :=
  (∑ i, totalVariation μ (swappedLaw μ i i₀)) / Fintype.card I

omit [Fintype I] in
/-- Equivariance identifies the swapped designated event with the original
labeled event, without any exchangeability assumption on the law. -/
theorem swapped_event_probability (μ : Measure (I → B))
    (H : (I → B) → I → Prop) (hH : ∀ i, MeasurableSet {z | H z i})
    (heq : Exchangeability.Equivariant H) (i i₀ : I) :
    (swappedLaw μ i i₀).real {z | H z i₀} = μ.real {z | H z i} := by
  have hp : Exchangeability.relabel (Equiv.swap i i₀) ⁻¹' {z | H z i₀} =
      {z | H z i} := by
    ext z
    change H (Exchangeability.relabel (Equiv.swap i i₀) z) i₀ ↔ H z i
    simpa using heq (Equiv.swap i i₀) z i
  unfold swappedLaw Measure.real
  rw [Measure.map_apply (FiniteExchangeable.measurable_relabel _) (hH i₀), hp]

omit [DecidableEq I] in
/-- Integrating the deterministic label count bounds the sum of marginal event
probabilities under an arbitrary block law. -/
theorem sum_probability_le_of_count_le (μ : Measure (I → B)) [IsProbabilityMeasure μ]
    (H : (I → B) → I → Prop) (hH : ∀ i, MeasurableSet {z | H z i})
    (s : ℕ) (hcount : ∀ z, (univ.filter (H z)).card ≤ s) :
    (∑ i, μ.real {z | H z i}) ≤ (s : ℝ) := by
  classical
  let f : I → (I → B) → ℝ := fun i => Set.indicator {z | H z i} (fun _ => 1)
  have hf : ∀ i, Integrable (f i) μ := fun i =>
    (integrable_const (1 : ℝ)).indicator (hH i)
  calc
    (∑ i, μ.real {z | H z i}) = ∫ z, ∑ i, f i z ∂μ := by
      rw [integral_finset_sum _ (fun i _ => hf i)]
      apply sum_congr rfl
      intro i _
      exact (integral_indicator_one (hH i)).symm
    _ ≤ ∫ _ : (I → B), (s : ℝ) ∂μ := by
      apply integral_mono (integrable_finset_sum _ (fun i _ => hf i)) (integrable_const _)
      intro z
      simp only [f, Set.indicator_apply, Set.mem_setOf_eq]
      simpa only [sum_boole, Nat.cast_le] using hcount z
    _ = s := by simp

/-- Corollary 6.7, upper bound: the exact pointwise count degrades by the true
mean swap total variation, with coefficient one. -/
theorem probability_le_count_add_swapDefect (μ : Measure (I → B))
    [IsProbabilityMeasure μ] (H : (I → B) → I → Prop)
    (hH : ∀ i, MeasurableSet {z | H z i}) (heq : Exchangeability.Equivariant H)
    (s : ℕ) (hcount : ∀ z, (univ.filter (H z)).card ≤ s) (i₀ : I) :
    μ.real {z | H z i₀} ≤ min 1 ((s : ℝ) / Fintype.card I + swapDefect μ i₀) := by
  classical
  refine le_min measureReal_le_one ?_
  have hi (i : I) : μ.real {z | H z i₀} ≤ μ.real {z | H z i} +
      totalVariation μ (swappedLaw μ i i₀) := by
    have h := event_le_event_add_totalVariation μ (swappedLaw μ i i₀)
      {z | H z i₀} (hH i₀)
    rwa [swapped_event_probability μ H hH heq i i₀] at h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) => hi i)
  have hsum' : (Fintype.card I : ℝ) * μ.real {z | H z i₀} ≤
      (∑ i, μ.real {z | H z i}) + ∑ i, totalVariation μ (swappedLaw μ i i₀) := by
    simpa only [sum_const, card_univ, nsmul_eq_mul, sum_add_distrib] using hsum
  have hc := sum_probability_le_of_count_le μ H hH s hcount
  have hcard : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i₀⟩
  unfold swapDefect
  rw [← add_div]
  apply (le_div_iff₀ hcard).mpr
  nlinarith

/-- The total probability of one designated event occurring while another label
fails to occur is computed by the exact a.e. label count. -/
theorem sum_event_differences_of_count_eq (Q : Measure (I → B)) [IsProbabilityMeasure Q]
    (H : (I → B) → I → Prop) (hH : ∀ i, MeasurableSet {z | H z i})
    (s : ℕ) (hcount : ∀ᵐ z ∂Q, (univ.filter (H z)).card = s) (i₀ : I) :
    (∑ i, Q.real ({z | H z i₀} \ {z | H z i})) =
      ((Fintype.card I - s : ℕ) : ℝ) * Q.real {z | H z i₀} := by
  classical
  let A := {z | H z i₀}
  let D (i : I) := A \ {z | H z i}
  let f (i : I) := (D i).indicator (fun _ => (1 : ℝ))
  have hD (i : I) : MeasurableSet (D i) := (hH i₀).diff (hH i)
  have hf (i : I) : Integrable (f i) Q := (integrable_const _).indicator (hD i)
  have hpoint : (fun z => ∑ i, f i z) =ᵐ[Q]
      A.indicator (fun _ => ((Fintype.card I - s : ℕ) : ℝ)) := by
    filter_upwards [hcount] with z hz
    have hc := filter_card_add_filter_neg_card_eq_card (s := univ) (H z)
    rw [hz, card_univ] at hc
    have hnc : (univ.filter (fun i => ¬ H z i)).card = Fintype.card I-s := by omega
    by_cases ha : H z i₀
    · simp only [f, D, A, Set.indicator_apply, Set.mem_diff, Set.mem_setOf_eq,
        ha, true_and, if_true]
      simpa only [sum_boole, Nat.cast_inj] using hnc
    · simp [f, D, A, Set.indicator_apply, ha]
  calc
    (∑ i, Q.real ({z | H z i₀} \ {z | H z i})) = ∫ z, ∑ i, f i z ∂Q := by
      rw [integral_finset_sum _ (fun i _ => hf i)]
      apply sum_congr rfl
      intro i _
      exact (integral_indicator_one (hD i)).symm
    _ = ∫ z, A.indicator (fun _ => ((Fintype.card I-s : ℕ) : ℝ)) z ∂Q :=
      integral_congr_ae hpoint
    _ = ((Fintype.card I-s : ℕ) : ℝ) * Q.real A := by
      simpa [smul_eq_mul, mul_comm] using
        integral_indicator_const (μ := Q) (((Fintype.card I-s : ℕ) : ℝ)) (hH i₀)

/-- The actual mean swap-TV of the two-level tilted measure. This equality
uses the variational supremum theorem above for each swap and the exact a.e.
count to add the disagreement probabilities. -/
theorem swapDefect_twoLevelTilt (Q : Measure (I → B)) [IsProbabilityMeasure Q]
    (hQ : Exchangeability.Exchangeable Q)
    (H : (I → B) → I → Prop) (hH : ∀ i, MeasurableSet {z | H z i})
    (heq : Exchangeability.Equivariant H) (s : ℕ)
    (hcount : ∀ᵐ z ∂Q, (univ.filter (H z)).card = s)
    (i₀ : I) (a b : ℝ≥0) (hab : b ≤ a) :
    swapDefect (twoLevelTilt Q {z | H z i₀} a b) i₀ =
      ((a : ℝ)-b) * ((Fintype.card I-s : ℕ) : ℝ) * Q.real {z | H z i₀} /
        Fintype.card I := by
  classical
  let A := {z | H z i₀}
  have hi (i : I) : totalVariation (twoLevelTilt Q A a b)
      (swappedLaw (twoLevelTilt Q A a b) i i₀) =
      ((a : ℝ)-b) * Q.real (A \ {z | H z i}) := by
    let f := Exchangeability.relabel (Equiv.swap i i₀) (B := B)
    have hf : Measurable f := FiniteExchangeable.measurable_relabel _
    have hinv : Function.Involutive f := by
      intro z
      funext j
      simp [f, Exchangeability.relabel, Function.comp_def]
    have hp : f ⁻¹' A = {z | H z i} := by
      ext z
      change H (Exchangeability.relabel (Equiv.swap i i₀) z) i₀ ↔ H z i
      simpa using heq (Equiv.swap i i₀) z i
    have hmap : swappedLaw (twoLevelTilt Q A a b) i i₀ =
        twoLevelTilt Q {z | H z i} a b := by
      change (twoLevelTilt Q A a b).map f = _
      rw [map_twoLevelTilt Q f hf hinv (hQ _) A (hH i₀) a b, hp]
    rw [hmap]
    exact totalVariation_twoLevelTilt Q A _ (hH i₀) (hH i)
      (Exchangeability.event_probability_eq Q hQ H hH heq i₀ i) a b hab
  unfold swapDefect
  change (∑ i, totalVariation (twoLevelTilt Q A a b)
    (swappedLaw (twoLevelTilt Q A a b) i i₀)) / Fintype.card I = _
  simp_rw [hi]
  rw [← mul_sum, sum_event_differences_of_count_eq Q H hH s hcount i₀]
  ring

/-- Exact base event probability from exchangeability and an a.e. exact count. -/
theorem probability_eq_of_exchangeable_count_eq (Q : Measure (I → B))
    [IsProbabilityMeasure Q] (hQ : Exchangeability.Exchangeable Q)
    (H : (I → B) → I → Prop) (hH : ∀ i, MeasurableSet {z | H z i})
    (heq : Exchangeability.Equivariant H) (s : ℕ)
    (hcount : ∀ᵐ z ∂Q, (univ.filter (H z)).card = s) (i₀ : I) :
    Q.real {z | H z i₀} = (s : ℝ) / Fintype.card I := by
  have h := Exchangeability.probability_eq_average_count Q H hH i₀
    (fun i => Exchangeability.event_probability_eq Q hQ H hH heq i i₀)
  have hi : (∫ z, ((univ.filter (H z)).card : ℝ) ∂Q) = (s : ℝ) := by
    calc
      _ = ∫ _ : (I → B), (s : ℝ) ∂Q := by
        apply integral_congr_ae
        filter_upwards [hcount] with z hz
        exact congrArg (fun n : ℕ => (n : ℝ)) hz
      _ = s := by simp
  rwa [hi] at h

/-- Exact sharp tilt for any exchangeable equivariant event family with
an almost-sure exact nontrivial label count. Coefficients are constructed as
nonnegative reals; no TV equality or event-probability target is assumed. -/
theorem exists_sharp_tilt (Q : Measure (I → B)) [IsProbabilityMeasure Q]
    (hQ : Exchangeability.Exchangeable Q)
    (H : (I → B) → I → Prop) (hH : ∀ i, MeasurableSet {z | H z i})
    (heq : Exchangeability.Equivariant H) (s : ℕ)
    (hcount : ∀ᵐ z ∂Q, (univ.filter (H z)).card = s)
    (hs : 0 < s) (hsN : s < Fintype.card I) (i₀ : I)
    (η : ℝ) (hη : 0 ≤ η) (hηmax : η ≤ 1-(s : ℝ)/Fintype.card I) :
    ∃ P : Measure (I → B), IsProbabilityMeasure P ∧
      swapDefect P i₀ = η ∧ P.real {z | H z i₀} = (s : ℝ)/Fintype.card I+η := by
  let γ : ℝ := (s : ℝ)/Fintype.card I
  have hN : (0 : ℝ) < Fintype.card I := by exact_mod_cast (hs.trans hsN)
  have hg : 0 < γ := div_pos (by exact_mod_cast hs) hN
  have hg1 : γ < 1 := (div_lt_one hN).mpr (by exact_mod_cast hsN)
  have hg0 : γ ≠ 0 := ne_of_gt hg
  have hgc : 1-γ ≠ 0 := ne_of_gt (sub_pos.mpr hg1)
  let a : ℝ≥0 := ⟨(γ+η)/γ, div_nonneg (by linarith) hg.le⟩
  let b : ℝ≥0 := ⟨(1-γ-η)/(1-γ), div_nonneg (by dsimp [γ]; linarith) (by linarith)⟩
  have ha : (a : ℝ)*γ = γ+η := by
    change ((γ+η)/γ)*γ = γ+η
    exact div_mul_cancel₀ _ hg0
  have hb : (b : ℝ)*(1-γ) = 1-γ-η := by
    change ((1-γ-η)/(1-γ))*(1-γ) = 1-γ-η
    exact div_mul_cancel₀ _ hgc
  have hd : ((a : ℝ)-b)*γ*(1-γ) = η := by
    calc
      _ = ((a : ℝ)*γ)*(1-γ) - ((b : ℝ)*(1-γ))*γ := by ring
      _ = η := by rw [ha, hb]; ring
  have hab : b ≤ a := by
    have hden : 0 < γ*(1-γ) := mul_pos hg (by linarith)
    have hmul : 0 ≤ ((a : ℝ)-b)*(γ*(1-γ)) := by nlinarith [hd]
    have hsub : 0 ≤ (a : ℝ)-b := (mul_nonneg_iff_of_pos_right hden).mp hmul
    exact_mod_cast (sub_nonneg.mp hsub)
  let A := {z | H z i₀}
  have hA : MeasurableSet A := hH i₀
  have hQA : Q.real A = γ := probability_eq_of_exchangeable_count_eq Q hQ H hH heq s hcount i₀
  have hQAc : Q.real Aᶜ = 1-γ := by
    have hp := measureReal_add_measureReal_compl (μ := Q) hA
    rw [measureReal_univ_eq_one, hQA] at hp
    linarith
  let P := twoLevelTilt Q A a b
  have hP : IsProbabilityMeasure P := by
    apply twoLevelTilt_isProbabilityMeasure
    rw [hQA, hQAc]
    linarith [ha, hb]
  refine ⟨P, hP, ?_, ?_⟩
  · dsimp [P, A]
    rw [swapDefect_twoLevelTilt Q hQ H hH heq s hcount i₀ a b hab, hQA]
    have hfrac : ((Fintype.card I-s : ℕ) : ℝ)/Fintype.card I = 1-γ := by
      rw [Nat.cast_sub (le_of_lt hsN)]
      dsimp [γ]
      field_simp
    calc
      _ = ((a : ℝ)-b)*γ*(((Fintype.card I-s : ℕ) : ℝ)/Fintype.card I) := by ring
      _ = η := by rw [hfrac]; exact hd
  · change (twoLevelTilt Q A a b).real A = γ+η
    rw [twoLevelTilt_real_apply Q A a b A hA]
    simp only [Set.inter_self, Set.inter_compl_self, measureReal_empty, mul_zero, add_zero, hQA]
    exact ha

end
end MEJF.SwapRobustness
