import MEJF.MainExact
import MEJF.ExtendedRule
import Mathlib.MeasureTheory.Integral.Prod

/-! The coherently randomized learner extension from §2.1. One seed is fixed
through every augmented fit. Its law is independent of the exchangeable blocks.
Joint failure measurability is derived from the raw all-arity joint hypothesis. -/
namespace MEJF.CoherentSeed
open MeasureTheory Finset Setup Exchangeability
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {U X : Type*} [MeasurableSpace U] [MeasurableSpace X] {N m n : ℕ}

/-- The source's jointly measurable seeded multiset family. The single first
argument supplies the same realized seed to all evaluations and deletions. -/
structure Family (U X : Type*) [MeasurableSpace U] [MeasurableSpace X] (n : ℕ) where
  predict : U → Multiset (Block X n) → X → ℝ
  measurable_predict : ∀ r : ℕ,
    Measurable (fun q : U × ((Fin r → Block X n) × X) =>
      predict q.1 ((List.ofFn q.2.1 : List (Block X n)) : Multiset (Block X n)) q.2.2)

/-- Fixing a seed gives an admissible deterministic learner, with its original
multiset prediction function. -/
def Family.sectionLearner (A : Family U X n) (u : U) : Learner X n where
  predict := A.predict u
  measurable_predict := fun r => (A.measurable_predict r).comp
    (measurable_const.prodMk measurable_id)

/-- Actual failure, evaluating every fit with the identical first-coordinate seed. -/
def failure (A : Family U X n) (q : U × (Fin (m+1) → Block X n))
    (i : Fin (m+1)) (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : Prop :=
  Setup.failure (A.sectionLearner q.1) q.2 i F t ell ht he

/-- Joint raw-fit measurability on any fixed retained finite set of block labels. -/
lemma measurable_predict_finset (A : Family U X n) (s : Finset (Fin N)) :
    Measurable (fun q : U × ((Fin N → Block X n) × X) =>
      (A.sectionLearner q.1).predict (s.val.map q.2.1) q.2.2) := by
  have henum : Measurable (fun q : U × ((Fin N → Block X n) × X) =>
      (q.1,((fun l : Fin s.card => q.2.1 (s.orderEmbOfFin rfl l)),q.2.2))) := by
    apply Measurable.prodMk measurable_fst
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro l
      exact (measurable_pi_apply (s.orderEmbOfFin rfl l)).comp (measurable_fst.comp measurable_snd)
    · exact measurable_snd.comp measurable_snd
  have h := (A.measurable_predict s.card).comp henum
  simpa only [Function.comp_def,Setup.ofFn_finset_map,Family.sectionLearner] using h

lemma measurable_pairPrediction (A : Family U X n) (i k : Fin N) :
    Measurable (fun q : U × ((Fin N → Block X n) × X) =>
      Setup.pairPrediction (A.sectionLearner q.1) q.2.1 i k q.2.2) :=
  measurable_predict_finset A ((univ.erase i).erase k)

lemma measurable_response (i : Fin N) (j : Fin n) :
    Measurable (fun q : U × (Fin N → Block X n) => (q.2 i j).2) :=
  ((Setup.measurable_response i j).comp measurable_snd)

lemma measurable_covariate (i : Fin N) (j : Fin n) :
    Measurable (fun q : U × (Fin N → Block X n) => (q.2 i j).1) :=
  ((Setup.measurable_covariate i j).comp measurable_snd)

lemma measurable_observed_prediction (A : Family U X n) (i k : Fin N) (j : Fin n) :
    Measurable (fun q : U × (Fin N → Block X n) =>
      Setup.pairPrediction (A.sectionLearner q.1) q.2 i k (q.2 i j).1) :=
  (measurable_pairPrediction A i k).comp
    (measurable_fst.prodMk (measurable_snd.prodMk (measurable_covariate i j)))

lemma measurable_radius (A : Family U X n) (i k : Fin N)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) :
    Measurable (fun q : U × (Fin N → Block X n) =>
      Setup.radius (A.sectionLearner q.1) q.2 i k t ht) := by
  apply OrderStatistics.measurable_stat_comp
  intro j
  exact continuous_abs.measurable.comp ((measurable_response i j).sub
    (measurable_observed_prediction A i k j))

lemma measurable_lowerEndpoint (A : Family U X n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    Measurable (fun q : U × (Fin (m+1) → Block X n) =>
      Setup.lowerEndpoint (A.sectionLearner q.1) q.2 i j t ell ht he) := by
  apply OrderStatistics.measurable_stat_comp
  intro k
  exact (measurable_observed_prediction A i (i.succAbove k) j).sub
    (measurable_radius A (i.succAbove k) i t ht)

lemma measurable_upperEndpoint (A : Family U X n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    Measurable (fun q : U × (Fin (m+1) → Block X n) =>
      Setup.upperEndpoint (A.sectionLearner q.1) q.2 i j t ell ht he) := by
  apply OrderStatistics.measurable_stat_comp
  intro k
  exact (measurable_observed_prediction A i (i.succAbove k) j).add
    (measurable_radius A (i.succAbove k) i t ht)

lemma measurableSet_covered (A : Family U X n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    MeasurableSet {q : U × (Fin (m+1) → Block X n) |
      Setup.covered (A.sectionLearner q.1) q.2 i j t ell ht he} := by
  exact (measurableSet_le (measurable_lowerEndpoint A i j t ell ht he)
    (measurable_response i j)).inter
      (measurableSet_le (measurable_response i j) (measurable_upperEndpoint A i j t ell ht he))

lemma measurable_missCount (A : Family U X n) (i : Fin (m+1))
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    Measurable (fun q : U × (Fin (m+1) → Block X n) =>
      (univ.filter fun j => ¬ Setup.covered (A.sectionLearner q.1) q.2 i j t ell ht he).card) := by
  have h : Measurable (fun q : U × (Fin (m+1) → Block X n) =>
      ∑ j : Fin n, if ¬ Setup.covered (A.sectionLearner q.1) q.2 i j t ell ht he then (1:ℕ) else 0) := by
    apply Finset.measurable_sum
    intro j hj
    exact Measurable.ite (measurableSet_covered A i j t ell ht he).compl
      measurable_const measurable_const
  simpa only [Finset.sum_boole] using h

/-- The actual joint failure event is measurable; it is not an input assumption. -/
theorem measurableSet_failure (A : Family U X n) (i : Fin (m+1))
    (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    MeasurableSet {q : U × (Fin (m+1) → Block X n) | failure A q i F t ell ht he} :=
  measurableSet_le measurable_const (measurable_missCount A i t ell ht he)

/-- Fubini's conditioning identity for the actual same-seed event under the
independent product law, derived from the raw family's joint measurability. -/
theorem failure_probability_eq_integral (A : Family U X n)
    (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ]
    (i : Fin (m+1)) (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    (ν.prod μ).real {q | failure A q i F t ell ht he} =
      ∫ u, μ.real {Z | Setup.failure (A.sectionLearner u) Z i F t ell ht he} ∂ν := by
  let f : U × (Fin (m+1) → Block X n) → ℝ :=
    Set.indicator {q | failure A q i F t ell ht he} (fun _ => 1)
  have hj := measurableSet_failure A i F t ell ht he
  have hf : Integrable f (ν.prod μ) := (integrable_const (1:ℝ)).indicator hj
  calc
    _ = ∫ q, f q ∂ν.prod μ := (integral_indicator_one hj).symm
    _ = ∫ u, ∫ Z, f (u,Z) ∂μ ∂ν := integral_prod f hf
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact integral_indicator_one (Setup.measurableSet_failure (A.sectionLearner u) i F t ell ht he)

/-- Integrability of the conditioning function is proved, not assumed. -/
lemma integrable_section_probability (A : Family U X n)
    (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ]
    (i : Fin (m+1)) (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    Integrable (fun u => μ.real {Z | Setup.failure (A.sectionLearner u) Z i F t ell ht he}) ν := by
  let f : U × (Fin (m+1) → Block X n) → ℝ :=
    Set.indicator {q | failure A q i F t ell ht he} (fun _ => 1)
  have hf : Integrable f (ν.prod μ) := (integrable_const (1:ℝ)).indicator
    (measurableSet_failure A i F t ell ht he)
  have hinner : (fun u => ∫ Z, f (u,Z) ∂μ) =
      fun u => μ.real {Z | Setup.failure (A.sectionLearner u) Z i F t ell ht he} := by
    funext u
    exact integral_indicator_one (Setup.measurableSet_failure (A.sectionLearner u) i F t ell ht he)
  rw [← hinner]
  exact hf.integral_prod_left

/-- A bound for every deterministic seed section remains valid after sampling
one independent seed and using it coherently in the full procedure. -/
theorem failure_probability_le_of_sections (A : Family U X n)
    (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ]
    (i : Fin (m+1)) (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (c : ℝ) (hc : ∀ u, μ.real {Z | Setup.failure (A.sectionLearner u) Z i F t ell ht he} ≤ c) :
    (ν.prod μ).real {q | failure A q i F t ell ht he} ≤ c := by
  rw [failure_probability_eq_integral A ν μ i F t ell ht he]
  calc
    _ ≤ ∫ _u : U, c ∂ν := integral_mono
      (integrable_section_probability A ν μ i F t ell ht he) (integrable_const c) hc
    _ = c := by simp

/-- The source's deterministic upper bound holds unchanged for every actual
coherently randomized family under an independent seed/block product law. -/
theorem failure_probability_le (A : Family U X n)
    (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ]
    (hμ : Exchangeable μ) (i : Fin (m+1)) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    (ν.prod μ).real {q | failure A q i F t ell ht he} ≤ RankFrontier.failureRate m F t ell :=
  failure_probability_le_of_sections A ν μ i F t ell ht he _
    (fun u => MainUpper.failure_probability_le (A.sectionLearner u) μ hμ F t ell ht he i)

/-- Every deterministic learner embeds as a seed-independent jointly measurable family. -/
def constantFamily (A : Learner X n) : Family U X n where
  predict := fun _ => A.predict
  measurable_predict := fun r => (A.measurable_predict r).comp measurable_snd

@[simp] lemma sectionLearner_constantFamily (A : Learner X n) (u : U) :
    (constantFamily (U := U) A).sectionLearner u = A := rfl

/-- The deterministic embedding has exactly its original failure probability. -/
lemma constantFamily_probability (A : Learner X n)
    (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ]
    (i : Fin (m+1)) (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    (ν.prod μ).real {q | failure (constantFamily A) q i F t ell ht he} =
      μ.real {Z | Setup.failure A Z i F t ell ht he} := by
  have heq : {q : U × (Fin (m+1) → Block X n) | failure (constantFamily A) q i F t ell ht he} =
      Set.univ ×ˢ {Z | Setup.failure A Z i F t ell ht he} := by
    ext q
    simp only [failure,sectionLearner_constantFamily,Set.mem_setOf_eq,Set.mem_prod,Set.mem_univ,true_and]
  rw [heq,measureReal_prod_prod]
  simp

/-- Actual randomized minimax values for an arbitrary fixed seed space and
probability law. The source block law and the seeded learner still range freely;
their joint experiment is the independent seed/block product. -/
def randomizedValues (ν : Measure U) (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : Set ℝ :=
  {r | ∃ (A : Family U UniversalCovariate n)
    (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
    IsProbabilityMeasure μ ∧ Exchangeable μ ∧
    r = (ν.prod μ).real {q | failure A q (Fin.last m) (failureRank alpha n) t ell ht he}}

/-- Independently defined statistical supremum for coherently randomized fits. -/
def randomizedGamma (ν : Measure U) (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : ℝ :=
  sSup (randomizedValues ν m n alpha t ell ht he)

lemma deterministic_values_bddAbove (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    BddAbove {r : ℝ | ∃ (A : Learner UniversalCovariate n)
      (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
      IsProbabilityMeasure μ ∧ Exchangeable μ ∧
      r = μ.real {Z | Setup.failure A Z (Fin.last m) (failureRank alpha n) t ell ht he}} := by
  refine ⟨RankFrontier.failureRate m (failureRank alpha n) t ell,?_⟩
  rintro r ⟨A,μ,hprob,hμ,rfl⟩
  letI : IsProbabilityMeasure μ := hprob
  exact MainUpper.failure_probability_le A μ hμ _ t ell ht he (Fin.last m)

/-- The sectionwise proof bounds a coherent procedure by the actual deterministic
supremum itself, without identifying that supremum with the closed formula. -/
theorem probability_le_finiteRankGamma (A : Family U UniversalCovariate n)
    (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure (Fin (m+1) → Block UniversalCovariate n)) [IsProbabilityMeasure μ]
    (hμ : Exchangeable μ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    (ν.prod μ).real {q | failure A q (Fin.last m) (failureRank alpha n) t ell ht he} ≤
      finiteRankGamma m n alpha t ell ht he := by
  apply failure_probability_le_of_sections A ν μ (Fin.last m) (failureRank alpha n) t ell ht he
  intro u
  unfold finiteRankGamma
  apply le_csSup (deterministic_values_bddAbove m n alpha t ell ht he)
  exact ⟨A.sectionLearner u,μ,inferInstance,hμ,rfl⟩

lemma randomizedValues_nonempty (ν : Measure U) [IsProbabilityMeasure ν]
    (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    (randomizedValues ν m n alpha t ell ht he).Nonempty := by
  obtain ⟨r,A,μ,hprob,hμ,hr⟩ := MainUpper.minimax_values_nonempty m n alpha t ell ht he
  letI : IsProbabilityMeasure μ := hprob
  refine ⟨r,constantFamily A,μ,hprob,hμ,?_⟩
  rw [constantFamily_probability A ν μ (Fin.last m) (failureRank alpha n) t ell ht he]
  exact hr

lemma randomizedValues_bddAbove (ν : Measure U) [IsProbabilityMeasure ν]
    (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    BddAbove (randomizedValues ν m n alpha t ell ht he) := by
  refine ⟨finiteRankGamma m n alpha t ell ht he,?_⟩
  rintro r ⟨A,μ,hprob,hμ,rfl⟩
  letI : IsProbabilityMeasure μ := hprob
  exact probability_le_finiteRankGamma A ν μ hμ alpha t ell ht he

/-- Independent coherent randomization cannot increase the actual statistical
worst-case value. This conclusion uses true conditioning and true supremum membership. -/
theorem randomizedGamma_le_finiteRankGamma (ν : Measure U) [IsProbabilityMeasure ν]
    (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    randomizedGamma ν m n alpha t ell ht he ≤ finiteRankGamma m n alpha t ell ht he := by
  unfold randomizedGamma
  apply csSup_le (randomizedValues_nonempty ν m n alpha t ell ht he)
  rintro r ⟨A,μ,hprob,hμ,rfl⟩
  letI : IsProbabilityMeasure μ := hprob
  exact probability_le_finiteRankGamma A ν μ hμ alpha t ell ht he

/-- Every deterministic procedure embeds in the actual coherent randomized
experiment for every seed probability law, with exactly its original probability. -/
theorem finiteRankGamma_le_randomizedGamma (ν : Measure U) [IsProbabilityMeasure ν]
    (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    finiteRankGamma m n alpha t ell ht he ≤ randomizedGamma ν m n alpha t ell ht he := by
  unfold finiteRankGamma
  apply csSup_le (MainUpper.minimax_values_nonempty m n alpha t ell ht he)
  rintro r ⟨A,μ,hprob,hμ,hr⟩
  letI : IsProbabilityMeasure μ := hprob
  unfold randomizedGamma
  apply le_csSup (randomizedValues_bddAbove ν m n alpha t ell ht he)
  refine ⟨constantFamily A,μ,hprob,hμ,?_⟩
  rw [constantFamily_probability A ν μ (Fin.last m) (failureRank alpha n) t ell ht he]
  exact hr

/-- The source's unchanged-worst-case assertion, as equality of independently
defined statistical suprema on the original universal covariate space. -/
theorem randomizedGamma_eq_finiteRankGamma (ν : Measure U) [IsProbabilityMeasure ν]
    (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    randomizedGamma ν m n alpha t ell ht he = finiteRankGamma m n alpha t ell ht he :=
  le_antisymm (randomizedGamma_le_finiteRankGamma ν m n alpha t ell ht he)
    (finiteRankGamma_le_randomizedGamma ν m n alpha t ell ht he)

/-- Therefore the exact finite-rank failure formula itself is unchanged under
coherent independent learner randomization in the source parameter regime. -/
theorem randomizedGamma_eq_failureRate (ν : Measure U) [IsProbabilityMeasure ν]
    (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    randomizedGamma ν m n alpha t ell ht he = RankFrontier.failureRate m (failureRank alpha n) t ell := by
  rw [randomizedGamma_eq_finiteRankGamma ν m n alpha t ell ht he,
    MainExact.finiteRankGamma_eq m n alpha ha ha1 t ell ht he]

/-- A deterministic attaining source model remains an actual attaining
independent-seed experiment, for every seed probability law. -/
theorem exists_attaining_model (ν : Measure U) [IsProbabilityMeasure ν]
    (m n F t ell : ℕ) (hm : 1 ≤ m) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    ∃ (A : Family U UniversalCovariate n) (Z : Fin (m+1) → Block UniversalCovariate n),
      (ν.prod (FiniteExchangeable.blockPermutationLaw Z)).real
        {q | failure A q (Fin.last m) F t ell ht he} = RankFrontier.failureRate m F t ell := by
  obtain ⟨A,Z,hA⟩ := MainExact.exists_attaining_model m n F t ell hm hF hFn ht he
  refine ⟨constantFamily A,Z,?_⟩
  rw [constantFamily_probability A ν (FiniteExchangeable.blockPermutationLaw Z)
    (Fin.last m) F t ell ht he]
  exact hA

section AlmostEverywhere
variable {B : Type*} [MeasurableSpace B]

/-- Fubini identity for an arbitrary jointly measurable event, used to transfer
versions differing only at exceptional seed values. -/
lemma event_probability_eq_integral (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure B) [IsProbabilityMeasure μ] (H : U × B → Prop)
    (hH : MeasurableSet {q | H q}) :
    (ν.prod μ).real {q | H q} = ∫ u, μ.real {Z | H (u,Z)} ∂ν := by
  let f : U × B → ℝ := Set.indicator {q | H q} (fun _ => 1)
  have hf : Integrable f (ν.prod μ) := (integrable_const (1:ℝ)).indicator hH
  calc
    _ = ∫ q, f q ∂ν.prod μ := (integral_indicator_one hH).symm
    _ = ∫ u, ∫ Z, f (u,Z) ∂μ ∂ν := integral_prod f hf
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact integral_indicator_one (measurable_prodMk_left hH)

lemma integrable_event_sections (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure B) [IsProbabilityMeasure μ] (H : U × B → Prop)
    (hH : MeasurableSet {q | H q}) :
    Integrable (fun u => μ.real {Z | H (u,Z)}) ν := by
  let f : U × B → ℝ := Set.indicator {q | H q} (fun _ => 1)
  have hf : Integrable f (ν.prod μ) := (integrable_const (1:ℝ)).indicator hH
  have heq : (fun u => ∫ Z, f (u,Z) ∂μ) = fun u => μ.real {Z | H (u,Z)} := by
    funext u
    exact integral_indicator_one (measurable_prodMk_left hH)
  rw [← heq]
  exact hf.integral_prod_left

/-- Only almost every seed section must satisfy the bound. Exceptional seeds
may have arbitrary values; independence is the actual product measure here. -/
theorem event_probability_le_of_ae_sections (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure B) [IsProbabilityMeasure μ] (H : U × B → Prop)
    (hH : MeasurableSet {q | H q}) (c : ℝ)
    (hc : ∀ᵐ u ∂ν, μ.real {Z | H (u,Z)} ≤ c) :
    (ν.prod μ).real {q | H q} ≤ c := by
  rw [event_probability_eq_integral ν μ H hH]
  calc
    _ ≤ ∫ _u : U, c ∂ν := integral_mono_ae (integrable_event_sections ν μ H hH)
      (integrable_const c) hc
    _ = c := by simp

/-- Jointly measurable event versions that agree at all block arrays for almost
every seed have exactly the same actual independent-product probability. -/
theorem probability_eq_of_ae_seedwise_iff (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure B) [IsProbabilityMeasure μ] (H K : U × B → Prop)
    (hH : MeasurableSet {q | H q}) (hK : MeasurableSet {q | K q})
    (heq : ∀ᵐ u ∂ν, ∀ Z, H (u,Z) ↔ K (u,Z)) :
    (ν.prod μ).real {q | H q} = (ν.prod μ).real {q | K q} := by
  rw [event_probability_eq_integral ν μ H hH,event_probability_eq_integral ν μ K hK]
  apply integral_congr_ae
  filter_upwards [heq] with u hu
  have hs : {Z | H (u,Z)} = {Z | K (u,Z)} := by ext Z; exact hu Z
  rw [hs]

end AlmostEverywhere

/-- A measurable seed mask keeps the original joint family on `G` and uses one
fixed admissible fallback learner off `G`. Joint measurability is preserved. -/
def Family.mask (A : Family U X n) (G : Set U) (hG : MeasurableSet G)
    (fallback : Learner X n) : Family U X n where
  predict := fun u T x => if u ∈ G then A.predict u T x else fallback.predict T x
  measurable_predict := fun r => Measurable.ite (hG.preimage measurable_fst)
    (A.measurable_predict r) ((fallback.measurable_predict r).comp measurable_snd)

lemma Family.sectionLearner_mask_of_mem (A : Family U X n) (G : Set U)
    (hG : MeasurableSet G) (fallback : Learner X n) (u : U) (hu : u ∈ G) :
    (A.mask G hG fallback).sectionLearner u = A.sectionLearner u := by
  simp only [Family.mask,Family.sectionLearner,if_pos hu]

lemma Family.sectionLearner_mask_of_not_mem (A : Family U X n) (G : Set U)
    (hG : MeasurableSet G) (fallback : Learner X n) (u : U) (hu : u ∉ G) :
    (A.mask G hG fallback).sectionLearner u = fallback := by
  simp only [Family.mask,Family.sectionLearner,if_neg hu]

/-- The concrete admissible zero fallback requested in the source's exceptional
seed interpretation. -/
def zeroLearner : Learner X n where
  predict := fun _ _ => 0
  measurable_predict := fun _ => measurable_const

def Family.zeroMask (A : Family U X n) (G : Set U) (hG : MeasurableSet G) : Family U X n :=
  A.mask G hG zeroLearner

/-- Modifying the family on a seed-null set, including the zero fallback,
does not change any actual finite-rank failure probability. -/
theorem mask_failure_probability_eq (A : Family U X n) (G : Set U) (hG : MeasurableSet G)
    (fallback : Learner X n) (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ]
    (hfull : ∀ᵐ u ∂ν, u ∈ G) (i : Fin (m+1)) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    (ν.prod μ).real {q | failure (A.mask G hG fallback) q i F t ell ht he} =
      (ν.prod μ).real {q | failure A q i F t ell ht he} := by
  apply probability_eq_of_ae_seedwise_iff ν μ
    (fun q => failure (A.mask G hG fallback) q i F t ell ht he)
    (fun q => failure A q i F t ell ht he)
    (measurableSet_failure _ i F t ell ht he) (measurableSet_failure A i F t ell ht he)
  filter_upwards [hfull] with u hu Z
  simp only [failure,Family.sectionLearner_mask_of_mem A G hG fallback u hu]

/-- Explicit a.e.-admissible form of the source upper bound. A single common
deterministic learner must realize all hypothetical label events at every block
array for each good seed. Nothing is required of exceptional null seeds. The
joint event measurability is explicit here; actual `Family` events satisfy it by
`measurableSet_failure`, proved above from raw prediction measurability. -/
theorem ae_admissible_failure_probability_le
    (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ] (hμ : Exchangeable μ)
    (H : U × (Fin (m+1) → Block X n) → Fin (m+1) → Prop)
    (hH : ∀ j, MeasurableSet {q | H q j}) (i : Fin (m+1)) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (hgood : ∀ᵐ u ∂ν, ∃ A : Learner X n, ∀ Z j,
      H (u,Z) j ↔ Setup.failure A Z j F t ell ht he) :
    (ν.prod μ).real {q | H q i} ≤ RankFrontier.failureRate m F t ell := by
  apply event_probability_le_of_ae_sections ν μ (fun q => H q i) (hH i)
  filter_upwards [hgood] with u hu
  obtain ⟨A,hA⟩ := hu
  have hs : {Z | H (u,Z) i} = {Z | Setup.failure A Z i F t ell ht he} := by
    ext Z
    exact hA Z i
  rw [hs]
  exact MainUpper.failure_probability_le A μ hμ F t ell ht he i

/-- The same a.e.-admissible statement bounds by the independently defined
actual deterministic supremum, prior to substituting its closed formula. -/
theorem ae_admissible_probability_le_finiteRankGamma
    (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure (Fin (m+1) → Block UniversalCovariate n)) [IsProbabilityMeasure μ]
    (hμ : Exchangeable μ)
    (H : U × (Fin (m+1) → Block UniversalCovariate n) → Fin (m+1) → Prop)
    (hH : ∀ j, MeasurableSet {q | H q j}) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (hgood : ∀ᵐ u ∂ν, ∃ A : Learner UniversalCovariate n, ∀ Z j,
      H (u,Z) j ↔ Setup.failure A Z j (failureRank alpha n) t ell ht he) :
    (ν.prod μ).real {q | H q (Fin.last m)} ≤ finiteRankGamma m n alpha t ell ht he := by
  apply event_probability_le_of_ae_sections ν μ (fun q => H q (Fin.last m)) (hH _)
  filter_upwards [hgood] with u hu
  obtain ⟨A,hA⟩ := hu
  have hs : {Z | H (u,Z) (Fin.last m)} =
      {Z | Setup.failure A Z (Fin.last m) (failureRank alpha n) t ell ht he} := by
    ext Z
    exact hA Z (Fin.last m)
  rw [hs]
  unfold finiteRankGamma
  apply le_csSup (deterministic_values_bddAbove m n alpha t ell ht he)
  exact ⟨A,μ,inferInstance,hμ,rfl⟩

/-- A.e.-admissible actual experiments. This deliberately also permits arbitrary
jointly measurable exceptional-seed behavior. On almost every seed, one actual
learner must generate all the label events simultaneously on every block array;
no probability bound or minimax conclusion is included in the definition. -/
def aeAdmissibleValues (ν : Measure U) (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : Set ℝ :=
  {r | ∃ (μ : Measure (Fin (m+1) → Block UniversalCovariate n))
    (H : U × (Fin (m+1) → Block UniversalCovariate n) → Fin (m+1) → Prop),
    IsProbabilityMeasure μ ∧ Exchangeable μ ∧ (∀ j, MeasurableSet {q | H q j}) ∧
    (∀ᵐ u ∂ν, ∃ A : Learner UniversalCovariate n, ∀ Z j,
      H (u,Z) j ↔ Setup.failure A Z j (failureRank alpha n) t ell ht he) ∧
    r = (ν.prod μ).real {q | H q (Fin.last m)}}

def aeAdmissibleGamma (ν : Measure U) (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : ℝ :=
  sSup (aeAdmissibleValues ν m n alpha t ell ht he)

/-- The actual jointly measurable source families belong to the a.e.-admissible
experiment class by the joint failure measurability theorem, not by an assumed
measurable-event conclusion. -/
lemma randomizedValues_subset_aeAdmissibleValues (ν : Measure U) (m n : ℕ)
    (alpha : ℝ) (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    randomizedValues ν m n alpha t ell ht he ⊆ aeAdmissibleValues ν m n alpha t ell ht he := by
  rintro r ⟨A,μ,hprob,hμ,hr⟩
  refine ⟨μ,(fun q j => failure A q j (failureRank alpha n) t ell ht he),hprob,hμ,?_,?_,hr⟩
  · intro j
    exact measurableSet_failure A j (failureRank alpha n) t ell ht he
  · exact Filter.Eventually.of_forall (fun u => ⟨A.sectionLearner u,fun Z j => Iff.rfl⟩)

lemma aeAdmissibleValues_nonempty (ν : Measure U) [IsProbabilityMeasure ν]
    (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    (aeAdmissibleValues ν m n alpha t ell ht he).Nonempty :=
  (randomizedValues_nonempty ν m n alpha t ell ht he).mono
    (randomizedValues_subset_aeAdmissibleValues ν m n alpha t ell ht he)

lemma aeAdmissibleValues_bddAbove (ν : Measure U) [IsProbabilityMeasure ν]
    (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    BddAbove (aeAdmissibleValues ν m n alpha t ell ht he) := by
  refine ⟨finiteRankGamma m n alpha t ell ht he,?_⟩
  rintro r ⟨μ,H,hprob,hμ,hH,hgood,rfl⟩
  letI : IsProbabilityMeasure μ := hprob
  exact ae_admissible_probability_le_finiteRankGamma ν μ hμ H hH alpha t ell ht he hgood

/-- Even the explicit a.e.-admissible experiment class with arbitrary exceptional
null-seed behavior has precisely the original deterministic worst-case value. -/
theorem aeAdmissibleGamma_eq_finiteRankGamma (ν : Measure U) [IsProbabilityMeasure ν]
    (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    aeAdmissibleGamma ν m n alpha t ell ht he = finiteRankGamma m n alpha t ell ht he := by
  apply le_antisymm
  · unfold aeAdmissibleGamma
    apply csSup_le (aeAdmissibleValues_nonempty ν m n alpha t ell ht he)
    rintro r ⟨μ,H,hprob,hμ,hH,hgood,rfl⟩
    letI : IsProbabilityMeasure μ := hprob
    exact ae_admissible_probability_le_finiteRankGamma ν μ hμ H hH alpha t ell ht he hgood
  · apply le_trans (finiteRankGamma_le_randomizedGamma ν m n alpha t ell ht he)
    unfold randomizedGamma aeAdmissibleGamma
    apply csSup_le (randomizedValues_nonempty ν m n alpha t ell ht he)
    intro r hr
    exact le_csSup (aeAdmissibleValues_bddAbove ν m n alpha t ell ht he)
      (randomizedValues_subset_aeAdmissibleValues ν m n alpha t ell ht he hr)

theorem aeAdmissibleGamma_eq_failureRate (ν : Measure U) [IsProbabilityMeasure ν]
    (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    aeAdmissibleGamma ν m n alpha t ell ht he = RankFrontier.failureRate m (failureRank alpha n) t ell := by
  rw [aeAdmissibleGamma_eq_finiteRankGamma ν m n alpha t ell ht he,
    MainExact.finiteRankGamma_eq m n alpha ha ha1 t ell ht he]

/-- The same coherent evaluator with the source's actual infinite-endpoint rule. -/
def extendedFailure (A : Family U X n) (q : U × (Fin (m+1) → Block X n))
    (i : Fin (m+1)) (F t ell : ℕ) : Prop :=
  ExtendedRule.failure (A.sectionLearner q.1) q.2 i F t ell

/-- Either source rank-zero axis remains failure-free for every realized seed. -/
theorem extended_failure_probability_zero (A : Family U X n) (ν : Measure U)
    (μ : Measure (Fin (m+1) → Block X n)) (i : Fin (m+1)) (F t ell : ℕ)
    (hF : 0 < F) (hell : ell ≤ m) (hz : t = 0 ∨ ell = 0) :
    (ν.prod μ).real {q | extendedFailure A q i F t ell} = 0 := by
  have hevent : {q | extendedFailure A q i F t ell} = ∅ := by
    ext q
    simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
    exact ExtendedRule.no_failure_zero_rank (A.sectionLearner q.1) q.2 i hF hell hz
  rw [hevent,measureReal_empty]

/-- Joint measurability for all source ranks, including the infinite endpoints. -/
theorem measurableSet_extendedFailure (A : Family U X n) (i : Fin (m+1))
    (F t ell : ℕ) (hF : 0 < F) (htn : t ≤ n) (hell : ell ≤ m) :
    MeasurableSet {q | extendedFailure A q i F t ell} := by
  by_cases hz : t = 0 ∨ ell = 0
  · have hevent : {q | extendedFailure A q i F t ell} = ∅ := by
      ext q
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      exact ExtendedRule.no_failure_zero_rank (A.sectionLearner q.1) q.2 i hF hell hz
    rw [hevent]
    exact MeasurableSet.empty
  · have ht : 1 ≤ t ∧ t ≤ n := by omega
    have he : 1 ≤ ell ∧ ell ≤ m := by omega
    have hevent : {q | extendedFailure A q i F t ell} = {q | failure A q i F t ell ht he} := by
      ext q
      exact ExtendedRule.failure_finite ht he (A.sectionLearner q.1) q.2 i F
    rw [hevent]
    exact measurableSet_failure A i F t ell ht he

lemma constantFamily_extended_probability (A : Learner X n)
    (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ]
    (i : Fin (m+1)) (F t ell : ℕ) :
    (ν.prod μ).real {q | extendedFailure (constantFamily A) q i F t ell} =
      μ.real {Z | ExtendedRule.failure A Z i F t ell} := by
  have heq : {q : U × (Fin (m+1) → Block X n) |
      extendedFailure (constantFamily A) q i F t ell} =
      Set.univ ×ˢ {Z | ExtendedRule.failure A Z i F t ell} := by
    ext q
    simp only [extendedFailure,sectionLearner_constantFamily,Set.mem_setOf_eq,
      Set.mem_prod,Set.mem_univ,true_and]
  rw [heq,measureReal_prod_prod]
  simp

/-- The independent randomized statistical supremum for the actual EReal rule. -/
def extendedRandomizedValues (ν : Measure U) (m n : ℕ) (alpha : ℝ) (t ell : ℕ) : Set ℝ :=
  {r | ∃ (A : Family U UniversalCovariate n)
    (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
    IsProbabilityMeasure μ ∧ Exchangeable μ ∧
    r = (ν.prod μ).real {q | extendedFailure A q (Fin.last m) (failureRank alpha n) t ell}}

def extendedRandomizedGamma (ν : Measure U) (m n : ℕ) (alpha : ℝ) (t ell : ℕ) : ℝ :=
  sSup (extendedRandomizedValues ν m n alpha t ell)

lemma extendedRandomizedValues_nonempty (ν : Measure U) [IsProbabilityMeasure ν]
    (m n : ℕ) (alpha : ℝ) (t ell : ℕ) :
    (extendedRandomizedValues ν m n alpha t ell).Nonempty := by
  obtain ⟨r,A,μ,hprob,hμ,hr⟩ := ExtendedRule.minimaxValues_nonempty m n alpha t ell
  letI : IsProbabilityMeasure μ := hprob
  refine ⟨r,constantFamily A,μ,hprob,hμ,?_⟩
  rw [constantFamily_extended_probability A ν μ (Fin.last m) (failureRank alpha n) t ell]
  exact hr

lemma extendedRandomizedGamma_zero (ν : Measure U) [IsProbabilityMeasure ν]
    (m n : ℕ) (alpha : ℝ) (t ell : ℕ) (hell : ell ≤ m) (hz : t = 0 ∨ ell = 0) :
    extendedRandomizedGamma ν m n alpha t ell = 0 := by
  have hF : 0 < failureRank alpha n := by unfold failureRank; omega
  have hall : ∀ r ∈ extendedRandomizedValues ν m n alpha t ell, r = 0 := by
    rintro r ⟨A,μ,hprob,hμ,hr⟩
    rw [extended_failure_probability_zero A ν μ (Fin.last m) (failureRank alpha n) t ell hF hell hz] at hr
    exact hr
  have hset : extendedRandomizedValues ν m n alpha t ell = {0} := by
    ext r
    constructor
    · intro hr
      exact Set.mem_singleton_iff.mpr (hall r hr)
    · intro hr
      have hr0 : r = 0 := Set.mem_singleton_iff.mp hr
      subst r
      obtain ⟨v,hv⟩ := extendedRandomizedValues_nonempty ν m n alpha t ell
      rwa [hall v hv] at hv
  unfold extendedRandomizedGamma
  rw [hset,csSup_singleton]

/-- Exact unchanged worst-case value for every source rank cell, with the actual
extended endpoint convention, including both rank-zero axes. -/
theorem extendedRandomizedGamma_eq_gamma (ν : Measure U) [IsProbabilityMeasure ν]
    (m n : ℕ) (alpha : ℝ) (t ell : ℕ) (htn : t ≤ n) (hell : ell ≤ m) :
    extendedRandomizedGamma ν m n alpha t ell = ExtendedRule.gamma m n alpha t ell := by
  by_cases hz : t = 0 ∨ ell = 0
  · rw [extendedRandomizedGamma_zero ν m n alpha t ell hell hz,
      ExtendedRule.gamma_zero m n alpha t ell hell hz]
  · have ht : 1 ≤ t ∧ t ≤ n := by omega
    have he : 1 ≤ ell ∧ ell ≤ m := by omega
    have hvalues : extendedRandomizedValues ν m n alpha t ell = randomizedValues ν m n alpha t ell ht he := by
      unfold extendedRandomizedValues randomizedValues
      simp only [extendedFailure,failure,ExtendedRule.failure_finite ht he]
    unfold extendedRandomizedGamma
    rw [hvalues]
    change randomizedGamma ν m n alpha t ell ht he = _
    rw [randomizedGamma_eq_finiteRankGamma ν m n alpha t ell ht he,
      ExtendedRule.gamma_finite m n alpha t ell ht he]

/-- A.e.-admissibility also preserves the full source extended-rule upper value.
The exceptional seed behavior may be arbitrary, including at zero-rank cells. -/
theorem ae_admissible_probability_le_gamma
    (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure (Fin (m+1) → Block UniversalCovariate n)) [IsProbabilityMeasure μ]
    (hμ : Exchangeable μ)
    (H : U × (Fin (m+1) → Block UniversalCovariate n) → Fin (m+1) → Prop)
    (hH : ∀ j, MeasurableSet {q | H q j}) (alpha : ℝ) (t ell : ℕ)
    (htn : t ≤ n) (hell : ell ≤ m)
    (hgood : ∀ᵐ u ∂ν, ∃ A : Learner UniversalCovariate n, ∀ Z j,
      H (u,Z) j ↔ ExtendedRule.failure A Z j (failureRank alpha n) t ell) :
    (ν.prod μ).real {q | H q (Fin.last m)} ≤ ExtendedRule.gamma m n alpha t ell := by
  by_cases hz : t = 0 ∨ ell = 0
  · rw [ExtendedRule.gamma_zero m n alpha t ell hell hz]
    apply event_probability_le_of_ae_sections ν μ (fun q => H q (Fin.last m)) (hH _)
    filter_upwards [hgood] with u hu
    obtain ⟨A,hA⟩ := hu
    have hF : 0 < failureRank alpha n := by unfold failureRank; omega
    have hevent : {Z | H (u,Z) (Fin.last m)} = ∅ := by
      ext Z
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      intro h
      exact ExtendedRule.no_failure_zero_rank A Z (Fin.last m) hF hell hz ((hA Z _).mp h)
    rw [hevent,measureReal_empty]
  · have ht : 1 ≤ t ∧ t ≤ n := by omega
    have he : 1 ≤ ell ∧ ell ≤ m := by omega
    rw [ExtendedRule.gamma_finite m n alpha t ell ht he]
    apply ae_admissible_probability_le_finiteRankGamma ν μ hμ H hH alpha t ell ht he
    filter_upwards [hgood] with u hu
    obtain ⟨A,hA⟩ := hu
    exact ⟨A,fun Z j => (hA Z j).trans (ExtendedRule.failure_finite ht he A Z j _)⟩

end
end MEJF.CoherentSeed
