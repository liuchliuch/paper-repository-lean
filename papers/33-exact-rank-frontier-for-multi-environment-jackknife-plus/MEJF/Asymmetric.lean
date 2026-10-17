import MEJF.MainExact
import Mathlib.Data.Fin.Rev

/-! # The actual asymmetric endpoint rule (Theorem 6.2)

The asymmetric minimax quantity below is independently defined as a supremum
over the same measurable learners and exchangeable probability laws as the
symmetric rule. Its two endpoint ranks are kept separate.
-/
namespace MEJF.Asymmetric

open Finset MeasureTheory MEJF.Setup MEJF.Exchangeability
noncomputable section
attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X] {m n : ℕ}

def maxRankProof {lm lp : ℕ} (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) :
    1 ≤ max lm lp ∧ max lm lp ≤ m := ⟨by omega, by omega⟩

/-- The interval in (6.15), with independently chosen positive endpoint ranks. -/
def interval (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n)
    (t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) : Set ℝ :=
  Set.Icc (lowerEndpoint A Z i j t lm ht hm) (upperEndpoint A Z i j t lp ht hp)

def covered (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n)
    (t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) : Prop :=
  (Z i j).2 ∈ interval A Z i j t lm lp ht hm hp

def failure (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1))
    (F t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) : Prop :=
  F ≤ (univ.filter fun j => ¬ covered A Z i j t lm lp ht hm hp).card

/-- Increasing a lower rank raises the actual sorted lower endpoint. -/
lemma lowerEndpoint_mono_rank (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i : Fin (m+1)) (j : Fin n) (t l r : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (hl : 1 ≤ l ∧ l ≤ m) (hr : 1 ≤ r ∧ r ≤ m) (hlr : l ≤ r) :
    lowerEndpoint A Z i j t l ht hl ≤ lowerEndpoint A Z i j t r ht hr := by
  apply OrderStatistics.stat_monotone_rank
  change l - 1 ≤ r - 1
  omega

/-- Increasing an upper trimming rank lowers the actual sorted upper endpoint. -/
lemma upperEndpoint_antitone_rank (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i : Fin (m+1)) (j : Fin n) (t l r : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (hl : 1 ≤ l ∧ l ≤ m) (hr : 1 ≤ r ∧ r ≤ m) (hlr : l ≤ r) :
    upperEndpoint A Z i j t r ht hr ≤ upperEndpoint A Z i j t l ht hl := by
  apply OrderStatistics.stat_monotone_rank
  change m - r ≤ m - l
  omega

/-- Equation (6.17), for every actual data array and designated covariate. -/
theorem symmetric_max_interval_subset (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i : Fin (m+1)) (j : Fin n) (t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) :
    interval A Z i j t (max lm lp) (max lm lp) ht (maxRankProof hm hp) (maxRankProof hm hp) ⊆
      interval A Z i j t lm lp ht hm hp := by
  exact Set.Icc_subset_Icc
    (lowerEndpoint_mono_rank A Z i j t lm (max lm lp) ht hm (maxRankProof hm hp) (le_max_left _ _))
    (upperEndpoint_antitone_rank A Z i j t lp (max lm lp) ht hp (maxRankProof hm hp) (le_max_right _ _))

lemma failure_implies_symmetric_max (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i : Fin (m+1)) (F t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) :
    failure A Z i F t lm lp ht hm hp →
      Setup.failure A Z i F t (max lm lp) ht (maxRankProof hm hp) := by
  intro hf
  apply hf.trans
  apply Finset.card_mono
  intro j hj
  simp only [mem_filter, mem_univ, true_and] at *
  intro hs
  exact hj (symmetric_max_interval_subset A Z i j t lm lp ht hm hp hs)

lemma measurableSet_covered (A : Learner X n) (i : Fin (m+1)) (j : Fin n)
    (t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) :
    MeasurableSet {Z : Fin (m+1) → Block X n | covered A Z i j t lm lp ht hm hp} :=
  (measurableSet_le (Setup.measurable_lowerEndpoint A i j t lm ht hm)
    (Setup.measurable_response i j)).inter
      (measurableSet_le (Setup.measurable_response i j)
        (Setup.measurable_upperEndpoint A i j t lp ht hp))

lemma measurableSet_failure (A : Learner X n) (i : Fin (m+1)) (F t lm lp : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) :
    MeasurableSet {Z : Fin (m+1) → Block X n | failure A Z i F t lm lp ht hm hp} := by
  have hc : Measurable (fun Z : Fin (m+1) → Block X n =>
      (univ.filter fun j => ¬ covered A Z i j t lm lp ht hm hp).card) := by
    have hsum : Measurable (fun Z : Fin (m+1) → Block X n =>
        ∑ j : Fin n, if ¬ covered A Z i j t lm lp ht hm hp then (1 : ℕ) else 0) := by
      apply Finset.measurable_sum
      intro j _
      exact Measurable.ite (measurableSet_covered A i j t lm lp ht hm hp).compl
        measurable_const measurable_const
    simpa only [Finset.sum_boole] using hsum
  exact measurableSet_le measurable_const hc

lemma covered_relabel (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (e : Equiv.Perm (Fin (m+1))) (i : Fin (m+1)) (j : Fin n)
    (t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) :
    covered A (relabel e Z) (e i) j t lm lp ht hm hp ↔ covered A Z i j t lm lp ht hm hp := by
  unfold covered interval
  rw [SetupEquivariance.lowerEndpoint_relabel, SetupEquivariance.upperEndpoint_relabel]
  simp only [relabel, Function.comp_apply, Equiv.symm_apply_apply]

lemma failure_equivariant (A : Learner X n) (F t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) :
    Equivariant (fun Z : Fin (m+1) → Block X n => fun i => failure A Z i F t lm lp ht hm hp) := by
  intro e Z i
  unfold failure
  simp only [covered_relabel]

/-- Uniform actual-law upper bound, obtained from the narrower symmetric rule. -/
theorem failure_probability_le (A : Learner X n)
    (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ] (hex : Exchangeable μ)
    (F t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) (i : Fin (m+1)) :
    μ.real {Z | failure A Z i F t lm lp ht hm hp} ≤ RankFrontier.failureRate m F t (max lm lp) := by
  apply (measureReal_mono (μ := μ) (fun Z hz =>
    failure_implies_symmetric_max A Z i F t lm lp ht hm hp hz)).trans
  exact MainUpper.failure_probability_le A μ hex F t (max lm lp) ht (maxRankProof hm hp) i

/-- A sorted tuple negates by reversing its rank, retaining all repeated values. -/
lemma stat_neg (a : Fin m → ℝ) (k : Fin m) :
    OrderStatistics.stat (fun i => -a i) k = -OrderStatistics.stat a k.rev := by
  have hmono : Monotone ((fun i => -a i) ∘ ((Fin.revPerm : Equiv.Perm (Fin m)).trans (Tuple.sort a))) := by
    intro i j hij
    change -OrderStatistics.stat a i.rev ≤ -OrderStatistics.stat a j.rev
    exact neg_le_neg (OrderStatistics.stat_monotone_rank a (Fin.rev_le_rev.mpr hij))
  exact congrFun (Tuple.unique_monotone (Tuple.monotone_sort (fun i => -a i)) hmono) k

lemma innerIndex_same (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) :
    (Setup.innerIndex n t ht) = ⟨n-t, by omega⟩ := rfl

lemma lowerIndex_rev (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) :
    (Setup.lowerIndex m ell he).rev = Setup.upperIndex m ell he := by
  apply Fin.ext
  simp only [Fin.val_rev, Setup.lowerIndex, Setup.upperIndex]
  omega

lemma upperIndex_rev (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) :
    (Setup.upperIndex m ell he).rev = Setup.lowerIndex m ell he := by
  rw [← lowerIndex_rev ell he, Fin.rev_rev]

section Reflection
variable [MeasurableSingletonClass X]
open PredictionTable

/-- Negating the prescribed predictions preserves every actual zero-response radius. -/
theorem reflected_radius (p : Fin (m+1) → Fin (m+1) → Fin n → ℝ)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (u v : Fin (m+1)) (huv : u ≠ v) :
    Setup.radius (tableLearner (fun u v j => -p u v j) emb) (modelData emb) u v t ht =
      Setup.radius (tableLearner p emb) (modelData emb) u v t ht := by
  rw [model_radius _ emb hinj (by omega) u v huv t ht, model_radius p emb hinj (by omega) u v huv t ht]
  simp only [abs_neg]

/-- The reflected actual lower endpoint is the negative original upper endpoint. -/
theorem reflected_lowerEndpoint (p : Fin (m+1) → Fin (m+1) → Fin n → ℝ)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (u : Fin (m+1)) (j : Fin n) :
    Setup.lowerEndpoint (tableLearner (fun u v j => -p u v j) emb) (modelData emb) u j t ell ht he =
      -Setup.upperEndpoint (tableLearner p emb) (modelData emb) u j t ell ht he := by
  unfold Setup.lowerEndpoint Setup.upperEndpoint
  have heq : (fun k : Fin m =>
      Setup.pairPrediction (tableLearner (fun u v j => -p u v j) emb) (modelData emb) u (u.succAbove k) (modelData emb u j).1 -
        Setup.radius (tableLearner (fun u v j => -p u v j) emb) (modelData emb) (u.succAbove k) u t ht) =
      fun k : Fin m => -(Setup.pairPrediction (tableLearner p emb) (modelData emb) u (u.succAbove k) (modelData emb u j).1 +
        Setup.radius (tableLearner p emb) (modelData emb) (u.succAbove k) u t ht) := by
    funext k
    rw [reflected_radius p emb hinj t ht _ _ (u.succAbove_ne k)]
    change Setup.pairPrediction _ _ _ _ (emb (u,j)) - _ = -(Setup.pairPrediction _ _ _ _ (emb (u,j)) + _)
    rw [model_pairPrediction _ emb hinj (by omega) _ _ (u.ne_succAbove k) j,
      model_pairPrediction p emb hinj (by omega) _ _ (u.ne_succAbove k) j]
    ring
  rw [heq, stat_neg, lowerIndex_rev]

/-- The reflected actual upper endpoint is the negative original lower endpoint. -/
theorem reflected_upperEndpoint (p : Fin (m+1) → Fin (m+1) → Fin n → ℝ)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (u : Fin (m+1)) (j : Fin n) :
    Setup.upperEndpoint (tableLearner (fun u v j => -p u v j) emb) (modelData emb) u j t ell ht he =
      -Setup.lowerEndpoint (tableLearner p emb) (modelData emb) u j t ell ht he := by
  unfold Setup.lowerEndpoint Setup.upperEndpoint
  have heq : (fun k : Fin m =>
      Setup.pairPrediction (tableLearner (fun u v j => -p u v j) emb) (modelData emb) u (u.succAbove k) (modelData emb u j).1 +
        Setup.radius (tableLearner (fun u v j => -p u v j) emb) (modelData emb) (u.succAbove k) u t ht) =
      fun k : Fin m => -(Setup.pairPrediction (tableLearner p emb) (modelData emb) u (u.succAbove k) (modelData emb u j).1 -
        Setup.radius (tableLearner p emb) (modelData emb) (u.succAbove k) u t ht) := by
    funext k
    rw [reflected_radius p emb hinj t ht _ _ (u.succAbove_ne k)]
    change Setup.pairPrediction _ _ _ _ (emb (u,j)) + _ = -(Setup.pairPrediction _ _ _ _ (emb (u,j)) - _)
    rw [model_pairPrediction _ emb hinj (by omega) _ _ (u.ne_succAbove k) j,
      model_pairPrediction p emb hinj (by omega) _ _ (u.ne_succAbove k) j]
    ring
  rw [heq, stat_neg, upperIndex_rev]

end Reflection

/-- The same universal pointwise label-count bound holds for asymmetric ranks. -/
theorem failure_label_count_le (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (F t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) :
    (univ.filter fun i => failure A Z i F t lm lp ht hm hp).card ≤
      RankFrontier.failureCount m F t (max lm lp) := by
  have hs : (univ.filter fun i => failure A Z i F t lm lp ht hm hp) ⊆
      (univ.filter fun i => Setup.failure A Z i F t (max lm lp) ht (maxRankProof hm hp)) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at *
    exact failure_implies_symmetric_max A Z i F t lm lp ht hm hp hi
  exact (card_mono hs).trans (by
    simpa only [RankFrontier.failureCount, RankFrontier.capacity] using
      DeterministicUpper.learner_failure_label_count_le A Z F t (max lm lp) ht (maxRankProof hm hp))

section Sharpness
variable [MeasurableSingletonClass X]
open PredictionTable

/-- An actual measurable learner attains the asymmetric count. The lower-side
construction is used when its rank is larger; otherwise the table is reflected. -/
theorem exists_exact_failure_count_model (m n F t lm lp : ℕ) (hmpos : 1 ≤ m)
    (hF : 1 ≤ F) (hFn : F ≤ n) (ht : 1 ≤ t ∧ t ≤ n)
    (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb) :
    ∃ (A : Learner X n) (Z : Fin (m+1) → Block X n),
      (univ.filter fun i => failure A Z i F t lm lp ht hm hp).card =
        RankFrontier.failureCount m F t (max lm lp) := by
  obtain ⟨R, S, B, hasym, hScard, hmark, hunmark, hrows, hzero⟩ :=
    Sharpness.exists_sharpness_array m n F t (max lm lp) hmpos hFn ht.1 (maxRankProof hm hp)
  let p := incidenceTable R B
  let q : Fin (m+1) → Fin (m+1) → Fin n → ℝ := if lm < lp then (fun u v j => -p u v j) else p
  let A := tableLearner q emb
  let Z := modelData emb
  have hsize : S.card = RankFrontier.failureCount m F t (max lm lp) := by
    simpa only [RankFrontier.failureCount, RankFrontier.capacity] using
      hScard.trans (Sharpness.graph_size_formula m F t (max lm lp) (maxRankProof hm hp))
  have hlower : ∀ u ∈ S, ∀ j : Fin n, j.val < F →
      lowerEndpoint (tableLearner p emb) Z u j t (max lm lp) ht (maxRankProof hm hp) = 1 := by
    intro u hu j hj
    rw [model_lowerEndpoint_incidence R (fun {u v} => hasym u v) B emb hinj t (max lm lp)
      ht (maxRankProof hm hp) hmark hunmark]
    exact incidence_lower_endpoint R B u j u.succAbove (by omega) (maxRankProof hm hp).2 (hrows u hu j hj)
  have hsel : ∀ u ∈ S, failure A Z u F t lm lp ht hm hp := by
    intro u hu
    have hs : Sharpness.firstRows F n ⊆ (univ.filter fun j => ¬ covered A Z u j t lm lp ht hm hp) := by
      intro j hj
      have hjF : j.val < F := by simpa [Sharpness.firstRows] using hj
      simp only [mem_filter, mem_univ, true_and]
      intro hc
      change lowerEndpoint A Z u j t lm ht hm ≤ 0 ∧
        0 ≤ upperEndpoint A Z u j t lp ht hp at hc
      by_cases hlp : lm < lp
      · have hmax : max lm lp = lp := max_eq_right (by omega)
        have href := reflected_upperEndpoint p emb hinj t lp ht hp u j
        have hl := hlower u hu j hjF
        have heq : A = tableLearner (fun u v j => -p u v j) emb := by simp [A, q, hlp]
        rw [heq, href] at hc
        simp only [hmax] at hl
        rw [hl] at hc
        norm_num at hc
      · have hmax : max lm lp = lm := max_eq_left (by omega)
        have heq : A = tableLearner p emb := by simp [A, q, hlp]
        have hl := hlower u hu j hjF
        simp only [hmax] at hl
        rw [heq, hl] at hc
        norm_num at hc
    have hc := card_mono hs
    rw [Sharpness.firstRows_card hFn] at hc
    exact hc
  refine ⟨A, Z, le_antisymm (failure_label_count_le A Z F t lm lp ht hm hp) ?_⟩
  rw [← hsize]
  apply card_mono
  intro u hu
  exact mem_filter.mpr ⟨mem_univ _, hsel u hu⟩

end Sharpness

/-- A finite exchangeable block law and one admissible learner attain (6.16). -/
theorem exists_attaining_model (m n F t lm lp : ℕ) (hmpos : 1 ≤ m)
    (hF : 1 ≤ F) (hFn : F ≤ n) (ht : 1 ≤ t ∧ t ≤ n)
    (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) :
    ∃ (A : Learner UniversalCovariate n) (Z : Fin (m+1) → Block UniversalCovariate n),
      (FiniteExchangeable.blockPermutationLaw Z).real
        {W | failure A W (Fin.last m) F t lm lp ht hm hp} =
      RankFrontier.failureRate m F t (max lm lp) := by
  obtain ⟨A, Z, hcount⟩ := exists_exact_failure_count_model m n F t lm lp hmpos hF hFn ht hm hp
    (PredictionTable.unitEmbedding (m+1) n) (PredictionTable.unitEmbedding (m+1) n).injective
  refine ⟨A, Z, ?_⟩
  have hp' := FiniteExchangeable.blockPermutationLaw_equivariant_probability Z
    (fun W i => failure A W i F t lm lp ht hm hp)
    (fun i => measurableSet_failure A i F t lm lp ht hm hp)
    (failure_equivariant A F t lm lp ht hm hp) (Fin.last m)
  simpa only [hcount, Fintype.card_fin, RankFrontier.failureRate] using hp'

/-- The actual asymmetric minimax supremum, on the original universal experiment. -/
def gamma (m n : ℕ) (alpha : ℝ) (t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) : ℝ :=
  sSup {r : ℝ | ∃ (A : Learner UniversalCovariate n)
    (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
    IsProbabilityMeasure μ ∧ Exchangeable μ ∧
    r = μ.real {Z | failure A Z (Fin.last m) (failureRank alpha n) t lm lp ht hm hp}}

/-- Theorem 6.2, preserving the original supremum and both endpoint ranks. -/
theorem gamma_eq (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) :
    gamma m n alpha t lm lp ht hm hp = RankFrontier.failureRate m (failureRank alpha n) t (max lm lp) := by
  have hnon : {r : ℝ | ∃ (A : Learner UniversalCovariate n)
      (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
      IsProbabilityMeasure μ ∧ Exchangeable μ ∧
      r = μ.real {Z | failure A Z (Fin.last m) (failureRank alpha n) t lm lp ht hm hp}}.Nonempty := by
    obtain ⟨r, A, μ, hprob, hex, hr⟩ := MainUpper.minimax_values_nonempty m n alpha t (max lm lp) ht (maxRankProof hm hp)
    exact ⟨_, A, μ, hprob, hex, rfl⟩
  have hb : BddAbove {r : ℝ | ∃ (A : Learner UniversalCovariate n)
      (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
      IsProbabilityMeasure μ ∧ Exchangeable μ ∧
      r = μ.real {Z | failure A Z (Fin.last m) (failureRank alpha n) t lm lp ht hm hp}} := by
    refine ⟨RankFrontier.failureRate m (failureRank alpha n) t (max lm lp), ?_⟩
    intro r hr
    obtain ⟨A, μ, hprob, hex, rfl⟩ := hr
    letI : IsProbabilityMeasure μ := hprob
    exact failure_probability_le A μ hex _ t lm lp ht hm hp (Fin.last m)
  unfold gamma
  apply le_antisymm
  · apply csSup_le hnon
    intro r hr
    obtain ⟨A, μ, hprob, hex, rfl⟩ := hr
    letI : IsProbabilityMeasure μ := hprob
    exact failure_probability_le A μ hex _ t lm lp ht hm hp (Fin.last m)
  · have hn : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hFn : failureRank alpha n ≤ n := by
      unfold failureRank
      have hx : alpha * (n : ℝ) < n := by nlinarith
      have hh := (Nat.floor_lt (mul_nonneg ha hnR.le)).mpr hx
      omega
    obtain ⟨A, Z, heq⟩ := exists_attaining_model m n (failureRank alpha n) t lm lp
      (by omega) (by unfold failureRank; omega) hFn ht hm hp
    apply le_csSup hb
    exact ⟨A, FiniteExchangeable.blockPermutationLaw Z, by infer_instance,
      FiniteExchangeable.blockPermutationLaw_exchangeable Z, heq.symm⟩

/-- The two actual statistical minimax values coincide, despite interval inclusion. -/
theorem gamma_eq_symmetric (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m) :
    gamma m n alpha t lm lp ht hm hp =
      Setup.finiteRankGamma m n alpha t (max lm lp) ht (maxRankProof hm hp) := by
  rw [gamma_eq m n alpha ha ha1 t lm lp ht hm hp,
    MainExact.finiteRankGamma_eq m n alpha ha ha1 t (max lm lp) ht (maxRankProof hm hp)]

end
end MEJF.Asymmetric
