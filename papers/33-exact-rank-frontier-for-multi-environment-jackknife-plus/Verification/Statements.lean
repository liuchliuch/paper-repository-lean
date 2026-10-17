import MEJF.MainResults
import MEJF.RankFrontier
import MEJF.ExtendedRule
import MEJF.ActualPareto
import MEJF.RankAlgorithm
import MEJF.ActualAsymptotic
import MEJF.LimitingFrontier
import MEJF.DeterministicUpper
import MEJF.GraphBound
import MEJF.ExtremalGraph
import MEJF.Incidence
import MEJF.TieFreeSharpness
import MEJF.HeterogeneousProbability
import MEJF.HeterogeneousFrontier
import MEJF.HeterogeneousAlgorithm
import MEJF.HeterogeneousSortingInput
import MEJF.HeterogeneousTieFreeLaw
import MEJF.Asymmetric
import MEJF.RandomizedProbability
import MEJF.RandomizedTieFree
import MEJF.RankDP
import MEJF.StabilityProbability
import MEJF.StabilityExtended
import MEJF.StabilityFrontier
import MEJF.StabilityAsymptotic
import MEJF.Scaling
import MEJF.SwapSharpness
import MEJF.EfficiencyCompletion
import MEJF.Efficiency
import MEJF.AsymmetricFrontier
import MEJF.RankCells
import MEJF.CoherentSeed

/-! Independent literal proposition contracts. No contract uses the type of a
production theorem by reflection, an abbreviation of a theorem, or an assumed
certificate containing the requested conclusion. The types below are written
out separately from their production proofs. Challenge holes live elsewhere.
All official verification is deferred by the user. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open MEJF MeasureTheory Finset Filter Topology
set_option linter.unusedVariables false
open scoped BigOperators ENNReal NNReal
namespace Paper33.Contracts

section
open MEJF.Setup MEJF.RankFrontier MEJF.MainResults

/- Source S2.Thmtheorem1, S3.Thmtheorem1; production MEJF.MainResults.exact_failure_law. -/
def s3_exact_failure : Prop :=
  ∀ (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m),
  sSup {r : ℝ | ∃ (A : Setup.Learner Setup.UniversalCovariate n)
    (μ : Measure (Fin (m+1) → Setup.Block Setup.UniversalCovariate n)),
    IsProbabilityMeasure μ ∧ Exchangeability.Exchangeable μ ∧
    r = μ.real {Z | Setup.failure A Z (Fin.last m) (Setup.failureRank alpha n) t ell ht he}} =
      if failureRank alpha n < t then 1 else
        min 1 ((2 * (capacity m (failureRank alpha n) t ell : ℝ)+1) / (m+1 : ℕ))

end

section
open MEJF.Setup MEJF.RankFrontier MEJF.MainResults

/- Source S2.Thmtheorem1, S3.Thmtheorem2; production MEJF.MainResults.finite_validity_criterion. -/
def s3_finite_validity : Prop :=
  ∀ (m n : ℕ) (alpha delta : ℝ)
    (ha : 0 ≤ alpha) (ha1 : alpha < 1) (hd : 0 < delta) (hd1 : delta < 1)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (hD : 1 ≤ ⌊delta * (m+1 : ℕ)⌋₊),
  finiteRankGamma m n alpha t ell ht he ≤ delta ↔
      t ≤ failureRank alpha n ∧ ell ≤ halfCeil ⌊delta * (m+1 : ℕ)⌋₊ ∧
      halfCeil ⌊delta * (m+1 : ℕ)⌋₊ * (t-1)+1 ≤
        failureRank alpha n * (halfCeil ⌊delta * (m+1 : ℕ)⌋₊-ell+1)

end

section
open MEJF.Setup MEJF.RankFrontier MEJF.MainResults

/- Source S3.Thmtheorem2; production MEJF.MainResults.zero_floor_impossible. -/
def s3_zero_floor : Prop :=
  ∀ (m n : ℕ) (alpha delta : ℝ)
    (ha : 0 ≤ alpha) (ha1 : alpha < 1) (hd : 0 ≤ delta)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (hD : ⌊delta * (m+1 : ℕ)⌋₊ = 0),
  ¬ finiteRankGamma m n alpha t ell ht he ≤ delta

end

section
open MEJF.Setup MEJF.RankFrontier MEJF.MainResults

/- Source S3.Thmtheorem6, S3.Thmtheorem5; production MEJF.MainResults.complete_failure_iff. -/
def s3_complete_phase : Prop :=
  ∀ (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m),
  finiteRankGamma m n alpha t ell ht he = 1 ↔
      failureRank alpha n < t ∨
      (t ≤ failureRank alpha n ∧
        (failureRank alpha n-t+1)*halfCeil m ≤ failureRank alpha n*(ell-1))

end

section
open MEJF.Setup MEJF.RankFrontier MEJF.MainResults

/- Source S3.Thmtheorem5; production MEJF.MainResults.one_outer. -/
def s3_one_outer : Prop :=
  ∀ (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (hm : 1 ≤ m) (htF : t ≤ failureRank alpha n),
  finiteRankGamma m n alpha t 1 ht ⟨le_rfl,hm⟩ = 1/(m+1 : ℕ)

end

section
open MEJF.RankFrontier

/- Source S3.Thmtheorem5; production MEJF.RankFrontier.failureRate_low_inner. -/
def s3_one_inner : Prop :=
  ∀ {m F ell : ℕ} (hF : 0 < F) (hell : ell ≤ m + 1),
  failureRate m F 1 ell =
      (min (m + 1) (2 * (ell - 1) + 1) : ℕ) / (m + 1 : ℕ)

end

section
open MeasureTheory Finset MEJF.Setup MEJF.ExtendedRule

/- Source S3.Thmtheorem5, S3.Thmtheorem1; production MEJF.ExtendedRule.gamma_zero. -/
def s3_zero_rank_axes : Prop :=
  ∀ (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (hell : ell ≤ m) (hz : t = 0 ∨ ell = 0),
  gamma m n alpha t ell = 0

end

section
open MEJF.Setup MEJF.RankFrontier Finset MEJF.ActualPareto

/- Source S3.Thmtheorem3; production MEJF.ActualPareto.ranks_card. -/
def s3_pareto_card : Prop :=
  ∀ {m n : ℕ} {alpha delta : ℝ}
    (hn : 0 < n) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (hd : 0 < delta) (hd1 : delta < 1) (hD : 1 ≤ ⌊delta*(m+1:ℕ)⌋₊),
  (ranks m n alpha delta).card = min (failureRank alpha n) (halfCeil ⌊delta*(m+1:ℕ)⌋₊)

end

section
open MEJF.RankFrontier

/- Source S3.Thmtheorem3; production MEJF.RankFrontier.innerTop_eq_real_ceil. -/
def s3_inner_ceil : Prop :=
  ∀ {F q ell : ℕ} (hF : 0 < F) (hq : 0 < q)
    (helq : ell ≤ q),
  innerTop F q ell = ⌈(F : ℝ) * (q - ell + 1 : ℕ) / q⌉₊

end

section
open MEJF.RankFrontier

/- Source S3.Thmtheorem3; production MEJF.RankFrontier.pareto_iff_outer. -/
def s3_outer_enumeration : Prop :=
  ∀ {F q t ell : ℕ} (hF : 0 < F) (hFq : F ≤ q),
  Pareto F q t ell ↔ 1 ≤ t ∧ t ≤ F ∧ ell = outerTop F q t

end

section
open MEJF.RankFrontier

/- Source S3.Thmtheorem3; production MEJF.RankFrontier.pareto_iff_inner. -/
def s3_inner_enumeration : Prop :=
  ∀ {F q t ell : ℕ} (hq : 0 < q) (hqF : q ≤ F),
  Pareto F q t ell ↔ 1 ≤ ell ∧ ell ≤ q ∧ t = innerTop F q ell

end

section
open MEJF.RankFrontier Finset MEJF.RankAlgorithm

/- Source S3.Thmtheorem3; production MEJF.RankAlgorithm.enumerate_correct. -/
def s3_linear_enumeration : Prop :=
  ∀ {F q : ℕ} (hF : 0 < F) (hq : 0 < q),
  (enumerate F q).value.toFinset = paretoRanks F q

end

section
open MEJF.RankFrontier Finset MEJF.RankAlgorithm

/- Source S3.Thmtheorem3; production MEJF.RankAlgorithm.enumerate_ops_le. -/
def s3_linear_cost : Prop :=
  ∀ (F q : ℕ),
  (enumerate F q).ops ≤ 9*min F q+1

end

section
open MEJF.Setup Filter Topology MEJF.ActualAsymptotic

/- Source S3.Thmtheorem4; production MEJF.ActualAsymptotic.gamma_asymptotic_min. -/
def s3_actual_asymptotic : Prop :=
  ∀ {m n : ℕ → ℕ} {a b alpha : ℝ}
    (hmin : Tendsto (fun k => min (m k) (n k)) atTop atTop)
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (halpha : 0 < alpha) (halpha1 : alpha < 1),
  Tendsto (fun k => Gamma (m k) (n k) alpha a b)
      atTop (𝓝 (RankFrontier.limitingRate a b alpha))

end

section
open MEJF.Setup Filter Topology MEJF.ActualAsymptotic

/- Source S3.Thmtheorem4; production MEJF.ActualAsymptotic.limiting_validity_iff. -/
def s3_limiting_budget : Prop :=
  ∀ {a b alpha delta : ℝ}
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hd : 0 < delta) (hd1 : delta < 1),
  RankFrontier.limitingRate a b alpha ≤ delta ↔ a/alpha+2*b/delta ≤ 1

end

section
open MEJF.Setup Filter Topology MEJF.ActualAsymptotic

/- Source S3.Thmtheorem6; production MEJF.ActualAsymptotic.limiting_complete_failure_iff. -/
def s3_limiting_complete : Prop :=
  ∀ {a b alpha : ℝ} (halpha : 0 < alpha),
  RankFrontier.limitingRate a b alpha = 1 ↔
      alpha ≤ a ∨ (a < alpha ∧ 1 ≤ a/alpha+2*b)

end

section
open MEJF.RankFrontier MEJF.LimitingFrontier

/- Source S3.Thmtheorem4; production MEJF.LimitingFrontier.pareto_iff. -/
def s3_limiting_pareto : Prop :=
  ∀ (alpha delta a b : ℝ) (ha : 0 < alpha) (hd : 0 < delta)
    (hd1 : delta < 1) (hpa : 0 < a) (hpb : 0 < b),
  Pareto alpha delta a b ↔ a/alpha+2*b/delta=1

end

section
open MEJF.RankFrontier MEJF.LimitingFrontier

/- Source S7.Thmtheorem1; production MEJF.LimitingFrontier.factor_two_invalid. -/
def s7_factor_two_asymptotic : Prop :=
  ∀ (alpha delta a : ℝ) (ha : 0 < alpha)
    (hd : 0 < delta) (hd1 : delta < 1) (hpa : 0 < a),
  delta < limitingRate a (delta/2) alpha

end

section
open Finset MEJF.OrderStatistics MEJF.DeterministicUpper

/- Source S4.Thmtheorem1; production MEJF.DeterministicUpper.learner_aggregate_nonempty. -/
def s4_actual_nonempty : Prop :=
  ∀ {m n : ℕ} {X : Type*} [MeasurableSpace X]
    (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n)
    (i : Fin (m+1)) (j : Fin n) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) (htF : t ≤ F)
    (hlarge : m/2 < Incidence.threshold F m (m+1-ell) t),
  Setup.lowerEndpoint A Z i j t ell ht he ≤ Setup.upperEndpoint A Z i j t ell ht he

end

section
open Finset MEJF.OrderStatistics MEJF.DeterministicUpper

/- Source S4.Thmtheorem2; production MEJF.DeterministicUpper.learner_failure_forces_high_outdegree. -/
def s4_actual_degree : Prop :=
  ∀ {m n : ℕ} {X : Type*} [MeasurableSpace X]
    (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n)
    (i : Fin (m+1)) (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (he : 1 ≤ ell ∧ ell ≤ m) (htF : t ≤ F)
    (hfail : Setup.failure A Z i F t ell ht he),
  Incidence.threshold F m (m+1-ell) t ≤
      GraphBound.outDegree
        (fun i k => Setup.radius A Z k i t ht < Setup.radius A Z i k t ht) i

end

section
open Finset MEJF.GraphBound

/- Source S4.Thmtheorem3; production MEJF.GraphBound.highVertices_card_le. -/
def s4_oriented_count : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (R : α → α → Prop) [DecidableRel R] (hR : ∀ i j, R i j → ¬ R j i) (w : ℕ)
    (hw : w < Fintype.card α),
  (highVertices R w).card ≤
      min (Fintype.card α) (2 * (Fintype.card α - w) - 1)

end

section
open Finset MEJF.ExtremalGraph

/- Source S5.Thmtheorem1; production MEJF.ExtremalGraph.exists_extremal_oriented_graph. -/
def s5_extremal_graph : Prop :=
  ∀ (N w : ℕ) (hN : 2 ≤ N) (hw : w < N),
  ∃ (R : Fin N → Fin N → Prop) (S : Finset (Fin N)),
      (∀ u v, R u v → ¬ R v u) ∧
      S.card = min N (2 * (N-w) - 1) ∧
      (∀ u ∈ S, outdegree R u = w) ∧
      (∀ u ∉ S, outdegree R u = 0)

end

section
open Finset MEJF.Incidence

/- Source S5.Thmtheorem2; production MEJF.Incidence.realize_frontier. -/
def s5_incidence_realization : Prop :=
  ∀ {C : Type*} [Fintype C] [DecidableEq C]
    (F d t : ℕ) (marked : Finset C) (ht : 1 ≤ t) (hd : d ≤ Fintype.card C)
    (hmarked : marked.card = if F < t then 0 else threshold F (Fintype.card C) d t),
  ∃ B : Fin F → C → Prop, (∀ r, rowSum B r = d) ∧
      (∀ j ∈ marked, t ≤ colSum B j) ∧
      (∀ j ∉ marked, colSum B j ≤ t-1)

end

section
open Finset MeasureTheory MEJF.Setup MEJF.Exchangeability MEJF.PredictionTable MEJF.TieFreeSharpness

/- Source S5.Thmtheorem3; production MEJF.TieFreeSharpness.exists_quantitative_tieFree_model. -/
def s5_quantitative_tie_removal : Prop :=
  ∀ {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (m n F t ell : ℕ) (hm : 1 ≤ m) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (emb : Fin (m+1) × Fin n → X) (hinj : Function.Injective emb)
    (eta : ℝ) (heta : 0 < eta) (heta' : eta < 1/4),
  ∃ (R : Fin (m+1) → Fin (m+1) → Prop)
      (B : Fin (m+1) → Fin n → Fin (m+1) → Bool)
      (S : Finset (Fin (m+1))) (z : TieFreeTable.Vector (m+1) n),
      S.card = RankFrontier.failureCount m F t ell ∧
      (∀ a, |z a - TieFreeTable.baseline (incidenceTable R B) a| ≤ eta) ∧
      ActualTieFree (tableLearner (vectorPredictions z) emb) (vectorData emb z) t ell ht he ∧
      ∀ u, Setup.failure (tableLearner (vectorPredictions z) emb) (vectorData emb z) u F t ell ht he ↔ u ∈ S

end

section
open Finset MeasureTheory MEJF.Setup MEJF.Exchangeability MEJF.PredictionTable MEJF.TieFreeSharpness

/- Source S5.Thmtheorem3, S3.Thmtheorem1; production MEJF.TieFreeSharpness.exists_tieFree_attaining_model. -/
def s5_tie_free_attainment : Prop :=
  ∀ (m n F t ell : ℕ) (hm : 1 ≤ m)
    (hF : 1 ≤ F) (hFn : F ≤ n) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (eta : ℝ) (heta : 0 < eta) (heta' : eta < 1/4),
  ∃ (A : Learner UniversalCovariate n) (Z : Fin (m+1) → Block UniversalCovariate n),
      (∀ᵐ W ∂FiniteExchangeable.blockPermutationLaw Z, ActualTieFree A W t ell ht he) ∧
      (FiniteExchangeable.blockPermutationLaw Z).real
        {W | Setup.failure A W (Fin.last m) F t ell ht he} = RankFrontier.failureRate m F t ell

end

section
open MeasureTheory Finset MEJF.HeterogeneousSetup MEJF.Exchangeability MEJF.HeterogeneousFrontier MEJF.HeterogeneousEquivariance MEJF.HeterogeneousProbability

/- Source S6.Thmtheorem1; production MEJF.HeterogeneousProbability.gamma_eq. -/
def s6_heterogeneous_sup : Prop :=
  ∀ {m : ℕ} (n : Fin (m+1) → ℕ+) (alpha a : ℝ)
    (halpha : 0 ≤ alpha) (halpha1 : alpha < 1)
    (ht : ∀ i, 1 ≤ ⌊a*((n i).val+1)⌋₊ ∧ ⌊a*((n i).val+1)⌋₊ ≤ (n i).val)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m),
  gamma n alpha a ell he =
      (frontierOfMultiset m alpha a ell (univ.val.map (fun i => (n i).val)) : ℝ)/(m+1 : ℕ)

end

section
open MeasureTheory Finset MEJF.HeterogeneousSetup MEJF.Exchangeability MEJF.HeterogeneousFrontier MEJF.HeterogeneousEquivariance MEJF.HeterogeneousProbability

/- Source S6.Thmtheorem1; production MEJF.HeterogeneousProbability.exists_attaining_model. -/
def s6_heterogeneous_attainment : Prop :=
  ∀ {m : ℕ} (n : Fin (m+1) → ℕ+) (alpha a : ℝ)
    (halpha : 0 ≤ alpha) (halpha1 : alpha < 1)
    (ht : ∀ i, 1 ≤ ⌊a*((n i).val+1)⌋₊ ∧ ⌊a*((n i).val+1)⌋₊ ≤ (n i).val)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m),
  ∃ (A : Learner Setup.UniversalCovariate)
      (data : Fin (m+1) → Block Setup.UniversalCovariate),
      sizeMultiset data=univ.val.map (fun i => (n i).val) ∧
      (FiniteExchangeable.blockPermutationLaw data).real
        {Z | finiteFailure A Z alpha a ell he (Fin.last m)} =
        (frontierOfMultiset m alpha a ell (univ.val.map (fun i => (n i).val)) : ℝ)/(m+1 : ℕ)

end

section
open MeasureTheory Finset MEJF.HeterogeneousSetup MEJF.Exchangeability MEJF.HeterogeneousFrontier MEJF.HeterogeneousEquivariance MEJF.HeterogeneousProbability

/- Source S6.Thmtheorem1; production MEJF.HeterogeneousProbability.conditional_failure_le. -/
def s6_conditional_sizes : Prop :=
  ∀ {X : Type*} [MeasurableSpace X] [Nonempty X] {m : ℕ} (μ : Measure (Fin (m+1) → Block X)) [IsProbabilityMeasure μ]
    (hex : Exchangeable μ) (A : Learner X) (alpha a : ℝ)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (M : Multiset ℕ),
  conditionalFailure μ A alpha a ell he i M ≤
      (frontierOfMultiset m alpha a ell M : ℝ)/(m+1 : ℕ)

end

section
open MeasureTheory Finset MEJF.HeterogeneousSetup MEJF.Exchangeability MEJF.HeterogeneousFrontier MEJF.HeterogeneousEquivariance MEJF.HeterogeneousProbability

/- Source S6.Thmtheorem1; production MEJF.HeterogeneousProbability.failure_probability_le_expectation. -/
def s6_random_size_expectation : Prop :=
  ∀ {X : Type*} [MeasurableSpace X] [Nonempty X] {m : ℕ} (μ : Measure (Fin (m+1) → Block X)) [IsProbabilityMeasure μ]
    (hex : Exchangeable μ) (A : Learner X) (alpha a : ℝ)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)),
  μ.real {Z | finiteFailure A Z alpha a ell he i} ≤
      ∫ Z, (frontierOfMultiset m alpha a ell (sizeMultiset Z) : ℝ)/(m+1 : ℕ) ∂μ

end

section
open Finset MEJF.HeterogeneousGraph MEJF.HeterogeneousFrontier

/- Source S6.Thmtheorem1; production MEJF.HeterogeneousFrontier.supported_card_iff_sortedCell. -/
def s6_hall_sorted_cell : Prop :=
  ∀ {N : ℕ} (w : Fin N → ℕ) (s : ℕ),
  (∃ S : Finset (Fin N), S.card = s ∧ Supported w S) ↔
      SortedCell (OrderStatistics.stat w) s

end

section
open Finset MEJF.HeterogeneousGraph MEJF.HeterogeneousFrontier

/- Source S6.Thmtheorem1; production MEJF.HeterogeneousFrontier.maximumSupported_eq_sStar. -/
def s6_true_max_support : Prop :=
  ∀ {N : ℕ} (w : Fin N → ℕ),
  maximumSupported w = sStar w

end

section
open Finset MEJF.HeterogeneousFrontier MEJF.HeterogeneousAlgorithm

/- Source S6.Thmtheorem1; production MEJF.HeterogeneousAlgorithm.computeAfterSorting_correct. -/
def s6_quadratic_algorithm : Prop :=
  ∀ {N : ℕ} (w : Fin N → ℕ),
  (computeAfterSorting (MEJF.OrderStatistics.stat w)).value = sStar w

end

section
open Finset MEJF.HeterogeneousFrontier MEJF.HeterogeneousAlgorithm

/- Source S6.Thmtheorem1; production MEJF.HeterogeneousAlgorithm.computeAfterSorting_ops_le. -/
def s6_quadratic_cost : Prop :=
  ∀ {N : ℕ} (v : Fin N → ℕ) (hN : 1 ≤ N),
  (computeAfterSorting v).ops ≤ 23*N^2

end

section
open MEJF.HeterogeneousAlgorithm MEJF.HeterogeneousFrontier MEJF.HeterogeneousSortingInput

/- Source S6.Thmtheorem1; production MEJF.HeterogeneousSortingInput.computeWithSorter_correct. -/
def s6_published_sort_composition : Prop :=
  ∀ (published : PublishedMergeSortContract) {N : ℕ} (w : Fin N → ℕ),
  (computeWithSorter published w).value = sStar w

end

section
open MEJF.HeterogeneousAlgorithm MEJF.HeterogeneousFrontier MEJF.HeterogeneousSortingInput

/- Source S6.Thmtheorem1; production MEJF.HeterogeneousSortingInput.computeWithSorter_uniform_bound. -/
def s6_sort_and_scan_cost : Prop :=
  ∀ (published : PublishedMergeSortContract) {N : ℕ}
    (w : Fin N → ℕ) (hN : 1 ≤ N),
  (computeWithSorter published w).ops ≤
      published.uniformConstant*N*(Nat.clog 2 N+1)+23*N^2

end

section
open Finset MeasureTheory MEJF.HeterogeneousSetup MEJF.HeterogeneousLearner MEJF.HeterogeneousEquivariance MEJF.HeterogeneousTieFree

/- Source S6.Thmtheorem1; production MEJF.HeterogeneousTieFree.source_exists_tieFree_minimax_law. -/
def s6_heterogeneous_tie_free_law : Prop :=
  ∀ {m : ℕ} (n : Fin (m+1) → ℕ+) (alpha a : ℝ)
    (hα : 0 ≤ alpha) (hα1 : alpha < 1)
    (ht : ∀ u, 1 ≤ ⌊a*((n u).val+1)⌋₊ ∧ ⌊a*((n u).val+1)⌋₊ ≤ (n u).val)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m),
  ∃ (A : Learner Setup.UniversalCovariate)
      (data : Fin (m+1) → Block Setup.UniversalCovariate),
      (∀ u, (data u).1 = n u) ∧
      (FiniteExchangeable.blockPermutationLaw data).real
        {Z | sizeMultiset Z = univ.val.map (fun u => (n u).val)} = 1 ∧
      (FiniteExchangeable.blockPermutationLaw data).real
        {Z | HeterogeneousProbability.finiteFailure A Z alpha a ell he (Fin.last m)} =
        HeterogeneousProbability.gamma n alpha a ell he ∧
      (∀ᵐ Z ∂FiniteExchangeable.blockPermutationLaw data, ActualTieFree A Z a ell he)

end

section
open Finset MeasureTheory MEJF.Setup MEJF.Exchangeability MEJF.PredictionTable MEJF.Asymmetric

/- Source S6.Thmtheorem2; production MEJF.Asymmetric.gamma_eq. -/
def s6_asymmetric_sup : Prop :=
  ∀ (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m),
  gamma m n alpha t lm lp ht hm hp = RankFrontier.failureRate m (failureRank alpha n) t (max lm lp)

end

section
open Finset MeasureTheory MEJF.Setup MEJF.Exchangeability MEJF.PredictionTable MEJF.Asymmetric

/- Source S6.Thmtheorem2; production MEJF.Asymmetric.gamma_eq_symmetric. -/
def s6_asymmetric_symmetric_value : Prop :=
  ∀ (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m),
  gamma m n alpha t lm lp ht hm hp =
      Setup.finiteRankGamma m n alpha t (max lm lp) ht (maxRankProof hm hp)

end

section
open Finset MeasureTheory MEJF.Setup MEJF.Exchangeability MEJF.PredictionTable MEJF.Asymmetric

/- Source S6.Thmtheorem2; production MEJF.Asymmetric.symmetric_max_interval_subset. -/
def s6_symmetric_containment : Prop :=
  ∀ {X : Type*} [MeasurableSpace X] {m n : ℕ} (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i : Fin (m+1)) (j : Fin n) (t lm lp : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (hm : 1 ≤ lm ∧ lm ≤ m) (hp : 1 ≤ lp ∧ lp ≤ m),
  interval A Z i j t (max lm lp) (max lm lp) ht (maxRankProof hm hp) (maxRankProof hm hp) ⊆
      interval A Z i j t lm lp ht hm hp

end

section
open MeasureTheory Finset MEJF.Setup MEJF.Exchangeability MEJF.TournamentOptimization MEJF.RandomizedProbability

/- Source S6.Thmtheorem3; production MEJF.RandomizedProbability.finiteRankGammaPi_eq. -/
def s6_random_rank_sup : Prop :=
  ∀ (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (htF : t ≤ failureRank alpha n) (pi : RankLaw m),
  finiteRankGammaPi m n alpha t ht pi =
      maxObjective (failureRank alpha n) m t pi.mass / (m+1 : ℕ)

end

section
open MeasureTheory Finset MEJF.Setup MEJF.Exchangeability MEJF.TournamentOptimization MEJF.RandomizedProbability

/- Source S6.Thmtheorem3; production MEJF.RandomizedProbability.exists_attaining_model. -/
def s6_random_rank_attainment : Prop :=
  ∀ (m n F t : ℕ) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ F) (pi : RankLaw m),
  ∃ (A : Learner UniversalCovariate n) (Z : Fin (m+1) → Block UniversalCovariate n),
      weightedProbability pi.mass A (FiniteExchangeable.blockPermutationLaw Z) F t
        ⟨ht.1, ht.2.trans hFn⟩ (Fin.last m) = maxObjective F m t pi.mass / (m+1 : ℕ)

end

section
open Finset MeasureTheory MEJF.Setup MEJF.PredictionTable MEJF.TournamentOptimization MEJF.RandomizedProbability MEJF.RandomizedTieFree

/- Source S6.Thmtheorem3; production MEJF.RandomizedTieFree.exists_tieFree_attaining_law. -/
def s6_random_rank_tie_free : Prop :=
  ∀ (m n F t : ℕ) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ F) (pi : RankLaw m) (eta : ℝ) (heta : 0 < eta) (heta' : eta < 1/4),
  ∃ (A : Learner UniversalCovariate n) (Z : Fin (m+1) → Block UniversalCovariate n),
      (∀ᵐ W ∂FiniteExchangeable.blockPermutationLaw Z, ∀ l : Fin m,
        TieFreeSharpness.ActualTieFree A W t (l.val+1) ⟨ht.1,ht.2.trans hFn⟩ (rankValid l)) ∧
      weightedProbability pi.mass A (FiniteExchangeable.blockPermutationLaw Z) F t
        ⟨ht.1,ht.2.trans hFn⟩ (Fin.last m) = maxObjective F m t pi.mass/(m+1 : ℕ)

end

section
open Finset MEJF.TournamentOptimization MEJF.RankDP

/- Source S6.Thmtheorem3; production MEJF.RankDP.dp_computes_gamma. -/
def s6_landau_dp : Prop :=
  ∀ (m n F t : ℕ) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ F) (pi : RandomizedProbability.RankLaw m)
    (hLandau : LandauInput (m+1)),
  eval (m+1) (RandomizedRanks.payoff F m t pi.mass) (m+1) m ((m+1).choose 2) =
      ((((m+1 : ℕ) : ℝ) * RandomizedProbability.gammaF m n F t ⟨ht.1,ht.2.trans hFn⟩ pi : ℝ) : WithBot ℝ)

end

section
open Finset MEJF.TournamentOptimization MEJF.RankDP

/- Source S6.Thmtheorem3; production MEJF.RankDP.complete_program_cost. -/
def s6_dp_quartic_cost : Prop :=
  ∀ (F m t N : ℕ) (pi : Fin m → ℝ) (hmN : m ≤ N) (hN : 1 ≤ N),
  (∑ a : Grid N,(scheduledCell N (RandomizedRanks.payoff F m t pi) a).2) +
      preprocessingCost F m t N pi ≤ 64*N^4

end

section
open MeasureTheory Finset MEJF.Setup MEJF.Exchangeability MEJF.TournamentOptimization MEJF.RandomizedProbability

/- Source S6.Thmtheorem4; production MEJF.RandomizedProbability.nonconvexification_actual. -/
def s6_nonconvexification : Prop :=
  finiteRankGammaPi 6 1 (1/2) 1 (by norm_num) rank23Law = 3/7 ∧
    Setup.finiteRankGamma 6 1 (1/2) 1 2 (by norm_num) (by norm_num) = 3/7 ∧
    Setup.finiteRankGamma 6 1 (1/2) 1 3 (by norm_num) (by norm_num) = 5/7 ∧
    (3/7 : ℝ) < (1/2)*(3/7+5/7) ∧ (1/2 : ℝ)*(3/7+5/7) = 4/7

end

section
open MeasureTheory MEJF.Setup MEJF.Stability MEJF.Exchangeability Finset MEJF.StabilityProbability

/- Source S6.Thmtheorem5; production MEJF.StabilityProbability.expanded_failure_probability_le. -/
def s6_expanded_probability : Prop :=
  ∀ {X : Type*} [MeasurableSpace X] {m n : ℕ} (A : Learner X n)
    (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ]
    (hμ : Exchangeable μ) (ε : ℝ) (hε : 0 ≤ ε) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) (htF : t ≤ F)
    (γ : ℝ) (hprob : 1-γ ≤ μ.real {Z | onSampleDeletionStable A Z ε})
    (i : Fin (m+1)),
  μ.real {Z | learnerExpandedFailure A Z ε i F t ell ht he} ≤
      (ell : ℝ)/(m+1 : ℕ) +
        ((RankFrontier.failureCount m F t ell : ℕ) - (ell : ℝ))/(m+1 : ℕ)*γ

end

section
open MeasureTheory MEJF.Setup MEJF.Stability MEJF.StabilitySharpness MEJF.Exchangeability Finset MEJF.StabilityExtended

/- Source S6.Thmtheorem5; production MEJF.StabilityExtended.gamma_eq. -/
def s6_expanded_full_sup : Prop :=
  ∀ (m n F t ell : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hF : 1 ≤ F) (hFn : F ≤ n) (htn : t ≤ n) (helm : ell ≤ m),
  gamma m n F t ell ε =
      if t = 0 ∨ ell = 0 then 0 else if F < t then 1 else (ell : ℝ)/(m+1 : ℕ)

end

section
open MEJF.StabilityExtended Finset MEJF.StabilityFrontier

/- Source S6.Thmtheorem5; production MEJF.StabilityFrontier.maximal_valid_pair_iff. -/
def s6_stable_maximal_pair : Prop :=
  ∀ (m n F t ell : ℕ) (ε δ : ℝ) (hε : 0 ≤ ε)
    (hF : 1 ≤ F) (hFn : F ≤ n) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hD : 1 ≤ ⌊δ*(m+1 : ℕ)⌋₊),
  (Valid m n F ε δ (t,ell) ∧
      ∀ u v, Valid m n F ε δ (u,v) → t ≤ u → ell ≤ v → u ≤ t ∧ v ≤ ell) ↔
      t = F ∧ ell = ⌊δ*(m+1 : ℕ)⌋₊

end

section
open MEJF.Setup MEJF.StabilityExtended Filter Topology MEJF.StabilityAsymptotic

/- Source S6.Thmtheorem5; production MEJF.StabilityAsymptotic.actual_limiting_rectangle. -/
def s6_stable_asymptotic_rectangle : Prop :=
  ∀ {m n : ℕ → ℕ} {alpha a b ε δ : ℝ}
    (hmin : Tendsto (fun k => min (m k) (n k)) atTop atTop)
    (hα : 0 < alpha) (hα1 : alpha < 1) (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hb1 : b < 1) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ1 : δ < 1),
  ∃ L : ℝ, Tendsto (fun k => Gamma (m k) (n k) alpha a b ε) atTop (𝓝 L) ∧
      (L ≤ δ ↔ a ≤ alpha ∧ b ≤ δ)

end

section
open Finset MeasureTheory MEJF.Setup MEJF.PredictionTable MEJF.Stability MEJF.Exchangeability MEJF.Scaling

/- Source S6.Thmtheorem6; production MEJF.Scaling.stableUnexpandedGamma_eq. -/
def s6_unexpanded_stable_sup : Prop :=
  ∀ (m n F t ell : ℕ) (eps : ℝ) (heps : 0 < eps)
    (hm : 1 ≤ m) (hF : 1 ≤ F) (hFn : F ≤ n) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m),
  stableUnexpandedGamma m n F t ell eps ht he = RankFrontier.failureRate m F t ell

end

section
open MeasureTheory MEJF.Setup MEJF.Exchangeability Finset MEJF.SwapRobustness

/- Source S6.Thmtheorem7; production MEJF.SwapRobustness.source_failure_probability_le. -/
def s6_swap_upper : Prop :=
  ∀ {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (P : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure P]
    (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)),
  P.real {Z | Setup.failure A Z i F t ell ht he} ≤
      min 1 ((RankFrontier.failureCount m F t ell : ℝ)/(m+1 : ℕ)+swapDefect P i)

end

section
open MeasureTheory MEJF.Setup MEJF.Exchangeability Finset MEJF.SwapRobustness

/- Source S6.Thmtheorem7; production MEJF.SwapRobustness.source_swap_sharpness. -/
def s6_swap_attainment : Prop :=
  ∀ (m n F t ell : ℕ) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (hsmall : RankFrontier.failureCount m F t ell < m+1)
    (η : ℝ) (hη : 0 ≤ η)
    (hηmax : η ≤ 1-(RankFrontier.failureCount m F t ell : ℝ)/(m+1 : ℕ)),
  ∃ (A : Learner UniversalCovariate n)
      (P : Measure (Fin (m+1) → Block UniversalCovariate n)),
      IsProbabilityMeasure P ∧ swapDefect P (Fin.last m) = η ∧
      P.real {Z | Setup.failure A Z (Fin.last m) F t ell ht he} =
        (RankFrontier.failureCount m F t ell : ℝ)/(m+1 : ℕ)+η

end

section
open MEJF.Setup MEJF.RankFrontier MEJF.MainResults

/- Source S7.Thmtheorem1; production MEJF.MainResults.ordinary_factor_two_failure. -/
def s7_factor_two_failure : Prop :=
  finiteRankGamma 19 200 (1/5) 40 2 (by norm_num) (by norm_num) = 1

end

section
open MeasureTheory Filter MEJF.Efficiency MEJF.EfficiencyLaw MEJF.EfficiencyModel MEJF.EfficiencyCompletion

/- Source S2.Thmtheorem1, S7.Thmtheorem2; production MEJF.EfficiencyCompletion.proposition_7_2. -/
def s7_full_efficiency : Prop :=
  ∀ (K : ℝ) (hK : 0 < K),
  (Setup.finiteRankGamma 19 19 (1/5) 2 2 (by norm_num) (by norm_num) = 3/20 ∧
      Setup.finiteRankGamma 19 19 (1/5) 2 2 (by norm_num) (by norm_num) < 1/5) ∧
    IsProbabilityMeasure zeroBlockLaw ∧ Exchangeability.Exchangeable zeroBlockLaw ∧
    (∀ᵐ Z ∂zeroBlockLaw, ∀ i, (endpointAverage K Z i = 2 ∧ minmaxAverage K Z i = (2*K+38)/19 ∧ advantage K Z i = 2*K/19 ∧ endpointAverage K Z i/minmaxAverage K Z i = 38/(2*K+38))) ∧
    Tendsto (fun κ : ℝ => 38/(2*κ+38)) atTop (nhds 0) ∧
    (∀ ξ : ℝ, 0 < ξ → ξ < K/38 →
      IsProbabilityMeasure (blockLaw ξ) ∧ NoAtoms (blockLaw ξ) ∧
      Exchangeability.Exchangeable (blockLaw ξ) ∧ 0 < (2*K-76*ξ)/19 ∧
      (∀ᵐ Z ∂blockLaw ξ, ∀ i, ((2*K-76*ξ)/19 ≤ advantage K Z i ∧ endpointAverage K Z i ≤ 2+2*ξ ∧ (2*K+38-38*ξ)/19 ≤ minmaxAverage K Z i ∧ endpointAverage K Z i/minmaxAverage K Z i ≤ 38*(1+ξ)/(2*K+38-38*ξ))) ∧
      Tendsto (fun κ : ℝ => 38*(1+ξ)/(2*κ+38-38*ξ)) atTop (nhds 0))

end

section
open MeasureTheory Filter MEJF.Efficiency MEJF.EfficiencyLaw MEJF.EfficiencyModel MEJF.EfficiencyCompletion

/- Source S7.Thmtheorem2; production MEJF.EfficiencyCompletion.noiseless_every_permutation. -/
def s7_every_noiseless_realization : Prop :=
  ∀ {K : ℝ} (hK : 0 < K) (p : Equiv.Perm Type20) (i : Type20),
  (endpointAverage K (reveal (p,fun _ => 0)) i = 2 ∧ minmaxAverage K (reveal (p,fun _ => 0)) i = (2*K+38)/19 ∧ advantage K (reveal (p,fun _ => 0)) i = 2*K/19 ∧ endpointAverage K (reveal (p,fun _ => 0)) i/minmaxAverage K (reveal (p,fun _ => 0)) i = 38/(2*K+38))

end

section
open MeasureTheory Filter MEJF.Efficiency MEJF.EfficiencyLaw MEJF.EfficiencyModel MEJF.EfficiencyCompletion

/- Source S7.Thmtheorem2; production MEJF.EfficiencyCompletion.noisy_every_supported_sample. -/
def s7_every_supported_noise : Prop :=
  ∀ {K ξ : ℝ} (hK : 0 < K) (hξ : 0 ≤ ξ)
    (hsmall : ξ < K/38) (s : Sample) (hs : ∀ a, |s.2 a| ≤ ξ) (i : Type20),
  ((2*K-76*ξ)/19 ≤ advantage K (reveal s) i ∧ endpointAverage K (reveal s) i ≤ 2+2*ξ ∧ (2*K+38-38*ξ)/19 ≤ minmaxAverage K (reveal s) i ∧ endpointAverage K (reveal s) i/minmaxAverage K (reveal s) i ≤ 38*(1+ξ)/(2*K+38-38*ξ))

end

section
open Finset Set MEJF.OrderStatistics MEJF.Efficiency

/- Source S7.Thmtheorem3; production MEJF.Efficiency.strict_containment. -/
def s7_strict_containment : Prop :=
  ∀ {m : ℕ} (p Sa Sα : Fin (m+1) → ℝ)
    (k d : Fin (m+1))
    (_hne : (endpointInterval p Sa k).Nonempty)
    (hlo : stat Sa (Fin.last m) - stat Sα d < stat p k - stat p 0)
    (hhi : stat Sa (Fin.last m) - stat Sα d <
      stat p (Fin.last m) - stat p k.rev),
  endpointInterval p Sa k ⊆ interior (minmaxInterval p Sα d)

end

section
open MEJF.Setup MEJF.AsymmetricFrontier

/- Source S6.Thmtheorem2; production MEJF.AsymmetricFrontier.symmetric_interval_subset. -/
def s6_all_covariates_containment : Prop :=
  ∀ {X : Type*} [MeasurableSpace X] {m n : ℕ} (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i : Fin (m+1)) (x : X) (t lm lp : ℕ) (ht : 1≤t ∧ t≤n)
    (hm : 1≤lm ∧ lm≤m) (hp : 1≤lp ∧ lp≤m),
  intervalAt A Z i x t (max lm lp) (max lm lp) ht
      (Asymmetric.maxRankProof hm hp) (Asymmetric.maxRankProof hm hp) ⊆
      intervalAt A Z i x t lm lp ht hm hp

end

section
open MEJF.Setup MEJF.AsymmetricFrontier

/- Source S6.Thmtheorem2; production MEJF.AsymmetricFrontier.outer_pareto_symmetric. -/
def s6_asymmetric_pareto_symmetric : Prop :=
  ∀ (m n : ℕ) (alpha delta : ℝ)
    (ha : 0≤alpha) (ha1 : alpha<1) (t lm lp : ℕ) (ht : 1≤t ∧ t≤n)
    (h : OuterPareto m n alpha delta t lm lp ht),
  lm=lp

end

section
open MEJF.Setup MEJF.AsymmetricFrontier MEJF.RankCells

/- Source S3.Thmtheorem3; production MEJF.RankCells.shifted_rank_cell. -/
def s3_floor_cells : Prop :=
  ∀ (v k : ℕ) (a : ℝ) (ha : 0 ≤ a),
  ⌊a*((v:ℝ)+1)⌋₊=k ↔ (k:ℝ)/(v+1:ℝ) ≤ a ∧ a < ((k:ℝ)+1)/(v+1:ℝ)

end

section
open MEJF.Setup MEJF.AsymmetricFrontier MEJF.RankCells

/- Source S3.Thmtheorem3; production MEJF.RankCells.intervalAt_antitone. -/
def s3_pathwise_monotonicity : Prop :=
  ∀ {X : Type*} [MeasurableSpace X] {m n : ℕ} (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i : Fin (m+1)) (x : X) (t r ell q : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (hr : 1 ≤ r ∧ r ≤ n)
    (he : 1 ≤ ell ∧ ell ≤ m) (hq : 1 ≤ q ∧ q ≤ m) (htr : t ≤ r) (heq : ell ≤ q),
  intervalAt A Z i x r q q hr hq hq ⊆ intervalAt A Z i x t ell ell ht he he

end

section
open MEJF.Setup MEJF.AsymmetricFrontier MEJF.RankCells

/- Source S3.Thmtheorem3; production MEJF.RankCells.interval_constant_on_cell. -/
def s3_pathwise_cell_constancy : Prop :=
  ∀ {X : Type*} [MeasurableSpace X] {m n : ℕ} (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (i : Fin (m+1)) (x : X) (a a' b b' : ℝ)
    (hta : 1 ≤ innerRank a n ∧ innerRank a n ≤ n)
    (hta' : 1 ≤ innerRank a' n ∧ innerRank a' n ≤ n)
    (heb : 1 ≤ outerRank b m ∧ outerRank b m ≤ m)
    (heb' : 1 ≤ outerRank b' m ∧ outerRank b' m ≤ m)
    (ha : innerRank a n=innerRank a' n) (hb : outerRank b m=outerRank b' m),
  intervalAt A Z i x (innerRank a n) (outerRank b m) (outerRank b m) hta heb heb =
      intervalAt A Z i x (innerRank a' n) (outerRank b' m) (outerRank b' m) hta' heb' heb'

end

section
open MEJF.Setup MEJF.AsymmetricFrontier MEJF.RankCells

/- Source S7.Thmtheorem1; production MEJF.RankCells.ordinary_factor_two_at_levels. -/
def s7_factor_two_continuous_levels : Prop :=
  ActualAsymptotic.Gamma 19 200 (1/5) (1/5) (1/10)=1

end

section
open MeasureTheory Finset MEJF.Setup MEJF.Exchangeability MEJF.CoherentSeed

/- Source S2.Thmtheorem1; production MEJF.CoherentSeed.randomizedGamma_eq_finiteRankGamma. -/
def s2_coherent_seed_minimax : Prop :=
  ∀ {U : Type*} [MeasurableSpace U] (ν : Measure U) [IsProbabilityMeasure ν]
    (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m),
  randomizedGamma ν m n alpha t ell ht he = finiteRankGamma m n alpha t ell ht he

end

section
open MeasureTheory Finset MEJF.Setup MEJF.Exchangeability MEJF.CoherentSeed

/- Source S2.Thmtheorem1; production MEJF.CoherentSeed.measurableSet_failure. -/
def s2_coherent_seed_joint_measurable : Prop :=
  ∀ {U X : Type*} [MeasurableSpace U] [MeasurableSpace X] {m n : ℕ} (A : Family U X n) (i : Fin (m+1))
    (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m),
  MeasurableSet {q : U × (Fin (m+1) → Block X n) | failure A q i F t ell ht he}

end

section
open MeasureTheory Finset MEJF.Setup MEJF.Exchangeability MEJF.CoherentSeed

/- Source S2.Thmtheorem1; production MEJF.CoherentSeed.ae_admissible_failure_probability_le. -/
def s2_ae_admissible_seed_bound : Prop :=
  ∀ {U X : Type*} [MeasurableSpace U] [MeasurableSpace X] {m n : ℕ} (ν : Measure U) [IsProbabilityMeasure ν]
    (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ] (hμ : Exchangeable μ)
    (H : U × (Fin (m+1) → Block X n) → Fin (m+1) → Prop)
    (hH : ∀ j, MeasurableSet {q | H q j}) (i : Fin (m+1)) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (hgood : ∀ᵐ u ∂ν, ∃ A : Learner X n, ∀ Z j,
      H (u,Z) j ↔ Setup.failure A Z j F t ell ht he),
  (ν.prod μ).real {q | H q i} ≤ RankFrontier.failureRate m F t ell

end

section
open MeasureTheory Finset MEJF.Setup MEJF.Exchangeability MEJF.CoherentSeed

/- Source S2.Thmtheorem1; production MEJF.CoherentSeed.aeAdmissibleGamma_eq_finiteRankGamma. -/
def s2_ae_admissible_seed_minimax : Prop :=
  ∀ {U : Type*} [MeasurableSpace U] (ν : Measure U) [IsProbabilityMeasure ν]
    (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m),
  aeAdmissibleGamma ν m n alpha t ell ht he = finiteRankGamma m n alpha t ell ht he

end

end Paper33.Contracts
