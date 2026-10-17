import Paper37.CachedRefinedDP
import Paper37.SequentialRegret

/-! Actual cache-using query and predictor interfaces. Each visible adaptive
query shares one refined continuation table across all mixture components and
one empty-prefix table across all component normalizers. -/
namespace Paper37.CachedQueries
open Finset Paper37.DP Paper37.Envelope Paper37.Prediction Paper37.Adaptive
open Paper37.ContinuationDP Paper37.CachedDP Paper37.RefinedContinuation
open Paper37.CachedRefinedDP

lemma cachedContinuation_eq (H : ℕ) (z : List Bool) (R : ℕ) (hH : z.length+R≤H) :
    cachedEvaluateContinuation H z R = evaluateContinuation H z R :=
  (cachedEvaluateContinuation_correct H z R hH).trans (evaluateContinuation_correct H z R hH).symm

def cachedNormalizer (H : ℕ) : ℚ := cachedEvaluateContinuation H [] H

@[simp] theorem cachedNormalizer_correct (H : ℕ) : cachedNormalizer H = ordinaryNormalizer H := by
  unfold cachedNormalizer
  simpa only [List.length_nil, zero_add, Paper37.EnvelopeBridge.continuationMass_nil] using
    cachedEvaluateContinuation_correct H [] H (by simp)

def cachedBlockAssignment (x : List Bool) : ℚ :=
  match firstSuffix x with
  | none => 1 / (x.length+1 : ℚ)
  | some z => wordEnvelope z / ((x.length+1 : ℚ) * cachedNormalizer z.length)

theorem cachedBlockAssignment_correct (x : List Bool) : cachedBlockAssignment x = blockAssignment x := by
  unfold cachedBlockAssignment blockAssignment
  cases hs : firstSuffix x <;> simp [ordinaryAssignment, cachedNormalizer_correct, div_div, mul_comm]

def cachedVisibleConditional (L : ℕ) (z : List Bool) : ℚ :=
  let w₁ := cachedEvaluateContinuation L (z ++ [true]) (L - (z.length+1))
  let w₀ := cachedEvaluateContinuation L (z ++ [false]) (L - (z.length+1))
  w₁ / (w₀+w₁)

def cachedConditional (N : ℕ) (y : List Bool) : ℚ :=
  match firstSuffix y with
  | none => 1 / ((N-y.length+1 : ℕ) : ℚ)
  | some z => cachedVisibleConditional (N-y.length+z.length) z

theorem cachedConditional_eq (N : ℕ) (y : List Bool) (hy : y.length<N) :
    cachedConditional N y = evaluateConditional N y := by
  unfold cachedConditional evaluateConditional
  cases hs : firstSuffix y with
  | none => rfl
  | some z =>
    obtain ⟨j,hj⟩ := Paper37.EnvelopeBridge.firstSuffix_some_decomposition y z hs
    have hlen : y.length=j+1+z.length := by simp [hj]; omega
    have hz : z.length<N-y.length+z.length := by omega
    have hchild (b : Bool) : (z++[b]).length +
        (N-y.length+z.length-(z.length+1)) ≤ N-y.length+z.length := by simp; omega
    dsimp only
    unfold cachedVisibleConditional evaluateVisibleConditional
    rw [cachedContinuation_eq _ _ _ (hchild true), cachedContinuation_eq _ _ _ (hchild false)]

theorem cachedConditional_correct (N : ℕ) (y : List Bool) (hy : y.length<N) :
    cachedConditional N y = blockConditional N y :=
  (cachedConditional_eq N y hy).trans (evaluateConditional_correct N y hy)

def cachedPredictor (n : ℕ) (x : List Bool) : ℚ :=
  (∑ t ∈ Icc 1 n, cachedConditional (n+1) (x.drop (n-t))) / n

theorem cachedPredictor_correct (n : ℕ) (x : List Bool) (hx : x.length=n) :
    cachedPredictor n x = predict n x := by
  unfold cachedPredictor predict
  congr 1
  apply sum_congr rfl
  intro t ht
  apply cachedConditional_correct
  have htn : t≤n := (mem_Icc.mp ht).2
  simp only [List.length_drop, hx]
  omega

/-- Two shared refined-table results supply all components of one mixed
adaptive prefix. Ratios are formed componentwise before the probability mix. -/
def cachedAdaptivePrefix (N : ℕ) (y : List Bool) : ℚ :=
  match firstSuffix y with
  | none => ((N-y.length+1 : ℕ) : ℚ) / (N+1 : ℚ)
  | some z =>
    let L := N-y.length+z.length
    let masses := cachedEvaluateRestrictedAll L z (L-z.length)
    let normalizers := cachedEvaluateRestrictedAll L [] L
    ∑ t ∈ Icc 1 N, omegaWeight N t *
      (lookupRestriction masses t / ((N+1 : ℚ)*lookupRestriction normalizers t))

theorem cachedAdaptivePrefix_eq (N : ℕ) (y : List Bool) :
    cachedAdaptivePrefix N y = evaluateAdaptivePrefix N y := by
  unfold cachedAdaptivePrefix evaluateAdaptivePrefix
  cases hs : firstSuffix y with
  | none => rfl
  | some z =>
    dsimp only
    rw [cachedEvaluateRestrictedAll_eq _ z _ (by omega),
      cachedEvaluateRestrictedAll_eq _ [] _ (by simp)]

theorem cachedAdaptivePrefix_correct (N : ℕ) (y : List Bool) (hN : 1≤N) (hy : y.length≤N) :
    cachedAdaptivePrefix N y = adaptivePrefix N y :=
  (cachedAdaptivePrefix_eq N y).trans (evaluateAdaptivePrefix_correct N y hN hy)

def cachedAdaptiveConditional (N : ℕ) (y : List Bool) : ℚ :=
  cachedAdaptivePrefix N (y++[true]) / cachedAdaptivePrefix N y

theorem cachedAdaptiveConditional_correct (N : ℕ) (y : List Bool) (hy : y.length<N) :
    cachedAdaptiveConditional N y = adaptiveConditional N y := by
  unfold cachedAdaptiveConditional adaptiveConditional
  rw [cachedAdaptivePrefix_correct N _ (by omega) (by simp; omega),
    cachedAdaptivePrefix_correct N y (by omega) hy.le]

def cachedAdaptivePredictor (n : ℕ) (x : List Bool) : ℚ :=
  (∑ t ∈ Icc 1 n, cachedAdaptiveConditional (n+1) (x.drop (n-t))) / n

theorem cachedAdaptivePredictor_correct (n : ℕ) (x : List Bool) (hx : x.length=n) :
    cachedAdaptivePredictor n x = adaptivePredict n x := by
  unfold cachedAdaptivePredictor adaptivePredict
  congr 1
  apply sum_congr rfl
  intro t ht
  apply cachedAdaptiveConditional_correct
  have htn : t≤n := (mem_Icc.mp ht).2
  simp only [List.length_drop, hx]
  omega

def cachedAdaptiveMass (x : List Bool) : ℚ :=
  if x=[] then 1 else cachedAdaptivePrefix x.length x

theorem cachedAdaptiveMass_correct (x : List Bool) : cachedAdaptiveMass x = adaptiveMass x := by
  rw [← evaluateAdaptiveMass_correct]
  simp only [cachedAdaptiveMass, evaluateAdaptiveMass, cachedAdaptivePrefix_eq]

/-- C.13 for the actual coefficient-cache implementation, on a supplied
forward path rather than an enumeration of all possible prefixes. -/
theorem cached_path_log_regret (μ : Paper37.Renewal.Law) (x : List Bool)
    (hp : 0 < Paper37.Renewal.blockMass μ x) :
    (∑ t ∈ range x.length,
      Real.log (Paper37.RenewalCompression.next μ (x.take t) ((x[t]?).getD false) /
        (if (x[t]?).getD false then (cachedConditional x.length (x.take t) : ℝ)
          else 1-(cachedConditional x.length (x.take t) : ℝ)))) ≤
      Paper37.AnalyticBounds.redundancyBound x.length := by
  calc
    _ = ∑ t ∈ range x.length,
        Real.log (Paper37.RenewalCompression.next μ (x.take t) ((x[t]?).getD false) /
          (if (x[t]?).getD false then (evaluateConditional x.length (x.take t) : ℝ)
            else 1-(evaluateConditional x.length (x.take t) : ℝ))) := by
      apply sum_congr rfl
      intro t ht
      have ht' : t<x.length := mem_range.mp ht
      rw [cachedConditional_eq _ _ (by simp only [List.length_take, Nat.min_eq_left ht'.le]; exact ht')]
    _ ≤ _ := Paper37.SequentialRegret.computed_path_log_regret μ x hp

end Paper37.CachedQueries

namespace Paper37.CachedQueries
open Finset Paper37.DP Paper37.Envelope Paper37.Prediction Paper37.Adaptive
open Paper37.ContinuationDP Paper37.CachedDP Paper37.AdaptiveDP Paper37.CachedRefinedDP

/-- The sum of actual observed histogram counts is exactly the number of
completed observed gaps. -/
lemma observed_count_sum (H : ℕ) (z : List Bool) (hz : z.length≤H) :
    (gapSet H).sum (observedCounts z) = (parseGaps 0 z).length := by
  simpa only [observedCounts, List.length_map] using
    sum_count_of_support ((parseGaps 0 z).map Nat.succ) (gapSet H) (observed_support z H hz)

lemma observed_prefix_sum_le (H d : ℕ) (z : List Bool) (hd : d≤H) (hz : z.length≤H) :
    (gapSet d).sum (observedCounts z) ≤ H := by
  calc
    _ ≤ (gapSet H).sum (observedCounts z) := sum_le_sum_of_subset_of_nonneg (gapSet_mono hd)
      (fun i hi hn => Nat.zero_le _)
    _ = (parseGaps 0 z).length := observed_count_sum H z hz
    _ ≤ H := (parseGaps_length_le 0 z).trans hz

/-- Every completed gap consumes at least one position, including the current
censored age left over from the prefix. -/
lemma observed_count_add_age (z : List Bool) :
    (parseGaps 0 z).length + parseAge 0 z ≤ z.length := by
  have hc := gap_list_length_le_weight (parseGaps 0 z)
  have hw := parse_weight_age 0 z
  omega

/-- The empirical denominator in every final query term has exponent at most
the supplied source horizon, as required by the common denominator C.12. -/
lemma query_totalCount_le (H : ℕ) (z : List Bool) (R k : ℕ)
    (hH : z.length+R≤H) (hk : k≤parseAge 0 z+R) :
    (parseGaps 0 z).length+k≤H := by
  have hh := observed_count_add_age z
  omega

/-- Numeric bounds for every actual cached refinement entry; the observed
histogram budget is discharged from the source prefix, not postulated. -/
theorem cachedRefined_binarySize (H : ℕ) (z : List Bool) (A d : ℕ)
    (k u j : Fin (H+1)) (hH : 0<H) (hd : d≤H) (hz : z.length≤H) :
    (refinedAt (cachedRefinedRun H (makeObservedCache H z) A d) k u j).1.size ≤
        (2*(2*H))*(2*H).size+1 ∧
    (refinedAt (cachedRefinedRun H (makeObservedCache H z) A d) k u j).2.size ≤
        (2*(2*H)+1)*(2*H).size+1 := by
  rw [makeObservedCache_eq, cachedRefinedRun_correct H (observedCounts z) A d hd
    (observedCounts_le_horizon H z hz), refinedRun_correct]
  have hcard : (gapSet d).card≤2*H := by simp [gapSet]; omega
  have hsize : (gapSet d).sum (observedCounts z)+k.val≤2*H := by
    have hh := observed_prefix_sum_le H d z hd hz
    have hk := k.isLt
    omega
  constructor
  · change (refinedG (observedCounts z) (gapSet d) k.val u.val j.val).size ≤ _
    exact (Nat.size_le_size (refinedG_le_G _ _ _ _ _)).trans
      (G_binarySize _ _ _ _ _ (by omega) hcard hsize)
  · change (refinedS (observedCounts z) (gapSet d) A k.val u.val j.val).size ≤ _
    exact (Nat.size_le_size (refinedS_le_S _ _ _ _ _ _)).trans
      (S_binarySize _ _ _ _ _ _ (by omega) hcard hsize)

end Paper37.CachedQueries
