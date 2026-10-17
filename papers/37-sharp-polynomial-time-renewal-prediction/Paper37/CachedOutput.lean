import Paper37.IntegerOutput
import Paper37.CachedDP

namespace Paper37.CachedOutput
open Finset Paper37.DP Paper37.ContinuationDP Paper37.CachedDP
open Paper37.IntegerOutput Paper37.Envelope Paper37.Prediction

/-- Safe source-count access, with zero outside the allocated alphabet. -/
def observedAt {H : ℕ} (c : Cache H) (d : ℕ) : ℕ :=
  if h : d<H+1 then c.observed[d] else 0

def initialNumerator {H : ℕ} (c : Cache H) : ℕ :=
  ∏ d ∈ gapSet H, powerAt c (observedAt c d)

def denominator {H : ℕ} (c : Cache H) : ℕ :=
  ∏ k ∈ Icc 1 H, powerAt c k

lemma observedAt_source (H : ℕ) (z : List Bool) (d : ℕ) (hd : d≤H) :
    observedAt (makeObservedCache H z) d = observedCounts z d := by
  simp [observedAt,makeObservedCache_eq,makeCache,show d<H+1 by omega]

theorem initialNumerator_source (H : ℕ) (z : List Bool) (hz : z.length≤H) :
    initialNumerator (makeObservedCache H z) = weight (observedCounts z) (gapSet H) 0 := by
  unfold initialNumerator weight
  apply prod_congr rfl
  intro d hd
  have hdH := (mem_Icc.mp hd).2
  rw [observedAt_source H z d hdH,makeObservedCache_eq,
    powerAt_correct H (observedCounts z) _ (by
      have hh := observedCounts_le_horizon H z hz d hdH
      omega)]
  simp

theorem denominator_source (H : ℕ) (z : List Bool) :
    denominator (makeObservedCache H z) = commonDenominator H := by
  unfold denominator commonDenominator
  apply prod_congr rfl
  intro k hk
  rw [makeObservedCache_eq,powerAt_correct H (observedCounts z) k (by
    have hh := (mem_Icc.mp hk).2
    omega)]

/-- A genuinely integer-only output query. The observed histogram, Pascal
table, powers, and final rolling table are shared by every final summand. -/
def evaluatePair (H : ℕ) (z : List Bool) (R : ℕ) : ℕ × ℕ :=
  let c := makeObservedCache H z
  let D := denominator c
  let A := parseAge 0 z
  let r := (parseGaps 0 z).length
  let table := cachedRun H c A H
  (initialNumerator c * (D/powerAt c r) +
    ∑ k ∈ Icc 1 (A+R), ∑ u ∈ Icc k (A+R),
      scaledKernel.eval ![(layerAt table k u).2,k,D,powerAt c (r+k)],D)

theorem evaluatePair_eq (H : ℕ) (z : List Bool) (R : ℕ) (hz : z.length+R≤H) :
    evaluatePair H z R = (numerator H z R,commonDenominator H) := by
  unfold evaluatePair
  dsimp only
  rw [denominator_source,initialNumerator_source H z (by omega),
    makeObservedCache_eq,cachedRun_correct H (observedCounts z) (parseAge 0 z) H le_rfl
      (observedCounts_le_horizon H z (by omega))]
  apply Prod.ext
  · unfold numerator
    dsimp only
    have hr : (parseGaps 0 z).length≤2*H := by have hh := count_add_age_le z; omega
    rw [powerAt_correct H (observedCounts z) _ hr]
    congr 1
    apply sum_congr rfl
    intro k hk
    apply sum_congr rfl
    intro u hu
    have hrk : (parseGaps 0 z).length+k≤2*H := by
      have hh := count_add_age_le z
      have hkt := (mem_Icc.mp hk).2
      omega
    rw [powerAt_correct H (observedCounts z) _ hrk,scaledKernel_source]
  · rfl

theorem evaluatePair_correct (H : ℕ) (z : List Bool) (R : ℕ) (hz : z.length+R≤H) :
    ((evaluatePair H z R).1:ℚ)/(evaluatePair H z R).2 =
      continuationMass (z.length+R) z := by
  rw [evaluatePair_eq H z R hz]
  exact numerator_exact H z R hz

theorem evaluatePair_binarySize (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : 0<H) (hz : z.length+R≤H) :
    pairSize (evaluatePair H z R) ≤
      2*(H+1).size+(4*H+1)*(2*H).size+(H*(H+1)/2)*H.size+5 := by
  rw [evaluatePair_eq H z R hz]
  unfold pairSize
  apply max_le (numerator_binarySize H z R hH hz)
  change (commonDenominator H).size≤_
  have hh := commonDenominator_binarySize H
  omega

end Paper37.CachedOutput
