import Paper37.AdaptiveContinuation

/-! Equation E.7 on the exact source continuation, and one shared materialized
refinement table for every requested occupied-type restriction. -/
namespace Paper37.RefinedContinuation
open Finset Paper37.DP Paper37.Envelope Paper37.Prediction Paper37.Adaptive
open Paper37.AdaptiveDP Paper37.ContinuationDP Paper37.AdaptiveContinuation

/-- Prefix sum of the occupied-type coordinate counts exactly the future
histograms using at most `t` combined observed-and-future gap types. -/
theorem refinedF_prefix (a : ℕ → ℕ) (s : Finset ℕ) (A k u t : ℕ) :
    (∑ j ∈ range (t + 1), refinedF a s A k u j) =
      ∑ b ∈ s.piAntidiag k,
        if lengthSum s b = u ∧ occupied a s b ≤ t then
          admissibleOrders s A b * weight a s b else 0 := by
  classical
  unfold refinedF
  rw [sum_comm]
  apply sum_congr rfl
  intro b hb
  by_cases hu : lengthSum s b = u
  · by_cases ht : occupied a s b ≤ t
    · have hj : occupied a s b ∈ range (t + 1) := mem_range.mpr (by omega)
      simp [hu, ht, eq_comm, hj]
    · have hj : occupied a s b ∉ range (t + 1) := by simp only [mem_range]; omega
      simp [hu, ht, eq_comm, hj]
  · simp [hu]

def restrictedContribution (H t : ℕ) (z : List Bool) (A : ℕ) (b : ℕ → ℕ) : ℚ :=
  if occupied (observedCounts z) (gapSet H) b ≤ t then contribution H z A b else 0

/-- The restricted source mass grouped by natural count vectors in the same
ambient alphabet as the actual refined DP. -/
theorem restrictedContinuation_countFamily (H t : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length + R ≤ H) :
    restrictedContinuation (z.length + R) t z =
      ∑ b : CountFamily (parseAge 0 z + R),
        restrictedContribution H t z (parseAge 0 z) b.val := by
  classical
  rw [restrictedContinuation_histograms H t z R hH]
  apply Fintype.sum_equiv (countsEquivFamily (parseAge 0 z + R))
  intro c
  have hTH : parseAge 0 z + R ≤ H := by have hh := age_le_length z; omega
  let b := countsToFamily (parseAge 0 z + R) c
  have hs : (gapSet H).sum b.val = gapCount (fun i => (c.val i).val) := by
    rw [← sum_alphabet_eq _ _ b.val (gapSet_mono hTH) b.prop.1]
    exact family_count_eq_gapCount c
  have ho := admissibleOrders_alphabet_eq (gapSet (parseAge 0 z + R)) (gapSet H)
    (parseAge 0 z) b.val (gapSet_mono hTH) b.prop.1
  change _ = restrictedContribution H t z (parseAge 0 z) b.val
  unfold restrictedContribution contribution
  rw [hs, ← ho]
  by_cases ht : occupied (observedCounts z) (gapSet H) b.val ≤ t
  · by_cases hk : 0 < gapCount (fun i => (c.val i).val)
    · simp [ht, hk, Nat.ne_of_gt hk, b]
    · have hz : gapCount (fun i => (c.val i).val) = 0 := by omega
      simp [ht, hz, b]
  · simp [ht, b]

lemma restricted_state_mass (H t : ℕ) (z : List Bool) (A k u : ℕ) (hk : k ≠ 0) :
    (∑ b ∈ (gapSet H).piAntidiag k,
      if lengthSum (gapSet H) b = u then restrictedContribution H t z A b else 0) =
      ((∑ j ∈ range (t + 1), refinedF (observedCounts z) (gapSet H) A k u j : ℕ) : ℚ) /
        (((parseGaps 0 z).length + k : ℕ) : ℚ) ^ ((parseGaps 0 z).length + k) := by
  rw [refinedF_prefix, Nat.cast_sum, sum_div]
  apply sum_congr rfl
  intro b hb
  have hs := (mem_piAntidiag.mp hb).1
  unfold restrictedContribution contribution histogramMass
  by_cases hu : lengthSum (gapSet H) b = u
  · by_cases ht : occupied (observedCounts z) (gapSet H) b ≤ t
    · simp only [hu, ht, and_self, if_true, hs, if_neg hk, Nat.cast_mul]
      ring
    · simp [hu, ht]
  · simp [hu]

lemma zero_restricted_state_mass (H T t : ℕ) (z : List Bool) (A : ℕ) :
    (∑ u ∈ range (T + 1), ∑ b ∈ (gapSet H).piAntidiag 0,
      if lengthSum (gapSet H) b = u then restrictedContribution H t z A b else 0) =
      if occupied (observedCounts z) (gapSet H) 0 ≤ t then histogramMass H z 0 else 0 := by
  simp [restrictedContribution, lengthSum, contribution]

lemma refinedF_prefix_zero_of_lt (H A k u t : ℕ) (a : ℕ → ℕ) (hku : u < k) :
    (∑ j ∈ range (t + 1), refinedF a (gapSet H) A k u j) = 0 := by
  rw [refinedF_prefix]
  apply sum_eq_zero
  intro b hb
  have hsum := (mem_piAntidiag.mp hb).1
  have hbound := count_le_weight H b
  have hne : lengthSum (gapSet H) b ≠ u := by omega
  simp [hne]

end Paper37.RefinedContinuation

namespace Paper37.RefinedContinuation
open Finset Paper37.DP Paper37.Envelope Paper37.Prediction Paper37.Adaptive
open Paper37.AdaptiveDP Paper37.ContinuationDP Paper37.AdaptiveContinuation

/-- E.7 with the independent first-admissible refined counts. -/
theorem restrictedContinuation_eq_refinedF (H t : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length + R ≤ H) :
    restrictedContinuation (z.length + R) t z = restrictedEnvelope t z +
      ∑ k ∈ Icc 1 (parseAge 0 z + R), ∑ u ∈ Icc k (parseAge 0 z + R),
        ((∑ j ∈ range (t + 1), refinedF (observedCounts z) (gapSet H) (parseAge 0 z) k u j : ℕ) : ℚ) /
          (((parseGaps 0 z).length + k : ℕ) : ℚ) ^ ((parseGaps 0 z).length + k) := by
  classical
  let T := parseAge 0 z + R
  have hTH : T ≤ H := by have hh := age_le_length z; dsimp [T]; omega
  rw [restrictedContinuation_countFamily H t z R hH, countFamily_sum_ambient H T hTH]
  have hrange : range (T + 1) = insert 0 (Icc 1 T) := by
    ext k
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hrange, sum_insert (by simp)]
  have hzstate : (∑ u ∈ insert 0 (Icc 1 T), ∑ b ∈ (gapSet H).piAntidiag 0,
      if lengthSum (gapSet H) b = u then restrictedContribution H t z (parseAge 0 z) b else 0) =
      restrictedEnvelope t z := by
    rw [← hrange, zero_restricted_state_mass, histogramMass_zero H z (by omega),
      occupied_observed_zero H z (by omega)]
    rfl
  rw [hzstate]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hkn : k ≠ 0 := Nat.ne_of_gt ((mem_Icc.mp hk).1)
  calc
    _ = ∑ u ∈ insert 0 (Icc 1 T),
        ((∑ j ∈ range (t + 1), refinedF (observedCounts z) (gapSet H) (parseAge 0 z) k u j : ℕ) : ℚ) /
          (((parseGaps 0 z).length + k : ℕ) : ℚ) ^ ((parseGaps 0 z).length + k) := by
      apply sum_congr rfl
      intro u hu
      exact restricted_state_mass H t z (parseAge 0 z) k u hkn
    _ = ∑ u ∈ Icc k T,
        ((∑ j ∈ range (t + 1), refinedF (observedCounts z) (gapSet H) (parseAge 0 z) k u j : ℕ) : ℚ) /
          (((parseGaps 0 z).length + k : ℕ) : ℚ) ^ ((parseGaps 0 z).length + k) := by
      rw [← hrange]
      symm
      apply sum_subset
      · intro u hu
        simp only [mem_Icc, mem_range] at hu ⊢
        omega
      · intro u hu hnot
        have hlt : u < k := by simp only [mem_Icc, mem_range] at hu hnot; omega
        rw [refinedF_prefix_zero_of_lt H (parseAge 0 z) k u t (observedCounts z) hlt]
        simp

/-- Exact integer division after summing the occupied-type prefix. -/
theorem refinedS_prefix_div (a : ℕ → ℕ) (s : Finset ℕ) (A k u t : ℕ) (hk : 0 < k) :
    (∑ j ∈ range (t + 1), refinedS a s A k u j) / k =
      ∑ j ∈ range (t + 1), refinedF a s A k u j := by
  have heq : (∑ j ∈ range (t + 1), refinedS a s A k u j) =
      k * (∑ j ∈ range (t + 1), refinedF a s A k u j) := by
    simp_rw [refinedS_eq_mul_F]
    rw [mul_sum]
  rw [heq, Nat.mul_div_right _ hk]

/-- E.7 exactly, with the certified integer division used by the executable
implementation of every support-restricted continuation. -/
theorem restrictedContinuation_eq_integerDP (H t : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length + R ≤ H) :
    restrictedContinuation (z.length + R) t z = restrictedEnvelope t z +
      ∑ k ∈ Icc 1 (parseAge 0 z + R), ∑ u ∈ Icc k (parseAge 0 z + R),
        (((∑ j ∈ range (t + 1), refinedSd (observedCounts z) (parseAge 0 z) H k u j) / k : ℕ) : ℚ) /
          (((parseGaps 0 z).length + k : ℕ) : ℚ) ^ ((parseGaps 0 z).length + k) := by
  rw [restrictedContinuation_eq_refinedF H t z R hH]
  congr 1
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro u hu
  rw [show (∑ j ∈ range (t + 1), refinedSd (observedCounts z) (parseAge 0 z) H k u j) / k =
      ∑ j ∈ range (t + 1), refinedF (observedCounts z) (gapSet H) (parseAge 0 z) k u j from
    refinedS_prefix_div _ _ _ _ _ _ ((mem_Icc.mp hk).1)]

def refinedLayerAt {H : ℕ} (table : RefinedLayer H) (k u j : ℕ) : ℕ × ℕ :=
  if hk : k < H + 1 then if hu : u < H + 1 then if hj : j < H + 1 then
    refinedAt table ⟨k,hk⟩ ⟨u,hu⟩ ⟨j,hj⟩ else (0,0) else (0,0) else (0,0)

lemma refinedLayerAt_run (H : ℕ) (a : ℕ → ℕ) (A d k u j : ℕ)
    (hk : k ≤ H) (hu : u ≤ H) (hj : j ≤ H) :
    refinedLayerAt (refinedRun H a A d) k u j =
      (refinedGd a d k u j, refinedSd a A d k u j) := by
  have hk' : k < H + 1 := by omega
  have hu' : u < H + 1 := by omega
  have hj' : j < H + 1 := by omega
  simp only [refinedLayerAt, dif_pos hk', dif_pos hu', dif_pos hj']
  exact refinedRun_correct H a A d ⟨k,hk'⟩ ⟨u,hu'⟩ ⟨j,hj'⟩

/-- Extract every occupied-type restriction from one supplied materialized
refined table. No component causes the recurrence to be rerun. -/
def restrictedFromTable (H : ℕ) (z : List Bool) (R : ℕ) (table : RefinedLayer H) : Vector ℚ (H + 1) :=
  let A := parseAge 0 z
  let r := (parseGaps 0 z).length
  let T := A + R
  let nf := histogramMass H z 0
  let observedTypes := nu z
  Vector.ofFn fun t =>
    (if observedTypes ≤ t.val then nf else 0) +
      ∑ k ∈ Icc 1 T, ∑ u ∈ Icc k T,
        (((∑ j ∈ range (t.val + 1), (refinedLayerAt table k u j).2) / k : ℕ) : ℚ) /
          ((r + k : ℕ) : ℚ) ^ (r + k)

/-- The actual all-restrictions query computes the materialized refined table
once, then extracts each requested prefix of the occupied-type coordinate. -/
def evaluateRestrictedAll (H : ℕ) (z : List Bool) (R : ℕ) : Vector ℚ (H + 1) :=
  let table := refinedRun H (observedCounts z) (parseAge 0 z) H
  restrictedFromTable H z R table

theorem evaluateRestrictedAll_correct (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length + R ≤ H) (t : Fin (H + 1)) :
    (evaluateRestrictedAll H z R)[t.val] = restrictedContinuation (z.length + R) t.val z := by
  rw [restrictedContinuation_eq_integerDP H t.val z R hH]
  unfold evaluateRestrictedAll restrictedFromTable
  dsimp only
  simp only [Vector.getElem_ofFn]
  rw [histogramMass_zero H z (by omega)]
  change (if nu z ≤ t.val then wordEnvelope z else 0) + _ = _
  unfold restrictedEnvelope
  congr 1
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro u hu
  congr 2
  congr 1
  apply sum_congr rfl
  intro j hj
  have hTH : parseAge 0 z + R ≤ H := by have hh := age_le_length z; omega
  rw [refinedLayerAt_run H (observedCounts z) (parseAge 0 z) H k u j
    ((mem_Icc.mp hk).2.trans hTH) ((mem_Icc.mp hu).2.trans hTH) (by
      have hh := mem_range.mp hj; have ht := t.isLt; omega)]

lemma restrictedContinuation_cap (H t : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length + R ≤ H) :
    restrictedContinuation (z.length + R) t z =
      restrictedContinuation (z.length + R) (min t H) z := by
  unfold restrictedContinuation
  rw [show z.length + R - z.length = R by omega]
  apply sum_congr rfl
  intro v hv
  have hvl : v.length = R := (Paper37.Renewal.mem_words R v).mp (List.mem_toFinset.mp hv)
  have hn : nu (z ++ v) ≤ H := (nu_le_length _).trans (by simp [hvl]; omega)
  unfold restrictedEnvelope
  have he : nu (z ++ v) ≤ min t H ↔ nu (z ++ v) ≤ t := by omega
  simp only [he]

/-- Query any support size by retrieving its capped component from the one
shared all-restrictions table. -/
def evaluateRestricted (H t : ℕ) (z : List Bool) (R : ℕ) : ℚ :=
  (evaluateRestrictedAll H z R)[min t H]'(by have hh := min_le_right t H; omega)

theorem evaluateRestricted_correct (H t : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length + R ≤ H) :
    evaluateRestricted H t z R = restrictedContinuation (z.length + R) t z := by
  unfold evaluateRestricted
  exact (evaluateRestrictedAll_correct H z R hH
    ⟨min t H, by have hh := min_le_right t H; omega⟩).trans
      (restrictedContinuation_cap H t z R hH).symm

end Paper37.RefinedContinuation

namespace Paper37.RefinedContinuation
open Finset Paper37.DP Paper37.Envelope Paper37.Prediction Paper37.Adaptive
open Paper37.AdaptiveDP Paper37.ContinuationDP Paper37.AdaptiveContinuation

/-- Retrieve a restriction from a previously computed shared table result. -/
def lookupRestriction {H : ℕ} (values : Vector ℚ (H + 1)) (t : ℕ) : ℚ :=
  values[min t H]'(by have hh := min_le_right t H; omega)

lemma lookupRestriction_correct (H t : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length + R ≤ H) :
    lookupRestriction (evaluateRestrictedAll H z R) t =
      restrictedContinuation (z.length + R) t z := evaluateRestricted_correct _ _ _ _ hH

/-- One adaptive prefix query. Visible first renewal queries share one
refinement table across all continuation components and one across all
normalizers, then mix component prefix probabilities before taking ratios. -/
def evaluateAdaptivePrefix (N : ℕ) (y : List Bool) : ℚ :=
  match firstSuffix y with
  | none => ((N - y.length + 1 : ℕ) : ℚ) / (N + 1 : ℚ)
  | some z =>
    let L := N - y.length + z.length
    let masses := evaluateRestrictedAll L z (L - z.length)
    let normalizers := evaluateRestrictedAll L [] L
    ∑ t ∈ Icc 1 N, omegaWeight N t *
      (lookupRestriction masses t / ((N + 1 : ℚ) * lookupRestriction normalizers t))

theorem evaluateAdaptivePrefix_correct (N : ℕ) (y : List Bool)
    (hN : 1 ≤ N) (hy : y.length ≤ N) :
    evaluateAdaptivePrefix N y = adaptivePrefix N y := by
  unfold evaluateAdaptivePrefix
  cases hs : firstSuffix y with
  | none =>
    dsimp only
    rw [adaptivePrefix_eq_mix N y hy]
    have hz := (Paper37.EnvelopeBridge.firstSuffix_none_iff y).mp hs
    have hprefix (t : ℕ) : restrictedPrefix N t y =
        ((N - y.length + 1 : ℕ) : ℚ) / (N + 1 : ℚ) := by
      conv_lhs => rw [hz, restrictedPrefix_zeros N t y.length hy]
    simp_rw [hprefix]
    rw [← sum_mul, omegaWeight_sum hN, one_mul]
  | some z =>
    dsimp only
    obtain ⟨j,hj⟩ := Paper37.EnvelopeBridge.firstSuffix_some_decomposition y z hs
    have hlen : y.length = j + 1 + z.length := by simp [hj]; omega
    have hz : z.length ≤ N - (j + 1) := by omega
    have hL : N - y.length + z.length = N - (j + 1) := by omega
    rw [hL, adaptivePrefix_eq_mix N y hy]
    apply sum_congr rfl
    intro t ht
    have hm := lookupRestriction_correct (N - (j + 1)) t z (N - (j + 1) - z.length)
      (by omega)
    have hnorm := lookupRestriction_correct (N - (j + 1)) t [] (N - (j + 1)) (by simp)
    have hsum : z.length + (N - (j + 1) - z.length) = N - (j + 1) := Nat.add_sub_of_le hz
    simp only [hsum, List.length_nil, zero_add, restrictedContinuation_nil] at hm hnorm
    rw [hm, hnorm, hj, restrictedPrefix_firstRenewal N t j z (by omega)]

/-- The adaptive conditional uses two mixed prefix masses. -/
def evaluateAdaptiveConditional (N : ℕ) (y : List Bool) : ℚ :=
  evaluateAdaptivePrefix N (y ++ [true]) / evaluateAdaptivePrefix N y

theorem evaluateAdaptiveConditional_correct (N : ℕ) (y : List Bool) (hy : y.length < N) :
    evaluateAdaptiveConditional N y = adaptiveConditional N y := by
  unfold evaluateAdaptiveConditional adaptiveConditional
  rw [evaluateAdaptivePrefix_correct N _ (by omega) (by simp; omega),
    evaluateAdaptivePrefix_correct N y (by omega) hy.le]

/-- Executable adaptive compression-averaged predictor, using only the supplied
linear suffix batch and the shared all-restrictions table at each query. -/
def evaluateAdaptivePredictor (n : ℕ) (x : List Bool) : ℚ :=
  (∑ t ∈ Icc 1 n, evaluateAdaptiveConditional (n + 1) (x.drop (n - t))) / n

theorem evaluateAdaptivePredictor_correct (n : ℕ) (x : List Bool) (hx : x.length = n) :
    evaluateAdaptivePredictor n x = adaptivePredict n x := by
  unfold evaluateAdaptivePredictor adaptivePredict
  congr 1
  apply sum_congr rfl
  intro t ht
  apply evaluateAdaptiveConditional_correct
  have htn : t ≤ n := (mem_Icc.mp ht).2
  simp only [List.length_drop, hx]
  omega

end Paper37.RefinedContinuation

namespace Paper37.RefinedContinuation
open Finset Paper37.DP Paper37.Envelope Paper37.Prediction Paper37.Adaptive
open Paper37.AdaptiveDP Paper37.ContinuationDP Paper37.AdaptiveContinuation

/-- E.7 in the paper's rational notation, equivalent to the exact integer
prefix division used in the actual query. -/
theorem restrictedContinuation_eq_multisetDP (H t : ℕ) (z : List Bool) (R : ℕ)
    (hH : z.length + R ≤ H) :
    restrictedContinuation (z.length + R) t z = restrictedEnvelope t z +
      ∑ k ∈ Icc 1 (parseAge 0 z + R), ∑ u ∈ Icc k (parseAge 0 z + R),
        ((∑ j ∈ range (t + 1), refinedSd (observedCounts z) (parseAge 0 z) H k u j : ℕ) : ℚ) /
          ((k : ℚ) * (((parseGaps 0 z).length + k : ℕ) : ℚ) ^
            ((parseGaps 0 z).length + k)) := by
  rw [restrictedContinuation_eq_refinedF H t z R hH]
  refine congrArg (fun q : ℚ => restrictedEnvelope t z + q) ?_
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro u hu
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ((mem_Icc.mp hk).1)
  have heq : (∑ j ∈ range (t + 1), refinedSd (observedCounts z) (parseAge 0 z) H k u j) =
      k * (∑ j ∈ range (t + 1), refinedF (observedCounts z) (gapSet H) (parseAge 0 z) k u j) := by
    simp_rw [refinedSd, refinedS_eq_mul_F]
    rw [mul_sum]
  rw [heq, Nat.cast_mul]
  exact (mul_div_mul_left _ _ hk').symm

/-- All restricted normalizers come from one empty-prefix refinement table. -/
def evaluateRestrictedNormalizers (H : ℕ) : Vector ℚ (H + 1) :=
  evaluateRestrictedAll H [] H

theorem evaluateRestrictedNormalizers_correct (H t : ℕ) :
    lookupRestriction (evaluateRestrictedNormalizers H) t = restrictedNormalizer H t := by
  unfold evaluateRestrictedNormalizers
  simpa only [List.length_nil, zero_add, restrictedContinuation_nil] using
    lookupRestriction_correct H t [] H (by simp)

/-- The all-zero-horizon convention agrees with the source adaptiveMass. -/
def evaluateAdaptiveMass (x : List Bool) : ℚ :=
  if x = [] then 1 else evaluateAdaptivePrefix x.length x

theorem evaluateAdaptiveMass_correct (x : List Bool) :
    evaluateAdaptiveMass x = adaptiveMass x := by
  unfold evaluateAdaptiveMass adaptiveMass
  by_cases hx : x = []
  · simp [hx]
  · rw [if_neg hx, if_neg hx, evaluateAdaptivePrefix_correct x.length x
      (by have hh : 0 < x.length := List.length_pos_iff.mpr hx; omega) (le_refl _)]
    simp [adaptivePrefix, Paper37.Renewal.words]

end Paper37.RefinedContinuation
