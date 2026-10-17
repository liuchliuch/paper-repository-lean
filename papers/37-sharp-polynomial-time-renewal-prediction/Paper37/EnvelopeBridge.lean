import Paper37.Envelope
import Paper37.PredictorSpec

/-!
# The envelope on the source binary sample space

These results identify the rational source assignments with the real-valued
ordered-gap combinatorics and transfer the partition and monotonicity bounds.
-/
noncomputable section
open scoped BigOperators
namespace Paper37.EnvelopeBridge
open Paper37.Renewal Paper37.Envelope Paper37.Prediction

lemma parseGaps_eq_gapsFrom (a : ℕ) (x : List Bool) :
    parseGaps a x = gapsFrom a x := by
  induction x generalizing a with
  | nil => rfl
  | cons b x ih => cases b <;> simp [parseGaps, gapsFrom, ih]

lemma gapEnvelope_cast (g : List ℕ) :
    (Prediction.gapEnvelope g : ℝ) = listEnvelope g := by
  unfold Prediction.gapEnvelope
  push_cast
  have hh := Finset.prod_multiset_map_count (g : Multiset ℕ)
    (fun d => (g.count d : ℝ) / g.length)
  simpa [listEnvelope] using hh.symm

lemma wordEnvelope_encode {L : ℕ} (b : Block L) :
    (wordEnvelope (encode b) : ℝ) = M b := by
  unfold wordEnvelope
  rw [gapEnvelope_cast, ← parseGaps_eq_gapsFrom, parseGaps_encode, ← M_eq_nat_listEnvelope]

/-- The source normalizer B.4 is exactly the sum over completed ordered gaps. -/
theorem ordinaryNormalizer_cast (L : ℕ) : (ordinaryNormalizer L : ℝ) = Z L := by
  classical
  unfold ordinaryNormalizer Z
  push_cast
  symm
  apply Finset.sum_bij (fun b _ => encode b)
  · intro b hb
    exact List.mem_toFinset.mpr ((mem_words L (encode b)).mpr (encode_length b))
  · intro b hb c hc heq
    exact encode_injective L heq
  · intro x hx
    have hlen : x.length = L := (mem_words L x).mp (List.mem_toFinset.mp hx)
    exact ⟨ofWord L x hlen, Finset.mem_univ _, encode_ofWord L x hlen⟩
  · intro b hb
    exact (wordEnvelope_encode b).symm

/-- The integer-partition normalization inequality in Lemma B.1 on binary words. -/
theorem ordinaryNormalizer_le_partitions (L : ℕ) :
    ordinaryNormalizer L ≤ cumulativePartitions L := by
  have hh := Z_le_cumulativePartitions L
  rw [← ordinaryNormalizer_cast] at hh
  exact_mod_cast hh

/-- The monotonicity clause of Lemma B.1 on the source normalizer. -/
theorem ordinaryNormalizer_monotone : Monotone ordinaryNormalizer := by
  intro L K hLK
  have hh := Z_monotone hLK
  rw [← ordinaryNormalizer_cast L, ← ordinaryNormalizer_cast K] at hh
  exact_mod_cast hh

@[simp] theorem ordinaryNormalizer_zero : ordinaryNormalizer 0 = 1 := by
  simp [ordinaryNormalizer, words, wordEnvelope, gapsFrom, Prediction.gapEnvelope]

lemma ordinaryAssignment_encode {L : ℕ} (b : Block L) :
    (ordinaryAssignment (encode b) : ℝ) = q b := by
  unfold ordinaryAssignment q
  push_cast
  rw [encode_length, wordEnvelope_encode, ordinaryNormalizer_cast]

/-- Every queried horizon has a normalized full-support ordinary assignment. -/
theorem ordinaryAssignment_sum (L : ℕ) :
    ∑ x ∈ (words L).toFinset, ordinaryAssignment x = 1 := by
  have hn := (Prediction.ordinaryNormalizer_pos L).ne'
  calc
    _ = ∑ x ∈ (words L).toFinset, wordEnvelope x / ordinaryNormalizer L := by
      apply Finset.sum_congr rfl
      intro x hx
      have hh : x.length = L := (mem_words L x).mp (List.mem_toFinset.mp hx)
      rw [ordinaryAssignment, hh]
    _ = 1 := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      exact mul_inv_cancel₀ hn

/-- The ordinary completed-gap likelihood bound in B.3, directly on binary
words under the genuine finite-mean gap law. -/
theorem ordinary_le_wordEnvelope (μ : Law) (x : List Bool) :
    ordinary μ 0 x ≤ (wordEnvelope x : ℝ) := by
  let b := ofWord x.length x rfl
  have hμsum : ∑ i : Fin x.length, μ.mass i.val ≤ 1 := by
    rw [Fin.sum_univ_eq_sum_range]
    calc
      _ ≤ ∑' d, μ.mass d := μ.total.summable.sum_le_tsum _ (fun d hd => μ.nonneg d)
      _ = 1 := μ.total.tsum_eq
  have hc := censored_likelihood_le_M b (fun i => μ.mass i.val)
    (fun i => μ.nonneg i.val) hμsum (tail μ (ageFrom 0 x))
    (tail_nonneg μ _) (tail_le_one μ _)
  rw [← wordEnvelope_encode b, encode_ofWord] at hc
  rw [ordinary_completed_gaps]
  have hg : (gapList b).map Fin.val = gapsFrom 0 x := by
    rw [gapList_ofWord_vals, parseGaps_eq_gapsFrom]
  simpa only [← hg, List.map_map, Function.comp_def] using hc

/-- A finite sum over all binary words splits by their first symbol. -/
lemma sum_words_step {R : Type*} [AddCommMonoid R] (n : ℕ) (f : List Bool → R) :
    (∑ x ∈ (words (n+1)).toFinset, f x) =
      (∑ x ∈ (words n).toFinset, f (false::x)) +
      ∑ x ∈ (words n).toFinset, f (true::x) := by
  simp_rw [List.sum_toFinset _ (words_nodup _)]
  simp [words, List.map_map, Function.comp_def]

/-- First-renewal component mass before its uniform mixing weight. -/
def componentMass (x : List Bool) : ℚ :=
  match firstSuffix x with
  | none => 1
  | some suffix => ordinaryAssignment suffix

lemma componentMass_sum (N : ℕ) :
    (∑ x ∈ (words N).toFinset, componentMass x) = N+1 := by
  induction N with
  | zero => simp [words, componentMass, firstSuffix]
  | succ N ih =>
    rw [sum_words_step]
    change (∑ x ∈ (words N).toFinset, componentMass x) +
      (∑ x ∈ (words N).toFinset, ordinaryAssignment x) = _
    rw [ih, ordinaryAssignment_sum]
    push_cast
    ring

/-- B.7 is normalized on the actual binary alphabet. -/
theorem blockAssignment_sum (N : ℕ) :
    (∑ x ∈ (words N).toFinset, blockAssignment x) = 1 := by
  calc
    _ = (∑ x ∈ (words N).toFinset, componentMass x) / (N+1 : ℚ) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hlen := (mem_words N x).mp (List.mem_toFinset.mp hx)
      unfold blockAssignment componentMass
      rw [hlen]
      rfl
    _ = 1 := by rw [componentMass_sum]; exact div_self (by positivity)

lemma firstSuffix_zeros_prefix (t : ℕ) (x : List Bool) :
    firstSuffix (List.replicate t false ++ x) = firstSuffix x := by
  induction t with
  | zero => simp
  | succ t ih => simpa [firstSuffix] using ih

/-- All-zero prefix mass is exactly the number of compatible first-renewal
components times their common mixture weight. -/
theorem prefixMass_zeros (N t : ℕ) (ht : t ≤ N) :
    prefixMass N (List.replicate t false) = (N-t+1 : ℕ) / (N+1 : ℚ) := by
  unfold prefixMass
  simp only [List.length_replicate]
  calc
    _ = (∑ v ∈ (words (N-t)).toFinset, componentMass v) / (N+1 : ℚ) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      have hlen := (mem_words (N-t) v).mp (List.mem_toFinset.mp hv)
      have hN : (List.replicate t false ++ v).length = N := by simp [hlen]; omega
      unfold blockAssignment componentMass
      rw [hN, firstSuffix_zeros_prefix]
      rfl
    _ = _ := by rw [componentMass_sum]; push_cast; rfl

lemma prefixMass_zeros_one (N t : ℕ) (ht : t < N) :
    prefixMass N (List.replicate t false ++ [true]) = 1 / (N+1 : ℚ) := by
  unfold prefixMass
  have hlen : (List.replicate t false ++ [true]).length = t+1 := by simp
  rw [hlen]
  calc
    _ = (∑ v ∈ (words (N-(t+1))).toFinset, ordinaryAssignment v) / (N+1 : ℚ) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      have hvlen := (mem_words (N-(t+1)) v).mp (List.mem_toFinset.mp hv)
      have hN : ((List.replicate t false ++ [true]) ++ v).length = N := by simp [hvlen]; omega
      unfold blockAssignment
      rw [hN]
      simp only [List.append_assoc, List.singleton_append, firstSuffix_zeros_prefix,
        firstSuffix, div_eq_mul_inv]
    _ = _ := by rw [ordinaryAssignment_sum]

/-- Proposition C.2, equation C.10, including the stationary all-zero boundary. -/
theorem blockConditional_zeros (N t : ℕ) (ht : t < N) :
    blockConditional N (List.replicate t false) = 1 / ((N-t+1 : ℕ) : ℚ) := by
  rw [blockConditional, prefixMass_zeros_one N t ht, prefixMass_zeros N t ht.le]
  have hN : (N+1 : ℚ) ≠ 0 := by positivity
  have hr : ((N-t+1 : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp

/-- Once the first renewal is observed, its component factor is shared by
all completions and the remaining mass is exactly the ordinary W mass. -/
theorem prefixMass_firstRenewal (N j : ℕ) (z : List Bool)
    (hz : j+1+z.length ≤ N) :
    prefixMass N (List.replicate j false ++ true::z) =
      continuationMass (N-(j+1)) z / ((N+1 : ℚ) * ordinaryNormalizer (N-(j+1))) := by
  unfold prefixMass continuationMass
  have hrem : N - (List.replicate j false ++ true::z).length = N-(j+1)-z.length := by simp; omega
  rw [hrem]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  have hvlen := (mem_words (N-(j+1)-z.length) v).mp (List.mem_toFinset.mp hv)
  have hslen : (z++v).length = N-(j+1) := by simp [hvlen]; omega
  have hN : ((List.replicate j false ++ true::z) ++ v).length = N := by simp [hvlen]; omega
  unfold blockAssignment
  rw [hN]
  simp only [List.append_assoc, List.cons_append, firstSuffix_zeros_prefix, firstSuffix]
  simp [ordinaryAssignment, hslen, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]

lemma continuationMass_step (L : ℕ) (z : List Bool) (hz : z.length < L) :
    continuationMass L z = continuationMass L (z++[false]) + continuationMass L (z++[true]) := by
  unfold continuationMass
  have hrem : L-z.length = (L-(z.length+1))+1 := by omega
  rw [hrem, sum_words_step]
  simp [List.append_assoc]

lemma continuationMass_pos (L : ℕ) (z : List Bool) : 0 < continuationMass L z := by
  apply Finset.sum_pos'
  · intro v hv; exact (wordEnvelope_pos _).le
  · refine ⟨List.replicate (L-z.length) false, ?_, wordEnvelope_pos _⟩
    exact List.mem_toFinset.mpr ((mem_words _ _).mpr (by simp))

/-- Proposition C.2, equation C.11, for every prefix whose first one is visible. -/
theorem blockConditional_firstRenewal (N j : ℕ) (z : List Bool)
    (hz : j+1+z.length < N) :
    blockConditional N (List.replicate j false ++ true::z) =
      continuationMass (N-(j+1)) (z++[true]) /
        (continuationMass (N-(j+1)) (z++[false]) + continuationMass (N-(j+1)) (z++[true])) := by
  have hz' : j+1+(z++[true]).length ≤ N := by simp; omega
  have hzL : z.length < N-(j+1) := by omega
  unfold blockConditional
  rw [show (List.replicate j false ++ true::z) ++ [true] =
      List.replicate j false ++ true::(z++[true]) by simp]
  rw [prefixMass_firstRenewal N j (z++[true]) hz', prefixMass_firstRenewal N j z hz.le]
  rw [← continuationMass_step _ z hzL]
  have hden : (N+1 : ℚ) * ordinaryNormalizer (N-(j+1)) ≠ 0 :=
    mul_ne_zero (by positivity) (Prediction.ordinaryNormalizer_pos _).ne'
  have hZ := (Prediction.ordinaryNormalizer_pos (N-(j+1))).ne'
  have hW := (continuationMass_pos (N-(j+1)) z).ne'
  field_simp

/-- Completed-gap part of B.3, before multiplying the terminal survival. -/
theorem completed_gap_likelihood_le_wordEnvelope (μ : Law) (x : List Bool) :
    ((gapsFrom 0 x).map μ.mass).prod ≤ (wordEnvelope x : ℝ) := by
  let b := ofWord x.length x rfl
  have hμsum : ∑ i : Fin x.length, μ.mass i.val ≤ 1 := by
    rw [Fin.sum_univ_eq_sum_range]
    calc
      _ ≤ ∑' d, μ.mass d := μ.total.summable.sum_le_tsum _ (fun d hd => μ.nonneg d)
      _ = 1 := μ.total.tsum_eq
  have hc := completed_likelihood_le_M b (fun i => μ.mass i.val)
    (fun i => μ.nonneg i.val) hμsum
  rw [← wordEnvelope_encode b, encode_ofWord] at hc
  have hg : (gapList b).map Fin.val = gapsFrom 0 x := by
    rw [gapList_ofWord_vals, parseGaps_eq_gapsFrom]
  simpa only [← hg, List.map_map, Function.comp_def] using hc

lemma blockMass_le_wordEnvelope_suffix (μ : Law) (j : ℕ) (x : List Bool) :
    blockMass μ (List.replicate j false ++ true::x) ≤ (wordEnvelope x : ℝ) :=
  (blockMass_le_completed_gap_likelihood μ j x).trans
    (completed_gap_likelihood_le_wordEnvelope μ x)

lemma firstSuffix_none_iff (x : List Bool) :
    firstSuffix x = none ↔ x = List.replicate x.length false := by
  induction x with
  | nil => simp [firstSuffix]
  | cons b x ih =>
    cases b with
    | false => simpa [firstSuffix, List.replicate_succ] using ih
    | true => simp [firstSuffix, List.replicate_succ]

lemma firstSuffix_some_decomposition (x z : List Bool) (h : firstSuffix x = some z) :
    ∃ j, x = List.replicate j false ++ true::z := by
  induction x with
  | nil => simp [firstSuffix] at h
  | cons b x ih =>
    cases b with
    | true =>
      have hh : x = z := Option.some.inj h
      exact ⟨0, by simp [hh]⟩
    | false =>
      obtain ⟨j,hj⟩ := ih h
      exact ⟨j+1, by simp [hj, List.replicate_succ]⟩

lemma blockMass_le_one (μ : Law) (x : List Bool) : blockMass μ x ≤ 1 := by
  have hh := blockMass_normalized μ x.length
  unfold wordSum at hh
  rw [← List.sum_toFinset _ (words_nodup _)] at hh
  rw [← hh]
  exact Finset.single_le_sum (fun y hy => blockMass_nonneg μ y)
    (List.mem_toFinset.mpr ((mem_words _ _).mpr rfl))

/-- The finite-time multiplicative block regret on the source sample space,
prior to the analytic estimate on the integer-partition normalizer. -/
theorem blockAssignment_ratio_bound (μ : Law) (x : List Bool) :
    blockMass μ x / (blockAssignment x : ℝ) ≤
      (x.length+1 : ℝ) * (ordinaryNormalizer x.length : ℝ) := by
  have hq : 0 < (blockAssignment x : ℝ) := by exact_mod_cast blockAssignment_pos x
  cases hs : firstSuffix x with
  | none =>
    have hQ : (blockAssignment x : ℝ) = 1 / (x.length+1 : ℝ) := by
      simp [blockAssignment, hs]
    rw [hQ]
    have hh : blockMass μ x / (1 / (x.length+1 : ℝ)) ≤ (x.length+1 : ℝ) := by
      simp only [div_eq_mul_inv, inv_inv, one_mul]
      exact mul_le_of_le_one_left (by positivity) (blockMass_le_one μ x)
    exact hh.trans (le_mul_of_one_le_right (by positivity) (by
      rw [ordinaryNormalizer_cast]; exact one_le_Z _))
  | some z =>
    obtain ⟨j,hj⟩ := firstSuffix_some_decomposition x z hs
    have hp : blockMass μ x ≤ (wordEnvelope z : ℝ) := by
      rw [hj]
      exact blockMass_le_wordEnvelope_suffix μ j z
    have hZ : (0 : ℝ) < ordinaryNormalizer z.length := by exact_mod_cast Prediction.ordinaryNormalizer_pos _
    have hQ : (blockAssignment x : ℝ) =
        (wordEnvelope z : ℝ) / ((x.length+1 : ℝ) * (ordinaryNormalizer z.length : ℝ)) := by
      simp [blockAssignment, ordinaryAssignment, hs, div_div, mul_comm]
    have hlocal : blockMass μ x / (blockAssignment x : ℝ) ≤
        (x.length+1 : ℝ) * (ordinaryNormalizer z.length : ℝ) := by
      apply (div_le_iff₀ hq).mpr
      rw [hQ]
      have hn : (x.length+1 : ℝ) * (ordinaryNormalizer z.length : ℝ) ≠ 0 := by positivity
      rw [mul_div_cancel₀ _ hn]
      exact hp
    have hlen : z.length ≤ x.length := by simp [hj]; omega
    have hmono : (ordinaryNormalizer z.length : ℝ) ≤ ordinaryNormalizer x.length := by
      exact_mod_cast ordinaryNormalizer_monotone hlen
    exact hlocal.trans (mul_le_mul_of_nonneg_left hmono (by positivity))

/-- The source pointwise log-regret bound before substituting the classical
exponential partition estimate. -/
theorem blockAssignment_log_regret (μ : Law) (x : List Bool) (hp : 0 < blockMass μ x) :
    Real.log (blockMass μ x / (blockAssignment x : ℝ)) ≤
      Real.log ((x.length+1 : ℝ) * (ordinaryNormalizer x.length : ℝ)) := by
  apply Real.log_le_log
  · exact div_pos hp (by exact_mod_cast blockAssignment_pos x)
  · exact blockAssignment_ratio_bound μ x

/-- The KL redundancy clause of Proposition B.2 before the analytic partition
estimate. Full support makes every nonzero term a finite logarithm; zero mass
terms vanish in the usual finite-alphabet KL convention. -/
theorem blockAssignment_redundancy_bound (μ : Law) (N : ℕ) :
    (∑ x ∈ (words N).toFinset,
      blockMass μ x * Real.log (blockMass μ x / (blockAssignment x : ℝ))) ≤
      Real.log ((N+1 : ℝ) * (ordinaryNormalizer N : ℝ)) := by
  have hsum : (∑ x ∈ (words N).toFinset, blockMass μ x) = 1 := by
    rw [List.sum_toFinset _ (words_nodup N)]
    exact blockMass_normalized μ N
  calc
    _ ≤ ∑ x ∈ (words N).toFinset,
        blockMass μ x * Real.log ((N+1 : ℝ) * (ordinaryNormalizer N : ℝ)) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hp : blockMass μ x = 0
      · simp [hp]
      · have hpos : 0 < blockMass μ x := lt_of_le_of_ne (blockMass_nonneg μ x) (Ne.symm hp)
        have hh := blockAssignment_log_regret μ x hpos
        have hlen := (mem_words N x).mp (List.mem_toFinset.mp hx)
        rw [hlen] at hh
        exact mul_le_mul_of_nonneg_left hh (blockMass_nonneg μ x)
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Source equation C.10 with ordinary rational subtraction. -/
theorem blockConditional_zeros_rational (N t : ℕ) (ht : t < N) :
    blockConditional N (List.replicate t false) = 1 / ((N : ℚ) - t + 1) := by
  rw [blockConditional_zeros N t ht]
  congr 1
  rw [Nat.cast_add, Nat.cast_sub ht.le, Nat.cast_one]

/-- The normalization query is the empty-prefix continuation query C.1. -/
@[simp] theorem continuationMass_nil (L : ℕ) :
    continuationMass L [] = ordinaryNormalizer L := by
  simp [continuationMass, ordinaryNormalizer]

@[simp] theorem wordEnvelope_append_false (x : List Bool) :
    wordEnvelope (x ++ [false]) = wordEnvelope x := by
  unfold wordEnvelope
  rw [← parseGaps_eq_gapsFrom, parseGaps_append_false, parseGaps_eq_gapsFrom]

end Paper37.EnvelopeBridge
