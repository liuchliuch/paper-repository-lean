import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
Positive integer renewal gaps are encoded by `mass d = μ(d+1)`.
The finite mean is a genuine summability condition. No renewal, stationarity,
normalization, or prediction estimate is assumed in `Law`.
-/
namespace Paper37.Renewal
open scoped BigOperators

structure Law where
  mass : ℕ → ℝ
  nonneg : ∀ d, 0 ≤ mass d
  total : HasSum mass 1
  finiteMean : Summable (fun d : ℕ => ((d : ℝ) + 1) * mass d)

noncomputable def mean (μ : Law) : ℝ := ∑' d : ℕ, ((d : ℝ) + 1) * μ.mass d
noncomputable def tail (μ : Law) (a : ℕ) : ℝ :=
  ∑' d, if a ≤ d then μ.mass d else 0
noncomputable def residual (μ : Law) (n : ℕ) : ℝ :=
  ∑' d, ((d + 1 - n : ℕ) : ℝ) * μ.mass d

lemma tail_summable (μ : Law) (a : ℕ) :
    Summable (fun d => if a ≤ d then μ.mass d else 0) := by
  apply Summable.of_nonneg_of_le
  · intro d; split_ifs
    · exact μ.nonneg d
    · exact le_rfl
  · intro d; split_ifs
    · exact le_rfl
    · exact μ.nonneg d
  · exact μ.total.summable

lemma tail_nonneg (μ : Law) (a : ℕ) : 0 ≤ tail μ a := by
  apply tsum_nonneg
  intro d; split_ifs <;> simp_all [μ.nonneg]

lemma tail_le_one (μ : Law) (a : ℕ) : tail μ a ≤ 1 := by
  rw [← μ.total.tsum_eq]
  apply (tail_summable μ a).tsum_le_tsum _ μ.total.summable
  intro d; split_ifs <;> simp_all [μ.nonneg]

@[simp] lemma tail_zero (μ : Law) : tail μ 0 = 1 := by
  simpa [tail] using μ.total.tsum_eq

lemma tail_step (μ : Law) (a : ℕ) : tail μ a = μ.mass a + tail μ (a+1) := by
  have h : (fun d => if a ≤ d then μ.mass d else 0) =
      (fun d => if d = a then μ.mass a else 0) +
      (fun d => if a+1 ≤ d then μ.mass d else 0) := by
    funext d
    simp only [Pi.add_apply]
    by_cases hda : d = a
    · subst d; simp
    · by_cases h : a ≤ d
      · have h' : a+1 ≤ d := by omega
        simp [hda, h, h']
      · have h' : ¬a+1 ≤ d := by omega
        simp [hda, h, h']
  unfold tail
  rw [h]
  change (∑' d, ((if d = a then μ.mass a else 0) + (if a+1 ≤ d then μ.mass d else 0))) = _
  rw [Summable.tsum_add (hasSum_ite_eq a (μ.mass a)).summable (tail_summable μ (a+1))]
  simp

lemma tail_antitone (μ : Law) : Antitone (tail μ) := by
  intro a b hab
  apply (tail_summable μ b).tsum_le_tsum _ (tail_summable μ a)
  intro d
  by_cases hb : b ≤ d
  · have ha : a ≤ d := le_trans hab hb
    simp [ha, hb]
  · simp [hb]
    split_ifs <;> simp_all [μ.nonneg]

lemma residual_summable (μ : Law) (n : ℕ) :
    Summable (fun d => ((d+1-n : ℕ) : ℝ) * μ.mass d) := by
  refine Summable.of_nonneg_of_le
    (fun d => mul_nonneg (Nat.cast_nonneg _) (μ.nonneg d)) (fun d => ?_) μ.finiteMean
  apply mul_le_mul_of_nonneg_right _ (μ.nonneg d)
  exact_mod_cast Nat.sub_le (d+1) n

lemma residual_nonneg (μ : Law) (n : ℕ) : 0 ≤ residual μ n := by
  apply tsum_nonneg
  intro d; exact mul_nonneg (Nat.cast_nonneg _) (μ.nonneg d)

@[simp] lemma residual_zero (μ : Law) : residual μ 0 = mean μ := by
  simp [residual, mean]

lemma residual_step (μ : Law) (n : ℕ) :
    residual μ n = residual μ (n+1) + tail μ n := by
  have h : (fun d => ((d+1-n : ℕ) : ℝ) * μ.mass d) =
      (fun d => ((d+1-(n+1) : ℕ) : ℝ) * μ.mass d) +
      (fun d => if n ≤ d then μ.mass d else 0) := by
    funext d
    simp only [Pi.add_apply]
    by_cases hd : n ≤ d
    · have he : d+1-n = (d+1-(n+1))+1 := by omega
      rw [if_pos hd, he, Nat.cast_add, Nat.cast_one]
      ring
    · have h0 : d+1-n = 0 := by omega
      have h1 : d+1-(n+1) = 0 := by omega
      simp [hd, h0, h1]
  unfold residual tail
  rw [h]
  change (∑' d, (((d+1-(n+1) : ℕ) : ℝ) * μ.mass d + (if n ≤ d then μ.mass d else 0))) = _
  exact Summable.tsum_add (residual_summable μ (n+1)) (tail_summable μ n)

lemma residual_le_mean (μ : Law) (n : ℕ) : residual μ n ≤ mean μ := by
  apply (residual_summable μ n).tsum_le_tsum _ μ.finiteMean
  intro d
  apply mul_le_mul_of_nonneg_right _ (μ.nonneg d)
  exact_mod_cast Nat.sub_le (d+1) n

lemma mean_ge_one (μ : Law) : 1 ≤ mean μ := by
  have h := residual_step μ 0
  simp only [residual_zero, tail_zero] at h
  linarith [residual_nonneg μ 1]

lemma mean_pos (μ : Law) : 0 < mean μ := lt_of_lt_of_le zero_lt_one (mean_ge_one μ)

lemma residual_tail_identity (μ : Law) (n : ℕ) :
    mean μ = (∑ a ∈ Finset.range n, tail μ a) + residual μ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, residual_step μ n]
    ring

/-- Sum of the first `n+1` survival probabilities is at least
`(n+1) F̄(n)`, the weighting used in source Corollary D.4. -/
lemma tail_weight_bound (μ : Law) (n : ℕ) :
    (n+1 : ℝ) * tail μ n ≤ mean μ := by
  have hs : (n+1 : ℝ) * tail μ n ≤ ∑ a ∈ Finset.range (n+1), tail μ a := by
    calc
      _ = ∑ _a ∈ Finset.range (n+1), tail μ n := by simp
      _ ≤ _ := Finset.sum_le_sum fun a ha => tail_antitone μ (by
        have := Finset.mem_range.mp ha; omega)
  have hm := residual_tail_identity μ (n+1)
  linarith [residual_nonneg μ (n+1)]

/-- Exhaustive enumeration of binary words, with zeros first. -/
def words : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => (words n).map (false :: ·) ++ (words n).map (true :: ·)

def wordSum (n : ℕ) (f : List Bool → ℝ) : ℝ := ((words n).map f).sum

@[simp] lemma wordSum_zero (f : List Bool → ℝ) : wordSum 0 f = f [] := by
  simp [wordSum, words]

lemma wordSum_step (n : ℕ) (f : List Bool → ℝ) :
    wordSum (n+1) f = wordSum n (fun x => f (false::x)) +
      wordSum n (fun x => f (true::x)) := by
  simp [wordSum, words, List.map_map, Function.comp_def]

lemma wordSum_mul (n : ℕ) (c : ℝ) (f : List Bool → ℝ) :
    wordSum n (fun x => c * f x) = c * wordSum n f := by
  induction n generalizing f with
  | zero => simp
  | succ n ih => simp only [wordSum_step, ih]; ring

lemma mem_words (n : ℕ) (x : List Bool) : x ∈ words n ↔ x.length = n := by
  induction n generalizing x with
  | zero => simp [words, List.length_eq_zero_iff]
  | succ n ih =>
    cases x with
    | nil => simp [words]
    | cons b x => cases b <;> simp [words, ih, Nat.succ_eq_add_one]

/-- Ordinary likelihood with a known renewal at time zero. The age argument
permits induction through a censored zero run. -/
noncomputable def ordinary (μ : Law) (a : ℕ) : List Bool → ℝ
  | [] => tail μ a
  | false::x => ordinary μ (a+1) x
  | true::x => μ.mass a * ordinary μ 0 x

lemma ordinary_nonneg (μ : Law) (a : ℕ) (x : List Bool) : 0 ≤ ordinary μ a x := by
  induction x generalizing a with
  | nil => exact tail_nonneg μ a
  | cons b x ih => cases b with
    | false => exact ih (a+1)
    | true => exact mul_nonneg (μ.nonneg a) (ih 0)

lemma ordinary_normalized (μ : Law) (n a : ℕ) :
    wordSum n (ordinary μ a) = tail μ a := by
  induction n generalizing a with
  | zero => simp [ordinary]
  | succ n ih =>
    rw [wordSum_step]
    change wordSum n (ordinary μ (a+1)) +
      wordSum n (fun x => μ.mass a * ordinary μ 0 x) = _
    rw [wordSum_mul, ih, ih, tail_zero, mul_one]
    simpa [add_comm] using (tail_step μ a).symm

/-- Unnormalized stationary likelihood, tracking the equilibrium wait until
the first visible renewal. -/
noncomputable def stationaryNumerator (μ : Law) (a : ℕ) : List Bool → ℝ
  | [] => residual μ a
  | false::x => stationaryNumerator μ (a+1) x
  | true::x => tail μ a * ordinary μ 0 x

noncomputable def blockMass (μ : Law) (x : List Bool) : ℝ :=
  stationaryNumerator μ 0 x / mean μ

lemma stationaryNumerator_nonneg (μ : Law) (a : ℕ) (x : List Bool) :
    0 ≤ stationaryNumerator μ a x := by
  induction x generalizing a with
  | nil => exact residual_nonneg μ a
  | cons b x ih => cases b with
    | false => exact ih (a+1)
    | true => exact mul_nonneg (tail_nonneg μ a) (ordinary_nonneg μ 0 x)

lemma blockMass_nonneg (μ : Law) (x : List Bool) : 0 ≤ blockMass μ x :=
  div_nonneg (stationaryNumerator_nonneg μ 0 x) (le_of_lt (mean_pos μ))

lemma stationaryNumerator_normalized (μ : Law) (n a : ℕ) :
    wordSum n (stationaryNumerator μ a) = residual μ a := by
  induction n generalizing a with
  | zero => simp [stationaryNumerator]
  | succ n ih =>
    rw [wordSum_step]
    change wordSum n (stationaryNumerator μ (a+1)) +
      wordSum n (fun x => tail μ a * ordinary μ 0 x) = _
    rw [wordSum_mul, ih, ordinary_normalized, tail_zero, mul_one]
    exact (residual_step μ a).symm

lemma blockMass_normalized (μ : Law) (n : ℕ) : wordSum n (blockMass μ) = 1 := by
  unfold blockMass
  simp_rw [div_eq_mul_inv, mul_comm _ (mean μ)⁻¹]
  rw [wordSum_mul, stationaryNumerator_normalized, residual_zero,
    inv_mul_cancel₀ (ne_of_gt (mean_pos μ))]

lemma ordinary_zeros (μ : Law) (a n : ℕ) :
    ordinary μ a (List.replicate n false) = tail μ (a+n) := by
  induction n generalizing a with
  | zero => simp [ordinary]
  | succ n ih => simpa [ordinary, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (a+1)

lemma stationaryNumerator_zeros (μ : Law) (a n : ℕ) :
    stationaryNumerator μ a (List.replicate n false) = residual μ (a+n) := by
  induction n generalizing a with
  | zero => simp [stationaryNumerator]
  | succ n ih => simpa [stationaryNumerator, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (a+1)

/-- Exact stationary all-zero block probability, source equation (2.3). -/
lemma blockMass_zeros (μ : Law) (n : ℕ) :
    blockMass μ (List.replicate n false) = residual μ n / mean μ := by
  simp [blockMass, stationaryNumerator_zeros]

lemma ordinary_prefix_zeros_one (μ : Law) (a n : ℕ) (x : List Bool) :
    ordinary μ a (List.replicate n false ++ true::x) =
      μ.mass (a+n) * ordinary μ 0 x := by
  induction n generalizing a with
  | zero => simp [ordinary]
  | succ n ih => simpa [ordinary, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (a+1)

lemma stationaryNumerator_prefix_zeros_one (μ : Law) (a n : ℕ) (x : List Bool) :
    stationaryNumerator μ a (List.replicate n false ++ true::x) =
      tail μ (a+n) * ordinary μ 0 x := by
  induction n generalizing a with
  | zero => simp [stationaryNumerator]
  | succ n ih => simpa [stationaryNumerator, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (a+1)

lemma blockMass_first_renewal (μ : Law) (n : ℕ) (x : List Bool) :
    blockMass μ (List.replicate n false ++ true::x) =
      tail μ n / mean μ * ordinary μ 0 x := by
  simp [blockMass, stationaryNumerator_prefix_zeros_one]
  ring

/-- Genuine stationary next-one probability defined by the finite block laws. -/
noncomputable def conditional (μ : Law) (x : List Bool) : ℝ :=
  blockMass μ (x ++ [true]) / blockMass μ x

lemma conditional_zeros (μ : Law) (n : ℕ) :
    conditional μ (List.replicate n false) = tail μ n / residual μ n := by
  unfold conditional
  rw [blockMass_first_renewal, blockMass_zeros]
  simp only [ordinary, tail_zero, mul_one]
  exact div_div_div_cancel_right₀ (ne_of_gt (mean_pos μ)) _ _

lemma stationary_zero_weighted_parameter (μ : Law) (n : ℕ)
    (h : 0 < residual μ n) :
    blockMass μ (List.replicate n false) *
      conditional μ (List.replicate n false) ≤ 1 / (n+1 : ℝ) := by
  rw [blockMass_zeros, conditional_zeros]
  have hm := mean_pos μ
  have hn : 0 < (n+1 : ℝ) := by positivity
  have ht := tail_weight_bound μ n
  have he : residual μ n / mean μ * (tail μ n / residual μ n) =
      tail μ n / mean μ := by field_simp
  rw [he]
  apply (div_le_div_iff₀ hm hn).mpr
  simpa [one_mul, mul_comm] using ht


lemma ordinary_right_consistency (μ : Law) (a : ℕ) (x : List Bool) :
    ordinary μ a x = ordinary μ a (x ++ [false]) + ordinary μ a (x ++ [true]) := by
  induction x generalizing a with
  | nil => simp only [List.nil_append, ordinary, tail_zero, mul_one];
           simpa [add_comm] using tail_step μ a
  | cons b x ih => cases b with
    | false => exact ih (a+1)
    | true => simpa only [List.cons_append, ordinary, mul_add] using
        congrArg (μ.mass a * ·) (ih 0)

lemma stationaryNumerator_right_consistency (μ : Law) (a : ℕ) (x : List Bool) :
    stationaryNumerator μ a x = stationaryNumerator μ a (x ++ [false]) +
      stationaryNumerator μ a (x ++ [true]) := by
  induction x generalizing a with
  | nil => simp only [List.nil_append, stationaryNumerator, ordinary, tail_zero, mul_one];
           exact residual_step μ a
  | cons b x ih => cases b with
    | false => exact ih (a+1)
    | true => simpa only [List.cons_append, stationaryNumerator, mul_add] using
        congrArg (tail μ a * ·) (ordinary_right_consistency μ 0 x)

lemma blockMass_right_consistency (μ : Law) (x : List Bool) :
    blockMass μ x = blockMass μ (x ++ [false]) + blockMass μ (x ++ [true]) := by
  unfold blockMass
  rw [stationaryNumerator_right_consistency, add_div]

lemma stationaryNumerator_shift (μ : Law) (a : ℕ) (x : List Bool) :
    stationaryNumerator μ a x = stationaryNumerator μ (a+1) x + ordinary μ a x := by
  induction x generalizing a with
  | nil => exact residual_step μ a
  | cons b x ih => cases b with
    | false => exact ih (a+1)
    | true => simp only [stationaryNumerator, ordinary, tail_step μ a]; ring

/-- Left marginal consistency is stationarity of the constructed binary block laws. -/
lemma blockMass_left_consistency (μ : Law) (x : List Bool) :
    blockMass μ x = blockMass μ (false::x) + blockMass μ (true::x) := by
  unfold blockMass
  simp only [stationaryNumerator, tail_zero, one_mul]
  rw [stationaryNumerator_shift μ 0, add_div]

lemma conditional_mem_unitInterval (μ : Law) (x : List Bool) :
    0 ≤ conditional μ x ∧ conditional μ x ≤ 1 := by
  constructor
  · exact div_nonneg (blockMass_nonneg μ _) (blockMass_nonneg μ _)
  · unfold conditional
    by_cases h : blockMass μ x = 0
    · simp [h]
    · have hp : 0 < blockMass μ x := lt_of_le_of_ne (blockMass_nonneg μ _) (Ne.symm h)
      apply (div_le_one hp).mpr
      have hc := blockMass_right_consistency μ x
      linarith [blockMass_nonneg μ (x ++ [false])]

/-- Age measured from the most recent renewal, starting with an initial age. -/
def ageFrom (a : ℕ) : List Bool → ℕ
  | [] => a
  | false::x => ageFrom (a+1) x
  | true::x => ageFrom 0 x

lemma ordinary_hazard_cross (μ : Law) (a : ℕ) (x : List Bool) :
    ordinary μ a (x ++ [true]) * tail μ (ageFrom a x) =
      ordinary μ a x * μ.mass (ageFrom a x) := by
  induction x generalizing a with
  | nil => simp [ordinary, ageFrom, mul_comm]
  | cons b x ih => cases b with
    | false => exact ih (a+1)
    | true => simpa only [List.cons_append, ordinary, ageFrom, mul_assoc] using
        congrArg (μ.mass a * ·) (ih 0)

lemma ordinary_positive_terminal_tail (μ : Law) (a : ℕ) (x : List Bool)
    (h : 0 < ordinary μ a x) : 0 < tail μ (ageFrom a x) := by
  induction x generalizing a with
  | nil => exact h
  | cons b x ih => cases b with
    | false => exact ih (a+1) h
    | true =>
      apply ih 0
      change 0 < μ.mass a * ordinary μ 0 x at h
      exact pos_of_mul_pos_right h (μ.nonneg a)

lemma stationaryNumerator_hazard_cross (μ : Law) (a : ℕ) (x : List Bool)
    (hseen : true ∈ x) :
    stationaryNumerator μ a (x ++ [true]) * tail μ (ageFrom a x) =
      stationaryNumerator μ a x * μ.mass (ageFrom a x) := by
  induction x generalizing a with
  | nil => simp at hseen
  | cons b x ih => cases b with
    | false => exact ih (a+1) (by simpa using hseen)
    | true => simpa only [List.cons_append, stationaryNumerator, ageFrom, mul_assoc] using
        congrArg (tail μ a * ·) (ordinary_hazard_cross μ 0 x)

lemma stationary_positive_terminal_tail (μ : Law) (a : ℕ) (x : List Bool)
    (hseen : true ∈ x) (h : 0 < stationaryNumerator μ a x) :
    0 < tail μ (ageFrom a x) := by
  induction x generalizing a with
  | nil => simp at hseen
  | cons b x ih => cases b with
    | false => exact ih (a+1) (by simpa using hseen) h
    | true =>
      apply ordinary_positive_terminal_tail μ 0 x
      change 0 < tail μ a * ordinary μ 0 x at h
      exact pos_of_mul_pos_right h (tail_nonneg μ a)

/-- Source equation (2.4) on every positive history containing a renewal. -/
lemma conditional_visible_renewal (μ : Law) (x : List Bool)
    (hseen : true ∈ x) (hp : 0 < blockMass μ x) :
    conditional μ x = μ.mass (ageFrom 0 x) / tail μ (ageFrom 0 x) := by
  have hm := mean_pos μ
  have hn : 0 < stationaryNumerator μ 0 x := (div_pos_iff_of_pos_right hm).mp hp
  have ht := stationary_positive_terminal_tail μ 0 x hseen hn
  have hc := stationaryNumerator_hazard_cross μ 0 x hseen
  unfold conditional blockMass
  rw [div_div_div_cancel_right₀ (ne_of_gt hm)]
  exact (div_eq_div_iff (ne_of_gt hn) (ne_of_gt ht)).2 (by simpa [mul_comm] using hc)

end Paper37.Renewal

