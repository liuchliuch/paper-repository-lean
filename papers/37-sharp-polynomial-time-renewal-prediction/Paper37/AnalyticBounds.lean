import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact elementary inequalities used in P37, Appendices D, E and G.
The occupancy quantity below uses the paper's positive integer gap index. -/
namespace Paper37.AnalyticBounds

open scoped BigOperators
open intervalIntegral

noncomputable def partitionConstant : ℝ := Real.pi * Real.sqrt (2 / 3)

noncomputable def redundancyBound (N : ℕ) : ℝ :=
  partitionConstant * Real.sqrt N + Real.log (N + 1) +
    Real.log (1 + 2 * Real.sqrt N / partitionConstant)

theorem partitionConstant_gt_two : 2 < partitionConstant := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 / 3 by norm_num)
  have hp := Real.pi_gt_three
  have hsp := Real.sqrt_nonneg (2 / 3 : ℝ)
  have hs' : (2:ℝ) / 3 < Real.sqrt (2 / 3) := by nlinarith
  dsimp [partitionConstant]
  nlinarith

theorem partitionConstant_pos : 0 < partitionConstant :=
  lt_trans (by norm_num) partitionConstant_gt_two

/-- The scalar logarithmic estimate used to obtain the explicit constant in (2.9). -/
theorem log_add_two_le_sqrt_two_mul {x : ℝ} (hx : 1 ≤ x) :
    Real.log (x + 2) ≤ Real.sqrt (2 * x) := by
  apply (Real.log_le_iff_le_exp (by linarith : 0 < x + 2)).2
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * x by linarith)
  have hroot : 1 ≤ Real.sqrt (2 * x) := by
    apply (Real.le_sqrt (by norm_num) (by linarith)).2
    nlinarith
  have hexp := Real.quadratic_le_exp_of_nonneg (Real.sqrt_nonneg (2 * x))
  nlinarith

/-- The normalizer logarithm is bounded by the simpler logarithm, for every positive horizon. -/
theorem normalizer_argument_le {N : ℕ} (hN : 1 ≤ N) :
    1 + 2 * Real.sqrt (N : ℝ) / partitionConstant ≤ (N : ℝ) + 1 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≤ N := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith
  have hc := partitionConstant_gt_two.le
  rw [add_comm (N : ℝ) 1]
  apply (add_le_add_iff_left 1).2
  apply (div_le_iff₀ partitionConstant_pos).2
  nlinarith

theorem redundancyBound_le {N : ℕ} (hN : 1 ≤ N) :
    redundancyBound N ≤ partitionConstant * Real.sqrt N + 2 * Real.log (N + 1) := by
  have hn := normalizer_argument_le hN
  have hcp := partitionConstant_pos
  have hp : 0 < 1 + 2 * Real.sqrt (N : ℝ) / partitionConstant := by positivity
  have hl := Real.log_le_log hp hn
  dsimp [redundancyBound]
  linarith

/-- Square-root contribution to the explicit constant in (2.9). -/
theorem partitionConstant_mul_sqrt_two :
    partitionConstant * Real.sqrt 2 = 2 * Real.pi / Real.sqrt 3 := by
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h3p : (0:ℝ) < Real.sqrt 3 := by positivity
  dsimp [partitionConstant]
  rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 2)]
  field_simp
  nlinarith

/-- The final explicit scalar inequality of Theorem 2.2, with no probabilistic premises. -/
theorem fixed_time_explicit_constant {n : ℕ} (hn : 1 ≤ n) :
    (redundancyBound (n + 1) + Real.log (n + 2)) / n ≤
      (2 * Real.pi / Real.sqrt 3 + 3 * Real.sqrt 2) / Real.sqrt n := by
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0:ℝ) < n := by linarith
  have hsnp : (0:ℝ) < Real.sqrt n := by positivity
  have hsq := Real.sq_sqrt (show (0:ℝ) ≤ n by positivity)
  have hs1 : Real.sqrt ((n:ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt n := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.sqrt_le_sqrt
    linarith
  have hl := log_add_two_le_sqrt_two_mul hnr
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)] at hl
  have hb := redundancyBound_le (show 1 ≤ n + 1 by omega)
  have hcast : ((n + 1 : ℕ) : ℝ) = (n:ℝ) + 1 := by norm_cast
  have hcast' : ((n + 1 : ℕ) : ℝ) + 1 = (n:ℝ) + 2 := by push_cast; ring
  rw [hcast, show (n:ℝ) + 1 + 1 = (n:ℝ) + 2 by ring] at hb
  have hm := mul_le_mul_of_nonneg_left hs1 partitionConstant_pos.le
  rw [← mul_assoc, partitionConstant_mul_sqrt_two] at hm
  have hnum : redundancyBound (n+1) + Real.log ((n:ℝ)+2) ≤
      (2 * Real.pi / Real.sqrt 3 + 3 * Real.sqrt 2) * Real.sqrt n := by
    nlinarith
  apply (div_le_iff₀ hnp).2
  calc
    redundancyBound (n + 1) + Real.log ((n:ℝ) + 2) ≤
        (2 * Real.pi / Real.sqrt 3 + 3 * Real.sqrt 2) * Real.sqrt n := hnum
    _ = (2 * Real.pi / Real.sqrt 3 + 3 * Real.sqrt 2) / Real.sqrt n * n := by
      field_simp
      nlinarith

/-- Number of candidate positive count vectors with at most `s` occupied coordinates.
This is the combinatorial expression on the right of the first inequality in (E.2). -/
def restrictedCountBound (L s : ℕ) : ℕ :=
  1 + ∑ j ∈ Finset.Icc 1 (min s L), L.choose j * L ^ j

/-- The polynomial bound in the second inequality of (E.2). -/
theorem restrictedCountBound_le (L s : ℕ) :
    restrictedCountBound L s ≤ (L + 1) ^ (2 * s + 1) := by
  let t := min s L
  have hsum : restrictedCountBound L s =
      ∑ j ∈ Finset.range (t+1), L.choose j * L^j := by
    rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < t+1)]
    simp only [Nat.choose_zero_right, pow_zero, mul_one]
    congr 1
  rw [hsum]
  calc
    ∑ j ∈ Finset.range (t+1), L.choose j * L^j ≤
        ∑ _j ∈ Finset.range (t+1), (L+1)^(2*t) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjt : j ≤ t := by have := Finset.mem_range.mp hj; omega
      calc
        L.choose j * L^j ≤ L^j * L^j := Nat.mul_le_mul_right _ (Nat.choose_le_pow L j)
        _ = L^(2*j) := by rw [two_mul, pow_add]
        _ ≤ (L+1)^(2*j) := Nat.pow_le_pow_left (by omega) _
        _ ≤ (L+1)^(2*t) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = (t+1) * (L+1)^(2*t) := by simp
    _ ≤ (L+1) * (L+1)^(2*t) := by
      apply Nat.mul_le_mul_right
      dsimp [t]
      omega
    _ = (L+1)^(2*t+1) := by rw [pow_succ]; ring
    _ ≤ (L+1)^(2*s+1) := by
      apply Nat.pow_le_pow_right (by omega)
      dsimp [t]
      omega

/-- The stationary occupied-gap complexity (E.10), using positive gap lengths. -/
noncomputable def occupiedComplexity (N : ℕ) (μ : ℕ → ℝ) (m : ℝ) : ℝ :=
  ∑ d ∈ Finset.Ico 1 N, min 1 (((N-d : ℕ) : ℝ) * μ d / m)

theorem occupiedComplexity_nonneg (N : ℕ) {μ : ℕ → ℝ} {m : ℝ}
    (hμ : ∀ d, 0 ≤ μ d) (hm : 0 ≤ m) :
    0 ≤ occupiedComplexity N μ m := by
  apply Finset.sum_nonneg
  intro d hd
  apply le_min (by norm_num)
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hμ d)) hm

theorem occupiedComplexity_le_horizon (N : ℕ) (μ : ℕ → ℝ) (m : ℝ) :
    occupiedComplexity N μ m ≤ (N-1 : ℕ) := by
  calc
    occupiedComplexity N μ m ≤ ∑ _d ∈ Finset.Ico 1 N, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact min_le_left _ _
    _ = (N-1 : ℕ) := by simp

/-- A law supported on a finite set has occupied complexity at most that set's size. -/
theorem occupiedComplexity_le_support (N : ℕ) (μ : ℕ → ℝ) (m : ℝ)
    (S : Finset ℕ) (hS : ∀ d, d ∉ S → μ d = 0) :
    occupiedComplexity N μ m ≤ S.card := by
  calc
    occupiedComplexity N μ m ≤
        ∑ d ∈ Finset.Ico 1 N, if d ∈ S then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs with h
      · exact min_le_left _ _
      · simp [hS d h]
    _ = ((Finset.Ico 1 N ∩ S).card : ℝ) := by simp
    _ ≤ S.card := by exact_mod_cast Finset.card_le_card Finset.inter_subset_right

/-- The renewal-weighted complexity is bounded by the ordinary occupancy sum;
this is the finite version of the first estimate in the proof of Corollary E.5. -/
theorem occupiedComplexity_le_ordinary (N : ℕ) {μ : ℕ → ℝ} {m : ℝ}
    (hμ : ∀ d, 0 ≤ μ d) (hm : 1 ≤ m) :
    occupiedComplexity N μ m ≤
      ∑ d ∈ Finset.Ico 1 N, min 1 ((N:ℝ) * μ d) := by
  apply Finset.sum_le_sum
  intro d hd
  apply min_le_min_left
  apply (div_le_iff₀ (by linarith : 0 < m)).2
  have hNd : ((N-d : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N d
  have hpos : 0 ≤ (N:ℝ) * μ d := mul_nonneg (Nat.cast_nonneg _) (hμ d)
  calc
    ((N-d : ℕ) : ℝ) * μ d ≤ (N:ℝ) * μ d := mul_le_mul_of_nonneg_right hNd (hμ d)
    _ ≤ (N:ℝ) * μ d * m := le_mul_of_one_le_right hpos hm

/-- Finite probability-space form of the occupancy bound (E.12).
The count moment is supplied by stationary renewal intensity; the proof here
establishes the full indicator/Markov and summation step. -/
theorem expectedDistinct_le_complexity {Ω : Type*} [Fintype Ω]
    (N : ℕ) (w : Ω → ℝ) (C : Ω → ℕ → ℕ) (μ : ℕ → ℝ) (m : ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hmean : ∀ d ∈ Finset.Ico 1 N,
      ∑ ω, w ω * (C ω d : ℝ) = ((N-d : ℕ) : ℝ) * μ d / m) :
    (∑ ω, w ω * (∑ d ∈ Finset.Ico 1 N, if 0 < C ω d then (1:ℝ) else 0)) ≤
      occupiedComplexity N μ m := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro d hd
  apply le_min
  · calc
      ∑ ω, w ω * (if 0 < C ω d then (1:ℝ) else 0) ≤ ∑ ω, w ω := by
        apply Finset.sum_le_sum
        intro ω hω
        split_ifs <;> simp [hw ω]
      _ = 1 := hwsum
  · rw [← hmean d hd]
    apply Finset.sum_le_sum
    intro ω hω
    apply mul_le_mul_of_nonneg_left _ (hw ω)
    split_ifs with h
    · exact_mod_cast (show 1 ≤ C ω d by omega)
    · positivity

-- Additional exact Appendix G estimates, to append after first diagnostic pass.
theorem sqrt_two_natPow (j : ℕ) :
    Real.sqrt ((2^j : ℕ) : ℝ) = (Real.sqrt 2)^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Nat.cast_mul, Real.sqrt_mul (by positivity), ih, pow_succ]
    norm_num

theorem sum_sqrt_two_pow (J : ℕ) :
    (∑ j ∈ Finset.range (J+1), (Real.sqrt 2)^j) ≤
      (2 + Real.sqrt 2) * (Real.sqrt 2)^J := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hr := Real.sqrt_nonneg (2:ℝ)
  induction J with
  | zero => simp; nlinarith
  | succ J ih =>
    rw [Finset.sum_range_succ]
    calc
      (∑ j ∈ Finset.range (J+1), (Real.sqrt 2)^j) + (Real.sqrt 2)^(J+1) ≤
          (2 + Real.sqrt 2)*(Real.sqrt 2)^J + (Real.sqrt 2)^(J+1) :=
        add_le_add_right ih _
      _ = ((2 + Real.sqrt 2) + Real.sqrt 2) * (Real.sqrt 2)^J := by rw [pow_succ]; ring
      _ = (2 + Real.sqrt 2) * (Real.sqrt 2)^(J+1) := by
        have heq : (2 + Real.sqrt 2) + Real.sqrt 2 = (2 + Real.sqrt 2)*Real.sqrt 2 := by
          nlinarith
        rw [heq, pow_succ]
        ring

/-- The dyadic geometric estimate used for the leading term in (G.2). -/
theorem dyadic_sqrt_sum_le {J N : ℕ} (hJN : 2^J ≤ N) :
    (∑ j ∈ Finset.range (J+1), Real.sqrt ((2^j : ℕ) : ℝ)) ≤
      (2 + Real.sqrt 2) * Real.sqrt N := by
  simp_rw [sqrt_two_natPow]
  calc
    (∑ j ∈ Finset.range (J+1), (Real.sqrt 2)^j) ≤
        (2 + Real.sqrt 2) * (Real.sqrt 2)^J := sum_sqrt_two_pow J
    _ ≤ (2 + Real.sqrt 2) * Real.sqrt N := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← sqrt_two_natPow]
      apply Real.sqrt_le_sqrt
      exact_mod_cast hJN

theorem log_two_pow_add_one_le (j : ℕ) :
    Real.log ((2:ℝ)^j + 1) ≤ ((j:ℝ)+1) * Real.log 2 := by
  have hp : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  calc
    Real.log ((2:ℝ)^j + 1) ≤ Real.log ((2:ℝ)^(j+1)) := by
      apply Real.log_le_log (by positivity)
      rw [pow_succ]
      linarith
    _ = ((j:ℝ)+1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring


theorem sum_real_succ (J : ℕ) :
    (∑ j ∈ Finset.range (J+1), ((j:ℝ)+1)) = ((J:ℝ)+1)*((J:ℝ)+2)/2 := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem dyadic_log_sum_le (J : ℕ) :
    (∑ j ∈ Finset.range (J+1), Real.log (((2^j:ℕ):ℝ)+1)) ≤
      (Real.log 2 / 2) * ((J:ℝ)+1) * ((J:ℝ)+2) := by
  calc
    (∑ j ∈ Finset.range (J+1), Real.log (((2^j:ℕ):ℝ)+1)) ≤
        ∑ j ∈ Finset.range (J+1), ((j:ℝ)+1) * Real.log 2 := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using log_two_pow_add_one_le j
    _ = (Real.log 2 / 2) * ((J:ℝ)+1) * ((J:ℝ)+2) := by
      rw [← Finset.sum_mul, sum_real_succ]
      ring

/-- The complete deterministic sum estimate in the second inequality of (G.2),
for any dyadic cutoff whose final epoch starts before the observation horizon. -/
theorem dyadic_redundancy_sum_le {J N : ℕ} (hJN : 2^J ≤ N) :
    (∑ j ∈ Finset.range (J+1),
      (redundancyBound (2^j) + Real.log (((2^j:ℕ):ℝ)+1))) ≤
      partitionConstant * (2 + Real.sqrt 2) * Real.sqrt N +
        (3 * Real.log 2 / 2) * ((J:ℝ)+1) * ((J:ℝ)+2) := by
  have hs := dyadic_sqrt_sum_le hJN
  have hl := dyadic_log_sum_le J
  calc
    (∑ j ∈ Finset.range (J+1),
      (redundancyBound (2^j) + Real.log (((2^j:ℕ):ℝ)+1))) ≤
        ∑ j ∈ Finset.range (J+1),
          (partitionConstant * Real.sqrt ((2^j:ℕ):ℝ) +
            3 * Real.log (((2^j:ℕ):ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hb := redundancyBound_le (show 1 ≤ 2^j by exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero j (by norm_num)))
      linarith
    _ = partitionConstant *
          (∑ j ∈ Finset.range (J+1), Real.sqrt ((2^j:ℕ):ℝ)) +
        3 * (∑ j ∈ Finset.range (J+1), Real.log (((2^j:ℕ):ℝ)+1)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ partitionConstant * ((2 + Real.sqrt 2) * Real.sqrt N) +
        3 * ((Real.log 2 / 2) * ((J:ℝ)+1) * ((J:ℝ)+2)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hs partitionConstant_pos.le)
        (mul_le_mul_of_nonneg_left hl (by norm_num))
    _ = _ := by ring


/-- Splitting the stationary occupancy sum at an arbitrary positive-gap cutoff. -/
theorem occupiedComplexity_le_cutoff (N K : ℕ) {μ : ℕ → ℝ} {m : ℝ}
    (hμ : ∀ d, 0 ≤ μ d) (hm : 1 ≤ m) :
    occupiedComplexity N μ m ≤
      (K:ℝ) + (N:ℝ) * ∑ d ∈ Finset.Ico (K+1) N, μ d := by
  by_cases hKN : K+1 ≤ N
  · calc
      occupiedComplexity N μ m ≤
          ∑ d ∈ Finset.Ico 1 N, min 1 ((N:ℝ) * μ d) := occupiedComplexity_le_ordinary N hμ hm
      _ = (∑ d ∈ Finset.Ico 1 (K+1), min 1 ((N:ℝ) * μ d)) +
          ∑ d ∈ Finset.Ico (K+1) N, min 1 ((N:ℝ) * μ d) := by
        exact (Finset.sum_Ico_consecutive _ (by omega) hKN).symm
      _ ≤ (∑ _d ∈ Finset.Ico 1 (K+1), (1:ℝ)) +
          ∑ d ∈ Finset.Ico (K+1) N, (N:ℝ) * μ d := by
        apply add_le_add <;> apply Finset.sum_le_sum
        · intro d hd; exact min_le_left _ _
        · intro d hd; exact min_le_right _ _
      _ = (K:ℝ) + (N:ℝ) * ∑ d ∈ Finset.Ico (K+1) N, μ d := by
        rw [Finset.mul_sum]
        simp
  · have hcard := occupiedComplexity_le_horizon N μ m
    have hNK : ((N-1:ℕ):ℝ) ≤ K := by exact_mod_cast (show N-1 ≤ K by omega)
    have hempty : Finset.Ico (K+1) N = ∅ := Finset.Ico_eq_empty (by omega)
    simp only [hempty, Finset.sum_empty, mul_zero, add_zero]
    exact hcard.trans hNK

/-- An explicit exponential-tail occupancy bound. Choosing a logarithmic cutoff
in this estimate is the scalar occupancy step in Corollary E.5(2). -/
theorem occupiedComplexity_le_geometric (N K : ℕ) {μ : ℕ → ℝ} {m C r : ℝ}
    (hμ : ∀ d, 0 ≤ μ d) (hm : 1 ≤ m) (hC : 0 ≤ C)
    (hr : 0 ≤ r) (hr1 : r < 1) (htail : ∀ d, 1 ≤ d → μ d ≤ C * r^d) :
    occupiedComplexity N μ m ≤ (K:ℝ) + (N:ℝ) * C * r^(K+1) / (1-r) := by
  calc
    occupiedComplexity N μ m ≤
        (K:ℝ) + (N:ℝ) * ∑ d ∈ Finset.Ico (K+1) N, μ d :=
      occupiedComplexity_le_cutoff N K hμ hm
    _ ≤ (K:ℝ) + (N:ℝ) * ∑ d ∈ Finset.Ico (K+1) N, C * r^d := by
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro d hd
      exact htail d (by have := (Finset.mem_Ico.mp hd).1; omega)
    _ = (K:ℝ) + (N:ℝ) * C * ∑ d ∈ Finset.Ico (K+1) N, r^d := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (K:ℝ) + (N:ℝ) * C * (r^(K+1) / (1-r)) := by
      apply add_le_add_left
      exact mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr hr1)
        (mul_nonneg (Nat.cast_nonneg _) hC)
    _ = _ := by ring


/-- Explicit logarithmic stationary occupancy bound for an exponential gap tail.
No asymptotic or choice of an unknown cutoff remains in the conclusion. -/
theorem occupiedComplexity_le_exponential (N : ℕ) {μ : ℕ → ℝ} {m C c : ℝ}
    (hN : 1 ≤ N) (hμ : ∀ d, 0 ≤ μ d) (hm : 1 ≤ m)
    (hC : 0 ≤ C) (hc : 0 < c)
    (htail : ∀ d, 1 ≤ d → μ d ≤ C * Real.exp (-c * d)) :
    occupiedComplexity N μ m ≤ Real.log (N:ℝ) / c + 1 + C / (1 - Real.exp (-c)) := by
  let K := Nat.ceil (Real.log (N:ℝ) / c)
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hNr
  have hq : 0 ≤ Real.log (N:ℝ) / c := div_nonneg hlog hc.le
  have hKlo : Real.log (N:ℝ) / c ≤ (K:ℝ) := Nat.le_ceil _
  have hKhi : (K:ℝ) < Real.log (N:ℝ) / c + 1 := Nat.ceil_lt_add_one hq
  have hr : 0 ≤ Real.exp (-c) := Real.exp_nonneg _
  have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ht : ∀ d, 1 ≤ d → μ d ≤ C * Real.exp (-c)^d := by
    intro d hd
    convert htail d hd using 2
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hb := occupiedComplexity_le_geometric N K hμ hm hC hr hr1 ht
  have hp : Real.exp (-c)^(K+1) ≤ 1/(N:ℝ) := by
    rw [← Real.exp_nat_mul]
    have hlogK : Real.log (N:ℝ) ≤ (K:ℝ) * c := (div_le_iff₀ hc).mp hKlo
    have hex : ((K+1:ℕ):ℝ) * (-c) ≤ - Real.log (N:ℝ) := by push_cast; nlinarith
    calc
      Real.exp (((K+1:ℕ):ℝ)*(-c)) ≤ Real.exp (- Real.log (N:ℝ)) := Real.exp_le_exp.mpr hex
      _ = 1/(N:ℝ) := by rw [Real.exp_neg, Real.exp_log hNp, one_div]
  have hNp' : (N:ℝ) * Real.exp (-c)^(K+1) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hp hNp.le
    simpa [hNp.ne'] using this
  have hlast : (N:ℝ) * C * Real.exp (-c)^(K+1) / (1 - Real.exp (-c)) ≤
      C / (1 - Real.exp (-c)) := by
    apply (div_le_div_iff_of_pos_right (sub_pos.mpr hr1)).2
    nlinarith [mul_le_mul_of_nonneg_left hNp' hC]
  linarith


/-- Integral comparison for a power-law tail on positive integers. -/
theorem sum_power_tail_le (N K : ℕ) (hK : 1 ≤ K) {α : ℝ} (hα : 1 < α) :
    (∑ d ∈ Finset.Ico (K+1) N, (d:ℝ)^(-α)) ≤ (K:ℝ)^(1-α)/(α-1) := by
  have hKp : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  by_cases hKN : K < N
  · have hKN' : K ≤ N-1 := by omega
    have hf : AntitoneOn (fun x : ℝ => x^(-α)) (Set.Icc (K:ℝ) ((N-1:ℕ):ℝ)) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (hKp.trans_le hx.1) hxy (by linarith)
    have hi := hf.sum_le_integral_Ico hKN'
    have hsum : (∑ i ∈ Finset.Ico K (N-1), ((i+1:ℕ):ℝ)^(-α)) =
        ∑ d ∈ Finset.Ico (K+1) N, (d:ℝ)^(-α) := by
      have heN : N-1+1 = N := by omega
      simpa only [heN] using Finset.sum_Ico_add' (fun d : ℕ => (d:ℝ)^(-α)) K (N-1) 1
    rw [hsum] at hi
    have hlow : (0:ℝ) < (N-1:ℕ) := hKp.trans_le (by exact_mod_cast hKN')
    have hzero : (0:ℝ) ∉ Set.uIcc (K:ℝ) ((N-1:ℕ):ℝ) := by
      rw [Set.uIcc_of_le (by exact_mod_cast hKN')]
      simp only [Set.mem_Icc, not_and]
      intro h
      linarith
    have hint : (∫ x in (K:ℝ)..((N-1:ℕ):ℝ), x^(-α)) =
        ((K:ℝ)^(1-α) - ((N-1:ℕ):ℝ)^(1-α))/(α-1) := by
      rw [integral_rpow (Or.inr ⟨by linarith, hzero⟩)]
      have he : -α+1 = 1-α := by ring
      rw [he]
      field_simp [show α-1 ≠ 0 by linarith, show 1-α ≠ 0 by linarith]
      ring
    rw [hint] at hi
    exact hi.trans (div_le_div_of_nonneg_right (by linarith [Real.rpow_nonneg (le_of_lt hlow) (1-α)]) (by linarith))
  · have hempty : Finset.Ico (K+1) N = ∅ := Finset.Ico_eq_empty (by omega)
    simp only [hempty, Finset.sum_empty]
    exact div_nonneg (Real.rpow_nonneg hKp.le _) (by linarith)

/-- Explicit cutoff bound for a power-law gap mass. -/
theorem occupiedComplexity_le_power_cutoff (N K : ℕ) {μ : ℕ → ℝ} {m C α : ℝ}
    (hK : 1 ≤ K) (hμ : ∀ d, 0 ≤ μ d) (hm : 1 ≤ m) (hC : 0 ≤ C)
    (hα : 1 < α) (htail : ∀ d, 1 ≤ d → μ d ≤ C * (d:ℝ)^(-α)) :
    occupiedComplexity N μ m ≤ (K:ℝ) + (N:ℝ) * C * (K:ℝ)^(1-α)/(α-1) := by
  calc
    occupiedComplexity N μ m ≤
        (K:ℝ) + (N:ℝ) * ∑ d ∈ Finset.Ico (K+1) N, μ d :=
      occupiedComplexity_le_cutoff N K hμ hm
    _ ≤ (K:ℝ) + (N:ℝ) * ∑ d ∈ Finset.Ico (K+1) N, C * (d:ℝ)^(-α) := by
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro d hd
      exact htail d (by have := (Finset.mem_Ico.mp hd).1; omega)
    _ = (K:ℝ) + (N:ℝ) * C * ∑ d ∈ Finset.Ico (K+1) N, (d:ℝ)^(-α) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (K:ℝ) + (N:ℝ) * C * ((K:ℝ)^(1-α)/(α-1)) := by
      apply add_le_add_left
      exact mul_le_mul_of_nonneg_left (sum_power_tail_le N K hK hα)
        (mul_nonneg (Nat.cast_nonneg _) hC)
    _ = _ := by ring

/-- Explicit polynomial stationary occupancy bound for power-law gap tails.
It implies the occupancy growth asserted in Corollary E.5(3). -/
theorem occupiedComplexity_le_power (N : ℕ) {μ : ℕ → ℝ} {m C α : ℝ}
    (hN : 1 ≤ N) (hμ : ∀ d, 0 ≤ μ d) (hm : 1 ≤ m) (hC : 0 ≤ C)
    (hα : 1 < α) (htail : ∀ d, 1 ≤ d → μ d ≤ C * (d:ℝ)^(-α)) :
    occupiedComplexity N μ m ≤ (1 + C/(α-1)) * ((N:ℝ)^(1/α)+1) := by
  let u := (N:ℝ)^(1/α)
  let K := Nat.ceil u
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith
  have hup : 0 < u := Real.rpow_pos_of_pos hNp _
  have hu1 : 1 ≤ u := Real.one_le_rpow hNr (by positivity)
  have hKlo : u ≤ (K:ℝ) := Nat.le_ceil _
  have hKhi : (K:ℝ) < u+1 := Nat.ceil_lt_add_one hup.le
  have hK : 1 ≤ K := by exact_mod_cast (hu1.trans hKlo)
  have hKp : (0:ℝ) < K := hup.trans_le hKlo
  have hp : (K:ℝ)^(-α) ≤ 1/(N:ℝ) := by
    calc
      (K:ℝ)^(-α) ≤ u^(-α) := Real.rpow_le_rpow_of_nonpos hup hKlo (by linarith)
      _ = (N:ℝ)^(-1:ℝ) := by
        dsimp [u]
        rw [← Real.rpow_mul hNp.le]
        congr 1
        field_simp
      _ = 1/(N:ℝ) := by rw [Real.rpow_neg_one, one_div]
  have hprod : (N:ℝ) * (K:ℝ)^(-α) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hp hNp.le
    simpa [hNp.ne'] using this
  have hpow : (K:ℝ)^(1-α) = (K:ℝ) * (K:ℝ)^(-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hKp, Real.rpow_one]
  have hb := occupiedComplexity_le_power_cutoff N K hK hμ hm hC hα htail
  have hterm : (N:ℝ) * C * (K:ℝ)^(1-α)/(α-1) ≤ C*(K:ℝ)/(α-1) := by
    apply (div_le_div_iff_of_pos_right (by linarith : 0 < α-1)).2
    rw [hpow]
    have hCK : 0 ≤ C*(K:ℝ) := mul_nonneg hC hKp.le
    nlinarith [mul_le_mul_of_nonneg_left hprod hCK]
  calc
    occupiedComplexity N μ m ≤ (K:ℝ) + C*(K:ℝ)/(α-1) := by linarith
    _ = (1+C/(α-1))*(K:ℝ) := by ring
    _ ≤ (1+C/(α-1))*(u+1) := by
      apply mul_le_mul_of_nonneg_left hKhi.le
      have : 0 ≤ C/(α-1) := div_nonneg hC (by linarith)
      linarith


/-- The oracle branch may be bounded pointwise by a linear function of the
observed number of gap types. This also supplies the last simplification in
(E.13) without a separate concavity argument. -/
theorem adaptiveBranch_le_linear {N V : ℕ} (hN : 1 ≤ N) (hV : V ≤ N-1) :
    (2*((max 1 V : ℕ):ℝ)+2) * Real.log ((N:ℝ)+1) +
      2 * Real.log (((max 1 V : ℕ):ℝ)+1) ≤
        (2*(V:ℝ)+6) * Real.log ((N:ℝ)+1) := by
  have hκN : max 1 V ≤ N := by omega
  have hκV : max 1 V ≤ V+1 := by omega
  have hκNr : ((max 1 V : ℕ):ℝ) ≤ N := by exact_mod_cast hκN
  have hκVr : ((max 1 V : ℕ):ℝ) ≤ (V:ℝ)+1 := by exact_mod_cast hκV
  have hL : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hlog : Real.log (((max 1 V : ℕ):ℝ)+1) ≤ Real.log ((N:ℝ)+1) := by
    apply Real.log_le_log (by positivity)
    linarith
  have hm := mul_le_mul_of_nonneg_right hκVr hL
  nlinarith

/-- Finite-distribution averaging of the adaptive pointwise oracle branch.
The input `hv` is the independently proved expected occupied-type bound. -/
theorem expectedOracle_le {Ω : Type*} [Fintype Ω] {N : ℕ} (hN : 1 ≤ N)
    (w : Ω → ℝ) (V : Ω → ℕ) (v : ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hV : ∀ ω, V ω ≤ N-1) (hv : ∑ ω, w ω * (V ω:ℝ) ≤ v) :
    (∑ ω, w ω * min (redundancyBound N)
      ((2*((max 1 (V ω) : ℕ):ℝ)+2) * Real.log ((N:ℝ)+1) +
        2 * Real.log (((max 1 (V ω) : ℕ):ℝ)+1))) ≤
      min (redundancyBound N) ((2*v+6)*Real.log ((N:ℝ)+1)) := by
  apply le_min
  · calc
      (∑ ω, w ω * min (redundancyBound N)
        ((2*((max 1 (V ω) : ℕ):ℝ)+2) * Real.log ((N:ℝ)+1) +
          2 * Real.log (((max 1 (V ω) : ℕ):ℝ)+1))) ≤
          ∑ ω, w ω * redundancyBound N := by
        apply Finset.sum_le_sum
        intro ω hω
        exact mul_le_mul_of_nonneg_left (min_le_left _ _) (hw ω)
      _ = redundancyBound N := by rw [← Finset.sum_mul, hwsum, one_mul]
  · calc
      (∑ ω, w ω * min (redundancyBound N)
        ((2*((max 1 (V ω) : ℕ):ℝ)+2) * Real.log ((N:ℝ)+1) +
          2 * Real.log (((max 1 (V ω) : ℕ):ℝ)+1))) ≤
          ∑ ω, w ω * ((2*(V ω:ℝ)+6)*Real.log ((N:ℝ)+1)) := by
        apply Finset.sum_le_sum
        intro ω hω
        apply mul_le_mul_of_nonneg_left _ (hw ω)
        exact (min_le_right _ _).trans (adaptiveBranch_le_linear hN (hV ω))
      _ = (2*(∑ ω, w ω*(V ω:ℝ))+6)*Real.log ((N:ℝ)+1) := by
        calc
          (∑ ω, w ω*((2*(V ω:ℝ)+6)*Real.log ((N:ℝ)+1))) =
              ∑ ω, ((2*Real.log ((N:ℝ)+1))*(w ω*(V ω:ℝ)) +
                (6*Real.log ((N:ℝ)+1))*w ω) := by
            apply Finset.sum_congr rfl
            intro ω hω
            ring
          _ = (2*Real.log ((N:ℝ)+1))*(∑ ω, w ω*(V ω:ℝ)) +
              (6*Real.log ((N:ℝ)+1))*(∑ ω, w ω) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          _ = _ := by rw [hwsum]; ring
      _ ≤ (2*v+6)*Real.log ((N:ℝ)+1) := by
        apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith))
        linarith

end Paper37.AnalyticBounds
