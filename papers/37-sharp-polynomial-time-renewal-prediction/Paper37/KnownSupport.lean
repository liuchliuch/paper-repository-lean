import Paper37.Compression
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-! Finite-sample ingredients of source Proposition H.1. -/
noncomputable section
namespace Paper37.KnownSupport
open scoped BigOperators
open Paper37.Compression Paper37.Compression.Distribution

/-- The exact binomial count probabilities used for a single add-one cell. -/
def binomialWeight (k : ℕ) (p : ℝ) (r : ℕ) : ℝ :=
  (k.choose r : ℝ) * p^r * (1-p)^(k-r)

theorem binomialWeight_sum (k : ℕ) (p : ℝ) :
    (∑ r ∈ Finset.range (k+1), binomialWeight k p r) = 1 := by
  calc
    (∑ r ∈ Finset.range (k+1), binomialWeight k p r) =
        ∑ r ∈ Finset.range (k+1), p^r*(1-p)^(k-r)*(k.choose r:ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      unfold binomialWeight
      ring
    _ = (p+(1-p))^k := (add_pow p (1-p) k).symm
    _ = 1 := by simp

lemma choose_div_succ (k r : ℕ) :
    (k.choose r : ℝ)/((r+1:ℕ):ℝ) = ((k+1).choose (r+1):ℝ)/((k+1:ℕ):ℝ) := by
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  have hh := Nat.succ_mul_choose_eq k r
  have hc : ((k+1:ℕ):ℝ)*(k.choose r:ℝ) =
      ((k+1).choose (r+1):ℝ)*((r+1:ℕ):ℝ) := by exact_mod_cast hh
  nlinarith

lemma binomial_reciprocal_term (k r : ℕ) (p : ℝ) :
    p*(binomialWeight k p r/((r+1:ℕ):ℝ)) =
      binomialWeight (k+1) p (r+1)/((k+1:ℕ):ℝ) := by
  unfold binomialWeight
  rw [Nat.add_sub_add_right]
  calc
    p*((k.choose r:ℝ)*p^r*(1-p)^(k-r)/((r+1:ℕ):ℝ)) =
        ((k.choose r:ℝ)/((r+1:ℕ):ℝ))*p^(r+1)*(1-p)^(k-r) := by rw [pow_succ]; ring
    _ = (((k+1).choose (r+1):ℝ)/((k+1:ℕ):ℝ))*p^(r+1)*(1-p)^(k-r) := by rw [choose_div_succ]
    _ = _ := by ring

/-- The binomial inverse-count identity H.4, including the exact correction
for the event that the cell is never observed. -/
theorem binomial_inverse_moment (k : ℕ) {p : ℝ} (hp : 0 < p) :
    (∑ r ∈ Finset.range (k+1), binomialWeight k p r/((r+1:ℕ):ℝ)) =
      (1-(1-p)^(k+1))/(((k+1:ℕ):ℝ)*p) := by
  have hshift : (∑ r ∈ Finset.range (k+1), binomialWeight (k+1) p (r+1)) =
      1-(1-p)^(k+1) := by
    have ht := binomialWeight_sum (k+1) p
    rw [Finset.sum_range_succ'] at ht
    have hz : binomialWeight (k+1) p 0 = (1-p)^(k+1) := by simp [binomialWeight]
    rw [hz] at ht
    linarith
  have hmul : p*(∑ r ∈ Finset.range (k+1), binomialWeight k p r/((r+1:ℕ):ℝ)) =
      (1-(1-p)^(k+1))/((k+1:ℕ):ℝ) := by
    rw [Finset.mul_sum]
    simp_rw [binomial_reciprocal_term]
    rw [← Finset.sum_div, hshift]
  apply (eq_div_iff (mul_ne_zero (by positivity) hp.ne')).2
  have hk : ((k+1:ℕ):ℝ) ≠ 0 := by positivity
  have hh := (eq_div_iff hk).mp hmul
  nlinarith

theorem binomial_inverse_moment_le (k : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ r ∈ Finset.range (k+1), binomialWeight k p r/((r+1:ℕ):ℝ)) ≤
      1/(((k+1:ℕ):ℝ)*p) := by
  rw [binomial_inverse_moment k hp]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh := pow_nonneg (show 0 ≤ 1-p by linarith) (k+1)
  linarith

/-- The deterministic visibility inequality in H.1: all k selected past gaps
are inside the observed window. The selected renewal time is strictly positive. -/
theorem backward_gaps_visible {n B K k : ℕ} (hB : 1 ≤ B) (hnB : B ≤ n)
    (hk : k = n/B-1) (hK : n-B < K) : 0 < (K:ℤ) - k*B := by
  have hdiv : n/B*B ≤ n := Nat.div_mul_le_self n B
  have hdivp : 1 ≤ n/B := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hnB)
  have hprod : B + k*B ≤ n := by
    rw [hk]
    have he : n/B-1+1 = n/B := by omega
    nlinarith
  omega


/-- Every selected backward sample has its left endpoint after observation time
zero, since all k gap lengths are at most the known support bound. -/
theorem backward_sample_start_positive {n B K k : ℕ} (hB : 1 ≤ B) (hnB : B ≤ n)
    (hk : k=n/B-1) (hK : n-B < K) (D : Fin k → ℕ) (hD : ∀ i, D i ≤ B) :
    0 < (K:ℤ) - ∑ i, (D i:ℤ) := by
  have hv := backward_gaps_visible hB hnB hk hK
  have hs : (∑ i, D i) ≤ k*B := by
    calc
      (∑ i, D i) ≤ ∑ _i : Fin k, B := Finset.sum_le_sum (fun i hi => hD i)
      _ = k*B := by simp
  have hs' : (∑ i, (D i:ℤ)) ≤ (k:ℤ)*B := by exact_mod_cast hs
  omega

/-- The numerical comparison chain in source (H.2), retaining its mean factor. -/
theorem support_bound_chain {n B : ℕ} {m : ℝ} (hB : 1 ≤ B) (hBn : 2*B ≤ n) (hm : 1 ≤ m) :
    ((B:ℝ)-1)/(m*(n/B:ℕ)) ≤ (B:ℝ)*((B:ℝ)-1)/(m*((n:ℝ)-B)) ∧
    (B:ℝ)*((B:ℝ)-1)/(m*((n:ℝ)-B)) ≤ 2*(B:ℝ)^2/(m*n) ∧
    2*(B:ℝ)^2/(m*n) ≤ 2*(B:ℝ)^2/n := by
  have hBpos : 0 < B := by omega
  have hBr : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hBnr : 2*(B:ℝ) ≤ n := by exact_mod_cast hBn
  have hnp : (0:ℝ) < n := by nlinarith
  have hmpos : 0 < m := by linarith
  have hsub : 0 < (n:ℝ)-B := by nlinarith
  have hdiv : 1 ≤ n/B := (Nat.le_div_iff_mul_le hBpos).mpr (by omega)
  have hdivpos : (0:ℝ) < (n/B:ℕ) := by exact_mod_cast (show 0 < n/B by omega)
  have hbudget : (n:ℝ)-B ≤ (B:ℝ)*(n/B:ℕ) := by
    have hh := Nat.mod_add_div n B
    have hmod := Nat.mod_lt n hBpos
    have hhr : (n%B:ℕ)+(B:ℝ)*(n/B:ℕ) = n := by exact_mod_cast hh
    have hmodr : (n%B:ℕ) < (B:ℝ) := by exact_mod_cast hmod
    linarith
  constructor
  · apply (div_le_div_iff₀ (mul_pos hmpos hdivpos) (mul_pos hmpos hsub)).2
    have hfac : 0 ≤ m*((B:ℝ)-1) := mul_nonneg hmpos.le (by linarith)
    have hh := mul_le_mul_of_nonneg_left hbudget hfac
    nlinarith
  · constructor
    · calc
        (B:ℝ)*((B:ℝ)-1)/(m*((n:ℝ)-B)) ≤ (B:ℝ)^2/(m*((n:ℝ)-B)) := by
          apply div_le_div_of_nonneg_right _ (mul_nonneg hmpos.le hsub.le)
          nlinarith
        _ ≤ (B:ℝ)^2/(m*(n:ℝ)/2) := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left hBnr hmpos.le]
        _ = 2*(B:ℝ)^2/(m*n) := by ring
    · apply (div_le_div_iff₀ (mul_pos hmpos hnp) hnp).2
      have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*(B:ℝ)^2*n by positivity)
      nlinarith


/-- The actual add-one probability vector on a finite known support. -/
def addOne {α : Type*} [Fintype α] [Nonempty α] (k : ℕ)
    (C : α → ℕ) (hsum : ∑ j, C j = k) : Distribution α where
  mass j := ((C j:ℝ)+1)/((k:ℝ)+Fintype.card α)
  nonneg j := by positivity
  total := by
    rw [← Finset.sum_div]
    have hh : (∑ j, ((C j:ℝ)+1)) = (k:ℝ)+Fintype.card α := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      congr 1
      exact_mod_cast hsum
    rw [hh]
    exact div_self (by positivity)

lemma count_le_sample_size {α : Type*} [Fintype α] (k : ℕ) (C : α → ℕ)
    (hsum : ∑ j, C j = k) (j : α) : C j ≤ k := by
  rw [← hsum]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (C i)) (Finset.mem_univ j)

/-- A cell's binomial count marginal gives the exact inverse-count moment,
independently of any correlations among the other cell counts. -/
theorem inverse_count_of_binomial_marginal {Ω : Type*} [Fintype Ω]
    (w : Distribution Ω) (k : ℕ) (C : Ω → ℕ) (p : ℝ) (hp : 0 < p)
    (hC : ∀ ω, C ω ≤ k)
    (hbin : ∀ r ∈ Finset.range (k+1),
      (∑ ω, if C ω = r then w ω else 0) = binomialWeight k p r) :
    (∑ ω, w ω/((C ω:ℝ)+1)) = (1-(1-p)^(k+1))/(((k:ℝ)+1)*p) := by
  have hh : (∑ ω, w ω/((C ω:ℝ)+1)) =
      ∑ r ∈ Finset.range (k+1), binomialWeight k p r/((r:ℝ)+1) := by
    calc
      (∑ ω, w ω/((C ω:ℝ)+1)) =
          ∑ ω, ∑ r ∈ Finset.range (k+1), if C ω = r then w ω/((r:ℝ)+1) else 0 := by
        apply Finset.sum_congr rfl
        intro ω hω
        symm
        rw [Finset.sum_eq_single (C ω)]
        · simp
        · intro r hr hne
          simp [Ne.symm hne]
        · intro hnot
          exact False.elim (hnot (Finset.mem_range.mpr (by have := hC ω; omega)))
      _ = ∑ r ∈ Finset.range (k+1),
          (∑ ω, if C ω = r then w ω else 0)/((r:ℝ)+1) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro ω hω
        split_ifs <;> simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hbin r hr]
  rw [hh]
  simpa only [Nat.cast_add, Nat.cast_one] using binomial_inverse_moment k hp

/-- The scalar expected log-loss bound for one positive cell of the add-one
estimator. It follows directly from log x ≤ x−1 and the inverse-count moment. -/
lemma expected_addOne_cell_le {Ω : Type*} [Fintype Ω] (w : Distribution Ω)
    (k : ℕ) (C : Ω → ℕ) {p M : ℝ} (hp : 0 < p) (hM : 0 < M)
    (hi : (∑ ω, w ω/((C ω:ℝ)+1)) ≤ 1/(((k:ℝ)+1)*p)) :
    (∑ ω, w ω*(p*(Real.log p-Real.log (((C ω:ℝ)+1)/M)))) ≤
      p*(M/((k:ℝ)+1)-1) := by
  have hk : 0 < (k:ℝ)+1 := by positivity
  have hscalar : ∀ ω, p*(Real.log p-Real.log (((C ω:ℝ)+1)/M)) ≤
      p*(p*M/((C ω:ℝ)+1)-1) := by
    intro ω
    have hCp : 0 < (C ω:ℝ)+1 := by positivity
    have hq : 0 < ((C ω:ℝ)+1)/M := div_pos hCp hM
    have hl := Real.log_le_sub_one_of_pos (div_pos hp hq)
    rw [Real.log_div hp.ne' hq.ne'] at hl
    have he : p/(((C ω:ℝ)+1)/M) = p*M/((C ω:ℝ)+1) := by field_simp
    rw [he] at hl
    exact mul_le_mul_of_nonneg_left hl hp.le
  calc
    (∑ ω, w ω*(p*(Real.log p-Real.log (((C ω:ℝ)+1)/M)))) ≤
        ∑ ω, w ω*(p*(p*M/((C ω:ℝ)+1)-1)) := by
      apply Finset.sum_le_sum
      intro ω hω
      exact mul_le_mul_of_nonneg_left (hscalar ω) (w.nonneg ω)
    _ = p*(p*M*(∑ ω, w ω/((C ω:ℝ)+1))-1) := by
      calc
        _ = (p*p*M)*(∑ ω, w ω/((C ω:ℝ)+1)) - p*(∑ ω, w ω) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro ω hω
          ring
        _ = _ := by rw [w.total]; ring
    _ ≤ p*(p*M*(1/(((k:ℝ)+1)*p))-1) := by
      have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ p*M by positivity)
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right hh 1) hp.le
    _ = _ := by field_simp

/-- Finite-sample add-one KL bound from the genuine binomial cell marginals.
The count table is required to contain exactly k observations in each sample. -/
theorem addOne_expectedKL_le {α Ω : Type*} [Fintype α] [Nonempty α] [Fintype Ω]
    (p : Distribution α) (w : Distribution Ω) (k : ℕ) (C : Ω → α → ℕ)
    (hsum : ∀ ω, ∑ j, C ω j = k)
    (hbin : ∀ j r, r ∈ Finset.range (k+1) →
      (∑ ω, if C ω j = r then w ω else 0) = binomialWeight k (p j) r) :
    (∑ ω, w ω * Distribution.kl p (addOne k (C ω) (hsum ω))) ≤
      ((Fintype.card α:ℝ)-1)/((k:ℝ)+1) := by
  have hM : 0 < (k:ℝ)+Fintype.card α := by positivity
  have hcell : ∀ j, (∑ ω, w ω*(p j*(Real.log (p j)-Real.log
      (((C ω j:ℝ)+1)/((k:ℝ)+Fintype.card α))))) ≤
      p j*(((k:ℝ)+Fintype.card α)/((k:ℝ)+1)-1) := by
    intro j
    by_cases hz : p j = 0
    · simp [hz]
    · have hp : 0 < p j := lt_of_le_of_ne (p.nonneg j) (Ne.symm hz)
      apply expected_addOne_cell_le w k (fun ω => C ω j) hp hM
      rw [inverse_count_of_binomial_marginal w k (fun ω => C ω j) (p j) hp
        (fun ω => count_le_sample_size k (C ω) (hsum ω) j) (hbin j)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hpp := pow_nonneg (show 0 ≤ 1-p j by linarith [p.mass_le_one j]) (k+1)
      linarith
  calc
    _ = ∑ j, ∑ ω, w ω*(p j*(Real.log (p j)-Real.log
        (((C ω j:ℝ)+1)/((k:ℝ)+Fintype.card α)))) := by
      simp only [Distribution.kl, addOne, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ j, p j*(((k:ℝ)+Fintype.card α)/((k:ℝ)+1)-1) :=
      Finset.sum_le_sum (fun j hj => hcell j)
    _ = ((Fintype.card α:ℝ)-1)/((k:ℝ)+1) := by
      rw [← Finset.sum_mul, p.total]
      have hk : (k:ℝ)+1 ≠ 0 := by positivity
      field_simp
      ring

end Paper37.KnownSupport
