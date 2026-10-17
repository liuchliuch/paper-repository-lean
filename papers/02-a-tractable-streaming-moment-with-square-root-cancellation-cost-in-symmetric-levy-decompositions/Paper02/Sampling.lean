import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite probability calculations for the support sampler

The random seed in Appendix A is finite.  The following elementary probability
space therefore suffices, including for adaptively selected sampling levels.
All probabilities and moments below are actual weighted finite sums.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper02.Sampling

/-- A probability law on a finite seed space. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  mass_nonneg : ∀ ω, 0 ≤ mass ω
  mass_sum : ∑ ω, mass ω = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

def expect (X : Ω → ℝ) : ℝ := ∑ ω, μ.mass ω * X ω

def prob (E : Set Ω) : ℝ := μ.expect (fun ω => if ω ∈ E then 1 else 0)

def variance (X : Ω → ℝ) : ℝ := μ.expect (fun ω => (X ω - μ.expect X) ^ 2)

@[simp] lemma expect_const (c : ℝ) : μ.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, μ.mass_sum]

@[simp] lemma expect_add (X Y : Ω → ℝ) :
    μ.expect (fun ω => X ω + Y ω) = μ.expect X + μ.expect Y := by
  simp [expect, mul_add, Finset.sum_add_distrib]

@[simp] lemma expect_sub (X Y : Ω → ℝ) :
    μ.expect (fun ω => X ω - Y ω) = μ.expect X - μ.expect Y := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

@[simp] lemma expect_const_mul (c : ℝ) (X : Ω → ℝ) :
    μ.expect (fun ω => c * X ω) = c * μ.expect X := by
  simp [expect, ← Finset.mul_sum, mul_left_comm]

@[simp] lemma expect_mul_const (X : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => X ω * c) = μ.expect X * c := by
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma expect_congr {X Y : Ω → ℝ} (h : ∀ ω, X ω = Y ω) :
    μ.expect X = μ.expect Y := by
  congr 1
  funext ω
  exact h ω

lemma expect_mono {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    μ.expect X ≤ μ.expect Y :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.mass_nonneg ω)

lemma expect_nonneg {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ μ.expect X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (μ.mass_nonneg ω) (h ω)

@[simp] lemma expect_sum {ι : Type*} (s : Finset ι) (X : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, μ.expect (X i) := by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma variance_eq (X : Ω → ℝ) :
    μ.variance X = μ.expect (fun ω => X ω ^ 2) - μ.expect X ^ 2 := by
  unfold variance
  calc
    _ = μ.expect (fun ω => X ω ^ 2 - 2 * μ.expect X * X ω + μ.expect X ^ 2) := by
      apply μ.expect_congr
      intro ω
      ring
    _ = _ := by simp; ring

lemma variance_nonneg (X : Ω → ℝ) : 0 ≤ μ.variance X :=
  μ.expect_nonneg fun _ => sq_nonneg _

lemma prob_nonneg (E : Set Ω) : 0 ≤ μ.prob E := by
  apply μ.expect_nonneg
  intro ω
  split <;> norm_num

lemma prob_mono {E G : Set Ω} (h : E ⊆ G) : μ.prob E ≤ μ.prob G := by
  apply μ.expect_mono
  intro ω
  by_cases he : ω ∈ E
  · simp [he, h he]
  · simp only [he, if_false]
    split <;> norm_num

lemma prob_union_le (E G : Set Ω) : μ.prob (E ∪ G) ≤ μ.prob E + μ.prob G := by
  simp only [prob]
  rw [← μ.expect_add]
  apply μ.expect_mono
  intro ω
  by_cases he : ω ∈ E <;> by_cases hg : ω ∈ G <;> simp [he, hg]

/-- The finite union bound does not require independence. -/
lemma prob_exists_le_sum {ι : Type*} (s : Finset ι) (E : ι → Set Ω) :
    μ.prob {ω | ∃ i ∈ s, ω ∈ E i} ≤ ∑ i ∈ s, μ.prob (E i) := by
  simp only [prob]
  rw [← μ.expect_sum]
  apply μ.expect_mono
  intro ω
  by_cases h : ∃ i ∈ s, ω ∈ E i
  · obtain ⟨i, hi, hmem⟩ := h
    have hex : ∃ i ∈ s, ω ∈ E i := ⟨i, hi, hmem⟩
    simp only [Set.mem_setOf_eq, if_pos hex]
    have hle := Finset.single_le_sum (f := fun i => if ω ∈ E i then (1 : ℝ) else 0)
      (fun j _ => by dsimp; split <;> norm_num) hi
    simpa only [if_pos hmem] using hle
  · simp only [Set.mem_setOf_eq, if_neg h]
    exact Finset.sum_nonneg fun _ _ => by split <;> norm_num

/-- Markov's bound on a nonnegative random variable, directly from finite sums. -/
lemma markov (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) {t : ℝ} (ht : 0 < t) :
    μ.prob {ω | t ≤ X ω} ≤ μ.expect X / t := by
  apply (le_div_iff₀ ht).2
  rw [prob, ← μ.expect_mul_const]
  apply μ.expect_mono
  intro ω
  by_cases h : t ≤ X ω
  · simpa [h] using h
  · simpa [h] using hX ω

/-- Chebyshev for an arbitrary finite random variable. -/
lemma chebyshev (X : Ω → ℝ) {t : ℝ} (ht : 0 < t) :
    μ.prob {ω | t < |X ω - μ.expect X|} ≤ μ.variance X / t ^ 2 := by
  apply le_trans (μ.prob_mono (G := {ω | t ^ 2 ≤ (X ω - μ.expect X) ^ 2}) ?_)
    (μ.markov _ (fun _ => sq_nonneg _) (sq_pos_of_pos ht))
  intro ω hω
  exact le_of_lt ((sq_lt_sq₀ (le_of_lt ht) (abs_nonneg _)).2 hω |>.trans_eq (sq_abs _))

end FiniteLaw

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

/-- Real Bernoulli indicators with common retention probability and pairwise
independence, expressed by their elementary first and mixed moments. -/
structure PairwiseBernoulli (μ : FiniteLaw Ω) (B : ι → Ω → ℝ) (p : ℝ) : Prop where
  zero_or_one : ∀ i ω, B i ω = 0 ∨ B i ω = 1
  mean : ∀ i, μ.expect (B i) = p
  mixed : ∀ i j, i ≠ j → μ.expect (fun ω => B i ω * B j ω) = p ^ 2

namespace PairwiseBernoulli

variable {μ : FiniteLaw Ω} {B : ι → Ω → ℝ} {p : ℝ}
variable (hB : PairwiseBernoulli μ B p)
include hB

lemma square (i : ι) (ω : Ω) : B i ω ^ 2 = B i ω := by
  rcases hB.zero_or_one i ω with h | h <;> simp [h]

lemma centered_cross (i j : ι) :
    μ.expect (fun ω => (B i ω - p) * (B j ω - p)) =
      if i = j then p * (1 - p) else 0 := by
  calc
    _ = μ.expect (fun ω => B i ω * B j ω - p * B i ω - p * B j ω + p ^ 2) := by
      apply μ.expect_congr
      intro ω
      ring
    _ = μ.expect (fun ω => B i ω * B j ω) - p * p - p * p + p ^ 2 := by
      simp [hB.mean]
    _ = _ := by
      by_cases hij : i = j
      · subst j
        have hs : μ.expect (fun ω => B i ω * B i ω) = p := by
          calc
            _ = μ.expect (B i) := μ.expect_congr fun ω => by nlinarith [hB.square i ω]
            _ = p := hB.mean i
        rw [hs, if_pos rfl]
        ring
      · rw [hB.mixed i j hij, if_neg hij]
        ring

/-- Exact second moment of any centered weighted pairwise Bernoulli sum. -/
lemma centered_sum_square (a : ι → ℝ) :
    μ.expect (fun ω => (∑ i, a i * (B i ω - p)) ^ 2) =
      p * (1 - p) * ∑ i, a i ^ 2 := by
  calc
    _ = μ.expect (fun ω => ∑ i, ∑ j,
          (a i * a j) * ((B i ω - p) * (B j ω - p))) := by
      apply μ.expect_congr
      intro ω
      simp only [sq, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ j, (a i * a j) *
          (if i = j then p * (1 - p) else 0) := by
      simp only [μ.expect_sum, μ.expect_const_mul, hB.centered_cross]
    _ = p * (1 - p) * ∑ i, a i ^ 2 := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The inverse-probability weighted estimate of a sampled moment. -/
def estimator (a : ι → ℝ) (B : ι → Ω → ℝ) (p : ℝ) (ω : Ω) : ℝ :=
  (∑ i, a i * B i ω) / p

lemma estimator_mean (a : ι → ℝ) (hp : p ≠ 0) :
    μ.expect (estimator a B p) = ∑ i, a i := by
  unfold estimator
  simp only [div_eq_mul_inv, μ.expect_mul_const, μ.expect_sum,
    μ.expect_const_mul, hB.mean]
  rw [← Finset.sum_mul]
  field_simp

omit hB in
lemma estimator_centered (a : ι → ℝ) (hp : p ≠ 0) (ω : Ω) :
    estimator a B p ω - ∑ i, a i =
      p⁻¹ * ∑ i, a i * (B i ω - p) := by
  unfold estimator
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  field_simp

/-- Exact variance; pairwise independence is sufficient. -/
lemma estimator_variance (a : ι → ℝ) (hp : p ≠ 0) :
    μ.variance (estimator a B p) = (1 - p) / p * ∑ i, a i ^ 2 := by
  unfold FiniteLaw.variance
  rw [hB.estimator_mean a hp]
  calc
    _ = μ.expect (fun ω => p⁻¹ ^ 2 * (∑ i, a i * (B i ω - p)) ^ 2) := by
      apply μ.expect_congr
      intro ω
      rw [estimator_centered a hp]
      ring
    _ = p⁻¹ ^ 2 * (p * (1 - p) * ∑ i, a i ^ 2) := by
      rw [μ.expect_const_mul, hB.centered_sum_square]
    _ = _ := by field_simp

/-- Proposition 3.4: bounded weights give `Var Z ≤ 9s/p`. -/
lemma estimator_variance_le (a : ι → ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (ha0 : ∀ i, 0 ≤ a i) (ha3 : ∀ i, a i ≤ 3) :
    μ.variance (estimator a B p) ≤ 9 * Fintype.card ι / p := by
  rw [hB.estimator_variance a (ne_of_gt hp)]
  have hsum : (∑ i, a i ^ 2) ≤ 9 * (Fintype.card ι : ℝ) := by
    calc
      _ ≤ ∑ _i : ι, (9 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [ha0 i, ha3 i]
      _ = _ := by simp; ring
  have hsum0 : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfactor : 0 ≤ (1 - p) / p := div_nonneg (by linarith) (le_of_lt hp)
  have hf : (1 - p) / p ≤ 1 / p :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hp)
  calc
    _ ≤ (1 / p) * ∑ i, a i ^ 2 := mul_le_mul_of_nonneg_right hf hsum0
    _ ≤ (1 / p) * (9 * Fintype.card ι) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

omit hB in
lemma total_weight_bounds (a : ι → ℝ) (ha1 : ∀ i, 1 ≤ a i)
    (ha3 : ∀ i, a i ≤ 3) :
    (Fintype.card ι : ℝ) ≤ ∑ i, a i ∧
      (∑ i, a i) ≤ 3 * Fintype.card ι := by
  constructor
  · calc
      _ = ∑ _i : ι, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => ha1 i
  · calc
      _ ≤ ∑ _i : ι, (3 : ℝ) := Finset.sum_le_sum fun i _ => ha3 i
      _ = _ := by simp; ring

/-- Unscaled weighted sum: the mean identity used for sampled support. -/
lemma sum_mean (a : ι → ℝ) :
    μ.expect (fun ω => ∑ i, a i * B i ω) = p * ∑ i, a i := by
  simp only [μ.expect_sum, μ.expect_const_mul, hB.mean]
  rw [← Finset.sum_mul]
  ring

lemma sum_variance (a : ι → ℝ) :
    μ.variance (fun ω => ∑ i, a i * B i ω) =
      p * (1 - p) * ∑ i, a i ^ 2 := by
  unfold FiniteLaw.variance
  rw [hB.sum_mean]
  calc
    _ = μ.expect (fun ω => (∑ i, a i * (B i ω - p)) ^ 2) := by
      apply μ.expect_congr
      intro ω
      congr 1
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    _ = _ := hB.centered_sum_square a

/-- Chebyshev's relative-error estimate for weights in `[1,3]`. -/
lemma estimator_failure_le (a : ι → ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (ha1 : ∀ i, 1 ≤ a i) (ha3 : ∀ i, a i ≤ 3)
    (hs : 0 < Fintype.card ι) {ε : ℝ} (hε : 0 < ε) :
    μ.prob {ω | ε * (∑ i, a i) <
      |estimator a B p ω - (∑ i, a i)|} ≤
      9 / (ε ^ 2 * p * Fintype.card ι) := by
  have hs0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hs
  have hF := (total_weight_bounds a ha1 ha3).1
  have hF0 : 0 < ∑ i, a i := lt_of_lt_of_le hs0 hF
  have hvar := hB.estimator_variance_le a hp hp1 (fun i => by linarith [ha1 i]) ha3
  have hc := μ.chebyshev (estimator a B p) (mul_pos hε hF0)
  rw [hB.estimator_mean a (ne_of_gt hp)] at hc
  apply le_trans hc
  calc
    _ ≤ (9 * Fintype.card ι / p) / (ε * ∑ i, a i) ^ 2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ ≤ (9 * Fintype.card ι / p) / (ε ^ 2 * (Fintype.card ι : ℝ) ^ 2) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [sq_le_sq₀ (le_of_lt hs0) (le_of_lt hF0) |>.2 hF,
        mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr
          (sq_le_sq₀ (le_of_lt hs0) (le_of_lt hF0) |>.2 hF))]
    _ = _ := by field_simp

/-- The sampled support overflows a threshold with probability at most `2/K`
when its mean is at most `K/2` (Appendix A, equation A.6). -/
lemma support_overflow_le (hp : 0 < p) (hp1 : p ≤ 1) {K : ℝ}
    (hK : 0 < K) (hmean : p * Fintype.card ι ≤ K / 2) :
    μ.prob {ω | K < ∑ i, B i ω} ≤ 2 / K := by
  let s : ℝ := Fintype.card ι
  have hs : 0 ≤ s := by positivity
  have hgap : 0 < K - p * s := by dsimp [s]; linarith
  have hvar : μ.variance (fun ω => ∑ i, B i ω) ≤ p * s := by
    have hv := hB.sum_variance (fun _ => 1)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] at hv
    rw [hv]
    dsimp [s]
    nlinarith [mul_nonneg (le_of_lt hp) (Nat.cast_nonneg (Fintype.card ι))]
  have hm : μ.expect (fun ω => ∑ i, B i ω) = p * s := by
    simpa [s] using hB.sum_mean (fun _ => 1)
  have hc := μ.chebyshev (fun ω => ∑ i, B i ω) hgap
  rw [hm] at hc
  have hevent : {ω | K < ∑ i, B i ω} ⊆
      {ω | K - p * s < |(∑ i, B i ω) - p * s|} := by
    intro ω hω
    dsimp at *
    have hh := le_abs_self ((∑ i, B i ω) - p * s)
    linarith
  calc
    _ ≤ μ.prob {ω | K - p * s < |(∑ i, B i ω) - p * s|} := μ.prob_mono hevent
    _ ≤ μ.variance (fun ω => ∑ i, B i ω) / (K - p * s) ^ 2 := hc
    _ ≤ p * s / (K - p * s) ^ 2 := div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ ≤ 2 / K := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hgap) hK]
      have hfirst : 0 ≤ K - 2 * (p * s) := by dsimp [s]; linarith
      have hsecond : 0 ≤ 2 * K - p * s := by dsimp [s]; linarith
      nlinarith [mul_nonneg hfirst hsecond]

end PairwiseBernoulli

/-- Retention probability at level `j` of the dyadic sampler. -/
def dyadicProb (j : ℕ) : ℝ := 1 / (2 : ℝ) ^ j

lemma dyadicProb_pos (j : ℕ) : 0 < dyadicProb j := by
  unfold dyadicProb
  positivity

lemma dyadicProb_le_one (j : ℕ) : dyadicProb j ≤ 1 := by
  unfold dyadicProb
  exact (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))

@[simp] lemma dyadicProb_zero : dyadicProb 0 = 1 := by norm_num [dyadicProb]

lemma dyadicProb_succ (j : ℕ) : dyadicProb (j + 1) = dyadicProb j / 2 := by
  simp [dyadicProb, pow_succ]
  ring

/-- A useful dyadic level exists without knowing the support size in the
algorithm.  The proof uses the least level of expected support at most `K/2`;
this equals the ceiling-log level of Appendix A. -/
lemma exists_useful_dyadic_level {s K : ℝ} {J : ℕ}
    (hK : 2 ≤ K) (hs : K < s) (hcap : s ≤ (2 : ℝ) ^ J) :
    ∃ L : ℕ, 1 ≤ L ∧ L ≤ J ∧
      K / 4 < dyadicProb L * s ∧ dyadicProb L * s ≤ K / 2 := by
  have hJsmall : dyadicProb J * s ≤ 1 := by
    calc
      _ = s / (2 : ℝ) ^ J := by simp [dyadicProb, div_eq_mul_inv, mul_comm]
      _ ≤ 1 := (div_le_one (by positivity)).2 hcap
  have hJ : dyadicProb J * s ≤ K / 2 := by linarith
  have hex : ∃ j : ℕ, dyadicProb j * s ≤ K / 2 := ⟨J, hJ⟩
  let L := Nat.find hex
  have hL : dyadicProb L * s ≤ K / 2 := Nat.find_spec hex
  have hLJ : L ≤ J := Nat.find_min' hex hJ
  have hLpos : 0 < L := by
    by_contra hn
    have hz : L = 0 := by omega
    rw [hz, dyadicProb_zero, one_mul] at hL
    linarith
  have hprev : K / 2 < dyadicProb (L - 1) * s := by
    exact lt_of_not_ge (Nat.find_min hex (Nat.sub_lt hLpos (by norm_num)))
  have hrec : dyadicProb L = dyadicProb (L - 1) / 2 := by
    have he : L = (L - 1) + 1 := by omega
    conv_lhs => rw [he]
    exact dyadicProb_succ _
  refine ⟨L, hLpos, hLJ, ?_, hL⟩
  rw [hrec]
  linarith

lemma sum_two_powers (L : ℕ) :
    (∑ j ∈ Finset.range (L + 1), (2 : ℝ) ^ j) = 2 ^ (L + 1) - 1 := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

/-- Appendix A, equation A.7.  Only independence within each level is used. -/
lemma dyadic_failure_union_lt (μ : FiniteLaw Ω) (a : ι → ℝ)
    (B : ℕ → ι → Ω → ℝ) (L : ℕ)
    (hB : ∀ j ≤ L, PairwiseBernoulli μ (B j) (dyadicProb j))
    (ha1 : ∀ i, 1 ≤ a i) (ha3 : ∀ i, a i ≤ 3)
    (hs : 0 < Fintype.card ι) {ε : ℝ} (hε : 0 < ε) :
    μ.prob {ω | ∃ j ≤ L, ε * (∑ i, a i) <
      |PairwiseBernoulli.estimator a (B j) (dyadicProb j) ω - (∑ i, a i)|} <
      18 / (ε ^ 2 * dyadicProb L * Fintype.card ι) := by
  have hs0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hs
  let E : ℕ → Set Ω := fun j => {ω | ε * (∑ i, a i) <
    |PairwiseBernoulli.estimator a (B j) (dyadicProb j) ω - (∑ i, a i)|}
  have hevent : {ω | ∃ j ≤ L, ω ∈ E j} =
      {ω | ∃ j ∈ Finset.range (L + 1), ω ∈ E j} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.mem_range, Nat.lt_succ_iff]
  change μ.prob {ω | ∃ j ≤ L, ω ∈ E j} < _
  rw [hevent]
  apply lt_of_le_of_lt (μ.prob_exists_le_sum (Finset.range (L + 1)) E)
  calc
    _ ≤ ∑ j ∈ Finset.range (L + 1),
        9 / (ε ^ 2 * dyadicProb j * Fintype.card ι) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (hB j (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)).estimator_failure_le
        a (dyadicProb_pos j) (dyadicProb_le_one j) ha1 ha3 hs hε
    _ = (9 / (ε ^ 2 * Fintype.card ι)) * (2 ^ (L + 1) - 1) := by
      rw [← sum_two_powers, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      unfold dyadicProb
      field_simp
    _ < 18 / (ε ^ 2 * dyadicProb L * Fintype.card ι) := by
      unfold dyadicProb
      have hpow : (0 : ℝ) < 2 ^ L := by positivity
      rw [pow_succ]
      field_simp
      simp only [pow_succ]
      nlinarith

/-- The last useful level has expected support greater than `K/4`, so
its entire adaptive prefix has error probability less than `72/(ε²K)`. -/
lemma dyadic_failure_union_lt_K (μ : FiniteLaw Ω) (a : ι → ℝ)
    (B : ℕ → ι → Ω → ℝ) (L : ℕ)
    (hB : ∀ j ≤ L, PairwiseBernoulli μ (B j) (dyadicProb j))
    (ha1 : ∀ i, 1 ≤ a i) (ha3 : ∀ i, a i ≤ 3)
    (hs : 0 < Fintype.card ι) {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hmean : K / 4 < dyadicProb L * Fintype.card ι) :
    μ.prob {ω | ∃ j ≤ L, ε * (∑ i, a i) <
      |PairwiseBernoulli.estimator a (B j) (dyadicProb j) ω - (∑ i, a i)|} <
      72 / (ε ^ 2 * K) := by
  have hs0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hs
  have hpL := dyadicProb_pos L
  apply lt_trans (dyadic_failure_union_lt μ a B L hB ha1 ha3 hs hε)
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  have hh : 0 < 4 * (dyadicProb L * Fintype.card ι) - K := by linarith
  nlinarith [mul_pos (sq_pos_of_pos hε) hh]

/-- Compose recovery correctness with the adaptive-level concentration bound.
The two decoder hypotheses are the deterministic properties of the actual
selection algorithm: on checksum success, a sparse final useful level forces
selection in its prefix and the recovered output equals that prefix estimate. -/
lemma adaptive_failure_lt (μ : FiniteLaw Ω) (a : ι → ℝ)
    (B : ℕ → ι → Ω → ℝ) (L : ℕ)
    (hB : ∀ j ≤ L, PairwiseBernoulli μ (B j) (dyadicProb j))
    (ha1 : ∀ i, 1 ≤ a i) (ha3 : ∀ i, a i ≤ 3)
    (hs : 0 < Fintype.card ι) {ε K qerr : ℝ}
    (hε : 0 < ε) (hK : 0 < K)
    (hmeanlo : K / 4 < dyadicProb L * Fintype.card ι)
    (hmeanhi : dyadicProb L * Fintype.card ι ≤ K / 2)
    (D : Set Ω) (hD : μ.prob D ≤ qerr) (select : Ω → ℕ) (output : Ω → ℝ)
    (hselect : ∀ ω, ω ∉ D → (∑ i, B L i ω) ≤ K → select ω ≤ L)
    (hout : ∀ ω, ω ∉ D → (∑ i, B L i ω) ≤ K →
      output ω = PairwiseBernoulli.estimator a (B (select ω)) (dyadicProb (select ω)) ω) :
    μ.prob {ω | ε * (∑ i, a i) < |output ω - (∑ i, a i)|} <
      qerr + 2 / K + 72 / (ε ^ 2 * K) := by
  let O : Set Ω := {ω | K < ∑ i, B L i ω}
  let E : Set Ω := {ω | ∃ j ≤ L, ε * (∑ i, a i) <
    |PairwiseBernoulli.estimator a (B j) (dyadicProb j) ω - (∑ i, a i)|}
  have hsub : {ω | ε * (∑ i, a i) < |output ω - (∑ i, a i)|} ⊆ (D ∪ O) ∪ E := by
    intro ω hω
    by_cases hd : ω ∈ D
    · exact Or.inl (Or.inl hd)
    by_cases ho : K < ∑ i, B L i ω
    · exact Or.inl (Or.inr ho)
    · right
      refine ⟨select ω, hselect ω hd (le_of_not_gt ho), ?_⟩
      change ε * (∑ i, a i) < |output ω - (∑ i, a i)| at hω
      rwa [hout ω hd (le_of_not_gt ho)] at hω
  have hov := (hB L (le_refl L)).support_overflow_le
    (dyadicProb_pos L) (dyadicProb_le_one L) hK hmeanhi
  have hacc := dyadic_failure_union_lt_K μ a B L hB ha1 ha3 hs hε hK hmeanlo
  have hu := μ.prob_union_le (D ∪ O) E
  have hv := μ.prob_union_le D O
  have he := μ.prob_mono hsub
  change μ.prob O ≤ 2 / K at hov
  change μ.prob E < 72 / (ε ^ 2 * K) at hacc
  linarith

/-- Constants with slack for elementary independent-copy amplification. -/
lemma single_copy_sixteenth {ε K : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hK : 65536 / ε ^ 2 ≤ K) :
    (1 : ℝ) / 1024 + 2 / K + 72 / (ε ^ 2 * K) < 1 / 16 := by
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hε21 : ε ^ 2 ≤ 1 := by nlinarith
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hK
  have hprod : 65536 ≤ ε ^ 2 * K := by
    simpa only [mul_comm] using (div_le_iff₀ hε2).1 hK
  have hKbig : 65536 ≤ K := by
    nlinarith [mul_le_mul_of_nonneg_right hε21 (le_of_lt hK0)]
  have htwo : 2 / K ≤ (2 : ℝ) / 65536 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKbig
  have h72 : 72 / (ε ^ 2 * K) ≤ (72 : ℝ) / 65536 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hprod
  norm_num at *
  linarith

namespace FiniteLaw

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The uniform law on a nonempty finite seed space. -/
def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  mass _ := 1 / Fintype.card Ω
  mass_nonneg _ := by positivity
  mass_sum := by
    have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [hcard]

lemma uniform_expect [Nonempty Ω] (X : Ω → ℝ) :
    (uniform Ω).expect X = (∑ ω, X ω) / Fintype.card Ω := by
  unfold expect uniform
  simp only [one_div, div_eq_mul_inv, ← Finset.mul_sum]
  ring

lemma uniform_prob [Nonempty Ω] (E : Set Ω) :
    (uniform Ω).prob E =
      (((Finset.univ : Finset Ω).filter (fun ω => ω ∈ E)).card : ℝ) / Fintype.card Ω := by
  unfold prob
  rw [uniform_expect]
  congr 1
  simp

/-- Independent copies of a finite seed law, constructed as a Cartesian product. -/
def iid (μ : FiniteLaw Ω) (κ : Type*) [Fintype κ] [DecidableEq κ] : FiniteLaw (κ → Ω) where
  mass ω := ∏ i, μ.mass (ω i)
  mass_nonneg ω := Finset.prod_nonneg fun i _ => μ.mass_nonneg (ω i)
  mass_sum := by
    rw [← Fintype.prod_sum]
    simp [μ.mass_sum]

/-- Factorization is proved for the constructed product law. -/
lemma iid_expect_product (μ : FiniteLaw Ω) (g : κ → Ω → ℝ) :
    (μ.iid κ).expect (fun ω => ∏ i, g i (ω i)) = ∏ i, μ.expect (g i) := by
  unfold expect iid
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i ω => μ.mass ω * g i ω)).symm

lemma iid_prob_all (μ : FiniteLaw Ω) (T : Finset κ) (E : κ → Set Ω) :
    (μ.iid κ).prob {ω | ∀ i ∈ T, ω i ∈ E i} = ∏ i ∈ T, μ.prob (E i) := by
  let g : κ → Ω → ℝ := fun i ω => if i ∈ T then (if ω ∈ E i then 1 else 0) else 1
  have hind (ω : κ → Ω) : (if ∀ i ∈ T, ω i ∈ E i then (1 : ℝ) else 0) =
      ∏ i, g i (ω i) := by
    by_cases h : ∀ i ∈ T, ω i ∈ E i
    · rw [if_pos h]
      symm
      apply Finset.prod_eq_one
      intro i _
      by_cases hi : i ∈ T
      · simp [g, hi, h i hi]
      · simp [g, hi]
    · rw [if_neg h]
      push_neg at h
      obtain ⟨i, hi, hf⟩ := h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [g, hi, hf]
  calc
    _ = (μ.iid κ).expect (fun ω => ∏ i, g i (ω i)) := by
      apply (μ.iid κ).expect_congr
      intro ω
      by_cases h : ∀ i ∈ T, ω i ∈ E i
      · simpa only [Set.mem_setOf_eq, if_pos h] using hind ω
      · simpa only [Set.mem_setOf_eq, if_neg h] using hind ω
    _ = ∏ i, μ.expect (g i) := μ.iid_expect_product g
    _ = ∏ i, if i ∈ T then μ.prob (E i) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ T <;> simp [g, hi, prob]
    _ = _ := Fintype.prod_ite_mem T _

/-- Union over all failure subsets proves amplification without an analytic
concentration theorem. -/
lemma iid_many_failures_le (μ : FiniteLaw Ω) (E : κ → Set Ω) {p : ℝ}
    (hp : 0 ≤ p) (hE : ∀ i, μ.prob (E i) ≤ p) (k : ℕ) :
    (μ.iid κ).prob {ω | k ≤ ((Finset.univ : Finset κ).filter (fun i => ω i ∈ E i)).card} ≤
      (2 : ℝ) ^ Fintype.card κ * p ^ k := by
  let family : Finset (Finset κ) := (Finset.univ : Finset κ).powersetCard k
  let A : Finset κ → Set (κ → Ω) := fun T => {ω | ∀ i ∈ T, ω i ∈ E i}
  have hsub : {ω | k ≤ ((Finset.univ : Finset κ).filter (fun i => ω i ∈ E i)).card} ⊆
      {ω | ∃ T ∈ family, ω ∈ A T} := by
    intro ω hω
    obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hω
    refine ⟨T, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨fun i hi => Finset.mem_univ i, hcard⟩
    · intro i hi
      exact (Finset.mem_filter.mp (hT hi)).2
  calc
    _ ≤ (μ.iid κ).prob {ω | ∃ T ∈ family, ω ∈ A T} := (μ.iid κ).prob_mono hsub
    _ ≤ ∑ T ∈ family, (μ.iid κ).prob (A T) := (μ.iid κ).prob_exists_le_sum family A
    _ ≤ ∑ _T ∈ family, p ^ k := by
      apply Finset.sum_le_sum
      intro T hT
      rw [μ.iid_prob_all]
      have hcard := (Finset.mem_powersetCard.mp hT).2
      calc
        _ ≤ ∏ _i ∈ T, p := Finset.prod_le_prod (fun i _ => μ.prob_nonneg (E i)) (fun i _ => hE i)
        _ = p ^ k := by simp [hcard]
    _ = (family.card : ℝ) * p ^ k := by simp
    _ ≤ (2 : ℝ) ^ Fintype.card κ * p ^ k := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp k)
      have hcard : family.card ≤ ((Finset.univ : Finset κ).powerset).card := by
        apply Finset.card_le_card
        intro T hT
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hT).1
      have hc : family.card ≤ 2 ^ Fintype.card κ := by
        simpa only [Finset.card_powerset, Finset.card_univ] using hcard
      exact_mod_cast hc

/-- With per-copy failure probability at most `1/16`, an odd number of
independent copies has a majority failure probability at most `2⁻ᴿ`. -/
lemma iid_majority_failure_le (μ : FiniteLaw Ω) (b : ℕ)
    (E : Fin (2 * b + 1) → Set Ω) (hE : ∀ i, μ.prob (E i) ≤ 1 / 16) :
    (μ.iid (Fin (2 * b + 1))).prob
      {ω | b + 1 ≤ ((Finset.univ : Finset (Fin (2 * b + 1))).filter
        (fun i => ω i ∈ E i)).card} ≤ 1 / (2 : ℝ) ^ (2 * b + 1) := by
  have hh := μ.iid_many_failures_le E (by norm_num : (0 : ℝ) ≤ 1 / 16) hE (b + 1)
  simp only [Fintype.card_fin] at hh
  apply le_trans hh
  have hpow : ∀ b : ℕ,
      (2 : ℝ) ^ (2 * b + 1) * (1 / 16 : ℝ) ^ (b + 1) ≤
        1 / (2 : ℝ) ^ (2 * b + 1) := by
    intro b
    induction b with
    | zero => norm_num
    | succ b ih =>
      have he : 2 * (b + 1) + 1 = (2 * b + 1) + 2 := by omega
      calc
        _ = (1 / 4 : ℝ) * (2 ^ (2 * b + 1) * (1 / 16 : ℝ) ^ (b + 1)) := by
          rw [he, pow_add, pow_succ]
          norm_num
          ring
        _ ≤ (1 / 4 : ℝ) * (1 / (2 : ℝ) ^ (2 * b + 1)) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by rw [he, pow_add]; norm_num; ring
  exact hpow b

end FiniteLaw

/-- Maximum value on a finite subset.  The empty case is immaterial to the
median, whose defining subsets have cardinality `b+1`. -/
def subsetMaximum {κ : Type*} (a : κ → ℝ) (T : Finset κ) : ℝ :=
  if h : T.Nonempty then T.sup' h a else 0

/-- The middle order statistic of `2b+1` real values, by its finite minimax
formula: minimize the maximum over all subsets of `b+1` positions. -/
def median (b : ℕ) (a : Fin (2 * b + 1) → ℝ) : ℝ :=
  let family := (Finset.univ : Finset (Fin (2 * b + 1))).powersetCard (b + 1)
  family.inf' (Finset.powersetCard_nonempty.mpr (by simp; omega)) (subsetMaximum a)

/-- A strict majority of values in an interval forces their median into it. -/
lemma median_interval (b : ℕ) (a : Fin (2 * b + 1) → ℝ) (lo hi : ℝ)
    (hbad : ((Finset.univ : Finset (Fin (2 * b + 1))).filter
      (fun i => ¬ (lo ≤ a i ∧ a i ≤ hi))).card ≤ b) :
    lo ≤ median b a ∧ median b a ≤ hi := by
  let good := (Finset.univ : Finset (Fin (2 * b + 1))).filter
    (fun i => lo ≤ a i ∧ a i ≤ hi)
  let bad := (Finset.univ : Finset (Fin (2 * b + 1))).filter
    (fun i => ¬ (lo ≤ a i ∧ a i ≤ hi))
  have hsum : good.card + bad.card = 2 * b + 1 := by
    simpa [good, bad] using
      (Finset.univ : Finset (Fin (2 * b + 1))).filter_card_add_filter_neg_card_eq_card
        (fun i => lo ≤ a i ∧ a i ≤ hi)
  have hgood : b + 1 ≤ good.card := by change bad.card ≤ b at hbad; omega
  constructor
  · unfold median
    apply Finset.le_inf'
    intro T hT
    have hcard : T.card = b + 1 := (Finset.mem_powersetCard.mp hT).2
    have hg : ∃ i ∈ T, i ∈ good := by
      by_contra hn
      push_neg at hn
      have hsub : T ⊆ bad := by
        intro i hiT
        have hh := hn i hiT
        simpa only [good, bad, Finset.mem_filter, Finset.mem_univ, true_and, not_and] using hh
      have hc := Finset.card_le_card hsub
      change bad.card ≤ b at hbad
      omega
    obtain ⟨i, hiT, hiG⟩ := hg
    have hlo : lo ≤ a i := (Finset.mem_filter.mp hiG).2.1
    have hne : T.Nonempty := ⟨i, hiT⟩
    unfold subsetMaximum
    rw [dif_pos hne]
    exact hlo.trans (Finset.le_sup' a hiT)
  · obtain ⟨T, hTgood, hcard⟩ := Finset.exists_subset_card_eq hgood
    have hTfamily : T ∈ (Finset.univ : Finset (Fin (2 * b + 1))).powersetCard (b + 1) :=
      Finset.mem_powersetCard.mpr ⟨fun i _ => Finset.mem_univ i, hcard⟩
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    unfold median
    apply le_trans (Finset.inf'_le _ hTfamily)
    unfold subsetMaximum
    rw [dif_pos hne]
    apply Finset.sup'_le
    intro i hiT
    exact (Finset.mem_filter.mp (hTgood hiT)).2.2

/-- A median can be inaccurate only if a majority of the estimates are
inaccurate.  This lemma concerns the actual order statistic above. -/
lemma median_failure_subset (b : ℕ) (X : Ω → ℝ) (F t : ℝ) :
    {ω : Fin (2 * b + 1) → Ω | t < |median b (fun i => X (ω i)) - F|} ⊆
      {ω | b + 1 ≤ ((Finset.univ : Finset (Fin (2 * b + 1))).filter
        (fun i => t < |X (ω i) - F|)).card} := by
  intro ω hω
  by_contra hn
  have hcount : ((Finset.univ : Finset (Fin (2 * b + 1))).filter
      (fun i => t < |X (ω i) - F|)).card ≤ b := by
    change ¬ b + 1 ≤ _ at hn
    omega
  have hbad : ((Finset.univ : Finset (Fin (2 * b + 1))).filter
      (fun i => ¬ (F - t ≤ X (ω i) ∧ X (ω i) ≤ F + t))).card ≤ b := by
    convert hcount using 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← not_le, abs_le]
    constructor <;> intro h <;> contrapose! h <;> constructor <;> linarith [h.1, h.2]
  have hm := median_interval b (fun i => X (ω i)) (F - t) (F + t) hbad
  have habs : |median b (fun i => X (ω i)) - F| ≤ t := by
    rw [abs_le]
    constructor <;> linarith [hm.1, hm.2]
  exact (not_lt_of_ge habs) hω

/-- A complete finite probability amplification bound for the actual median
of independent copies. -/
lemma iid_median_failure_le (μ : FiniteLaw Ω) (b : ℕ) (X : Ω → ℝ) (F t : ℝ)
    (hX : μ.prob {ω | t < |X ω - F|} ≤ 1 / 16) :
    (μ.iid (Fin (2 * b + 1))).prob
      {ω | t < |median b (fun i => X (ω i)) - F|} ≤
      1 / (2 : ℝ) ^ (2 * b + 1) := by
  apply le_trans ((μ.iid _).prob_mono (median_failure_subset b X F t))
  exact μ.iid_majority_failure_le b (fun _ => {ω | t < |X ω - F|}) (fun _ => hX)

/-- The paper's repetition count also suffices for the stronger elementary
amplification bound proved here. -/
lemma inverse_two_pow_le_delta (R : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hR : 8 * Real.log (1 / δ) ≤ (R : ℝ)) :
    1 / (2 : ℝ) ^ R ≤ δ := by
  have hlog2 : (1 : ℝ) / 8 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    linarith
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hlog : -(R : ℝ) * Real.log 2 ≤ Real.log δ := by
    rw [Real.log_div (by norm_num) (ne_of_gt hδ), Real.log_one, zero_sub] at hR
    nlinarith [mul_le_mul_of_nonneg_left hlog2 hR0]
  calc
    _ = Real.exp (-((R : ℝ) * Real.log 2)) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      simp only [one_div]
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr (by nlinarith)
    _ = δ := Real.exp_log hδ

lemma iid_median_failure_le_delta (μ : FiniteLaw Ω) (b : ℕ) (X : Ω → ℝ)
    (F t : ℝ) (hX : μ.prob {ω | t < |X ω - F|} ≤ 1 / 16)
    {δ : ℝ} (hδ : 0 < δ) (hR : 8 * Real.log (1 / δ) ≤ (2 * b + 1 : ℕ)) :
    (μ.iid (Fin (2 * b + 1))).prob
      {ω | t < |median b (fun i => X (ω i)) - F|} ≤ δ :=
  (iid_median_failure_le μ b X F t hX).trans (inverse_two_pow_le_delta _ hδ hR)

end Paper02.Sampling
