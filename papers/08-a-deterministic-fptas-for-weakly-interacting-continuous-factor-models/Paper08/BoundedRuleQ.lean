import Paper08.PrimitiveMomentsQ

/-! # Actual magnitude bounds for the rational primitive and moment programs -/
open scoped BigOperators
namespace Paper08.BoundedRuleQ
open CellGrid RationalQuadrature PrimitiveMomentsQ

lemma weightQ_nonneg {n : ℕ} (m : Fin n → ℕ) : 0 ≤ weightQ m := by
  unfold weightQ
  positivity

lemma sum_weightsQ {n : ℕ} (m : Fin n → ℕ) : (∑ _z : Grid m, weightQ m) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_grid]
  simp [weightQ]

lemma abs_incrementQ_le_one {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (table : SampleTable scopes) (htable : ∀ i l p, 0 ≤ table i l p ∧ table i l p ≤ 1)
    (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν)) (i : Fin t) :
    |incrementQ scopes table ν z i| ≤ 1 := by
  unfold incrementQ
  generalize hν : ν i = l
  cases l with
  | zero => exact (abs_of_nonneg (htable _ _ _).1).trans_le (htable _ _ _).2
  | succ l =>
      have ha := htable i (l + 1) (localIndex scopes ν z i (l + 1))
      have hb := htable i l (localIndex scopes ν z i l)
      change |table i (l + 1) (localIndex scopes ν z i (l + 1)) - table i l (localIndex scopes ν z i l)| ≤ 1
      exact abs_le.mpr ⟨by linarith [ha.1, ha.2, hb.1, hb.2], by linarith [ha.1, ha.2, hb.1, hb.2]⟩

/-- The actual signed cell weights sum to one per retained level vector. Since
all rounded primitive samples lie in [0,1], each increment has absolute value ≤1. -/
theorem abs_ruleQ_le_levels {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (table : SampleTable scopes) (htable : ∀ i l p, 0 ≤ table i l p ∧ table i l p ≤ 1) (J : ℕ) :
    |ruleQ scopes table J| ≤ ((J + t).choose t : ℚ) := by
  unfold ruleQ
  calc
    _ ≤ ∑ ν ∈ TupleCount.boundedTuples t J,
        |∑ z : Grid (commonLevels scopes ν), weightQ (commonLevels scopes ν) *
          ∏ i, incrementQ scopes table ν z i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ν ∈ TupleCount.boundedTuples t J, (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro ν _
      calc
        _ ≤ ∑ z : Grid (commonLevels scopes ν),
            |weightQ (commonLevels scopes ν) * ∏ i, incrementQ scopes table ν z i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _z : Grid (commonLevels scopes ν), weightQ (commonLevels scopes ν) := by
          apply Finset.sum_le_sum
          intro z _
          rw [abs_mul, abs_of_nonneg (weightQ_nonneg _)]
          apply mul_le_of_le_one_right (weightQ_nonneg _)
          rw [Finset.abs_prod]
          exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => abs_incrementQ_le_one scopes table htable ν z i)
        _ = 1 := sum_weightsQ _
    _ = _ := by simp [TupleCount.card_boundedTuples]

/-- No analytic or oracle-accuracy hypotheses are needed for this program magnitude bound. -/
theorem abs_primitiveRuleQ_le {n t s C : ℕ} (scopes : Fin t → Finset (Fin n))
    (query : (i : Fin t) → (Fin (scopes i).card → ℚ) → ℕ → ℚ)
    (α : Fin t → ℕ) (τ : ℚ) :
    |primitiveRuleQ scopes query α s C τ| ≤ (2 : ℚ) ^ (Oracle.totalLevelChoice s C τ + t) := by
  unfold primitiveRuleQ
  exact (abs_ruleQ_le_levels scopes _ (fun i l p => Oracle.primitiveSampleQ_range _ _ _) _).trans
    (by exact_mod_cast Nat.choose_le_two_pow (Oracle.totalLevelChoice s C τ + t) t)

/-- Bound for the actual sparse primitive program with total exponent degree ≤s. -/
theorem abs_primitiveQ_le {n m s C : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (d : Fin m →₀ ℕ) (hd : d.degree ≤ s) (τ : ℚ) :
    |primitiveQ scopes query d s C τ| ≤ (2 : ℚ) ^ (Oracle.totalLevelChoice s C τ + s) := by
  have hsupport : d.support.card ≤ s := by
    calc
      d.support.card = ∑ _i ∈ d.support, 1 := by simp
      _ ≤ ∑ i ∈ d.support, d i := Finset.sum_le_sum fun i hi =>
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
      _ = d.degree := rfl
      _ ≤ s := hd
  exact (abs_primitiveRuleQ_le _ _ _ τ).trans
    (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_left hsupport _))

/-- Actual computed moments are at most `2^(J+3s)` in magnitude. This derives
from the computed cell sums, the true exponent enumeration, and factorial weights. -/
theorem abs_momentQ_le {n m s C j : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (B : Finset (Fin m)) (hB : B.card ≤ s) (hj : j ≤ s) (τ : ℚ) :
    |momentQ scopes query B j s C τ| ≤ (2 : ℚ) ^ (Oracle.totalLevelChoice s C τ + 3 * s) := by
  by_cases hj0 : j = 0
  · subst j
    simp only [momentQ_zero, abs_one]
    exact one_le_pow₀ (by norm_num)
  unfold momentQ
  rw [if_neg hj0]
  have hterm : ∀ d ∈ Finset.finsuppAntidiag B j,
      |primitiveQ scopes query d s C τ / factorialWeight d| ≤
        (2 : ℚ) ^ (Oracle.totalLevelChoice s C τ + s) := by
    intro d hd
    have hdeg : d.degree ≤ s := by
      have hh := (Finset.mem_finsuppAntidiag'.mp hd).1
      change (∑ e ∈ d.support, d e) ≤ s
      change (∑ e ∈ d.support, d e) = j at hh
      omega
    rw [abs_div, abs_of_nonneg (show (0 : ℚ) ≤ (factorialWeight d : ℚ) from Nat.cast_nonneg _)]
    exact (div_le_self (abs_nonneg _) (by exact_mod_cast factorialWeight_pos d)).trans
      (abs_primitiveQ_le scopes query d hdeg τ)
  calc
    _ ≤ ∑ d ∈ Finset.finsuppAntidiag B j, |primitiveQ scopes query d s C τ / factorialWeight d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.finsuppAntidiag B j, (2 : ℚ) ^ (Oracle.totalLevelChoice s C τ + s) :=
      Finset.sum_le_sum hterm
    _ = ((Finset.finsuppAntidiag B j).card : ℚ) * (2 : ℚ) ^ (Oracle.totalLevelChoice s C τ + s) := by simp
    _ ≤ (4 : ℚ) ^ s * (2 : ℚ) ^ (Oracle.totalLevelChoice s C τ + s) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast TupleCount.card_finsuppAntidiag_le B hB hj) (by positivity)
    _ = _ := by rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]; congr 1; omega

/-- The coarser form used by the recurrence numerator bound. -/
theorem abs_momentQ_le_coarse {n m s C j : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (B : Finset (Fin m)) (hB : B.card ≤ s) (hj : j ≤ s)
    (hs : 1 ≤ s) (τ : ℚ) :
    |momentQ scopes query B j s C τ| ≤ (2 : ℚ) ^ ((Oracle.totalLevelChoice s C τ + 3) * s) := by
  apply (abs_momentQ_le scopes query B hB hj τ).trans
  apply pow_le_pow_right₀ (by norm_num)
  have hJ : Oracle.totalLevelChoice s C τ ≤ Oracle.totalLevelChoice s C τ * s := by
    simpa using Nat.mul_le_mul_left (Oracle.totalLevelChoice s C τ) hs
  nlinarith

end Paper08.BoundedRuleQ
