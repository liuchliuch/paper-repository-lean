import Paper29.IncrementMetric

noncomputable section
open scoped BigOperators Classical
namespace Paper29.Sampling

/-- Aggregate all repeated requests into the actual importance weight of each
original coordinate. Repetitions never require an additional label. -/
def importanceWeights {n m : ℕ} (π : Fin n → ℝ) (ν : Fin m → Fin n) (i : Fin n) : ℝ :=
  ∑ j, if ν j = i then 1 / ((m : ℝ) * π i) else 0

theorem importanceWeights_nonneg {n m : ℕ} (π : Fin n → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (ν : Fin m → Fin n) (i : Fin n) :
    0 ≤ importanceWeights π ν i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg m) (hπ i))
  · exact le_rfl

theorem importanceWeights_sum {n m : ℕ} (π : Fin n → ℝ) (ν : Fin m → Fin n) :
    (∑ i, importanceWeights π ν i) = ∑ j, 1 / ((m : ℝ) * π (ν j)) := by
  unfold importanceWeights
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

theorem weightedHuber_importanceWeights {n m : ℕ} (π : Fin n → ℝ)
    (ν : Fin m → Fin n) (y : Fin n → ℝ) :
    weightedHuber (importanceWeights π ν) y = sampledHuber π ν y := by
  unfold weightedHuber importanceWeights
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [sampledHuber, ProcessTools.importanceAverage_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ite_mul, zero_mul]
  simp
  ring

/-- The uniform component of the pilot distribution bounds its aggregate
weight on every realized sample, as required by Lemma3.8. -/
theorem importanceWeights_sum_le {n m : ℕ} (hn : 1 ≤ n) (hm : 0 < m)
    (π : Fin n → ℝ) (hπ : ∀ i, 0 < π i)
    (hlower : ∀ i, 1 / (2 * (n : ℝ)) ≤ π i) (ν : Fin m → Fin n) :
    (∑ i, importanceWeights π ν i) ≤ 2 * (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [importanceWeights_sum]
  have hh (j : Fin m) : 1 / ((m : ℝ) * π (ν j)) ≤ 2 * (n : ℝ) / m := by
    apply (div_le_iff₀ (mul_pos hmR (hπ (ν j)))).2
    have he := (div_le_iff₀ (by positivity : (0 : ℝ) < 2*n)).1 (hlower (ν j))
    calc
      1 ≤ π (ν j) * (2 * (n : ℝ)) := he
      _ = (2 * (n : ℝ) / m) * ((m : ℝ) * π (ν j)) := by field_simp
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hh j)
  have heq : (∑ _j : Fin m, 2 * (n : ℝ) / m) = 2 * (n : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  exact hs.trans_eq heq

end Paper29.Sampling
