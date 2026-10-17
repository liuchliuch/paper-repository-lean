import Paper29.Majority
import Paper29.GoodBlockProbability

noncomputable section
open scoped BigOperators Classical
namespace Paper29.HardDistribution

def blockLoss {N : ℕ} (y : Fin N → Bool) (t : ℝ) : ℝ := ∑ k, huber (4*(t-bit (y k)))

def singleMean {N : ℕ} (y : Fin N → Bool) : ℝ := (∑ k, bit (y k))/(N:ℝ)

theorem singleMean_bounds {N : ℕ} (hN : 0 < N) (y : Fin N → Bool) :
    0 ≤ singleMean y ∧ singleMean y ≤ 1 := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hb (b : Bool) : 0 ≤ bit b ∧ bit b ≤ 1 := by cases b <;> norm_num [bit]
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun k _ => (hb _).1)) hNR.le
  · apply (div_le_iff₀ hNR).2
    have h := Finset.sum_le_sum (s:=Finset.univ) (fun k _ => (hb (y k)).2)
    simpa using h

theorem blockLoss_majority {N : ℕ} (hN : 0 < N) (y : Fin N → Bool) (t : ℝ) :
    blockLoss y t = majorityObjective N (singleMean y-1/2) t := by
  have he (b : Bool) : huber (4*(t-bit b)) =
      (1-bit b)*huber (4*t)+bit b*huber (4*(t-1)) := by cases b <;> simp [bit]
  unfold blockLoss majorityObjective singleMean
  simp only [he, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
  ring

def blockOpt {N : ℕ} (y : Fin N → Bool) : ℝ :=
  if 1/2 < singleMean y then majorityMinimizer (singleMean y-1/2)
  else if singleMean y < 1/2 then 1-majorityMinimizer (1/2-singleMean y) else 1/2

theorem blockLoss_midpoint {N : ℕ} (y : Fin N → Bool) : blockLoss y (1/2) = (3/2:ℝ)*N := by
  have he (b : Bool) : huber (4*((1/2:ℝ)-bit b)) = 3/2 := by
    cases b <;> norm_num [bit,huber]
  simp only [blockLoss,he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem blockOpt_minimizes {N : ℕ} (hN : 0 < N) (y : Fin N → Bool) (t : ℝ) :
    blockLoss y (blockOpt y) ≤ blockLoss y t := by
  have hNR : (0:ℝ) ≤ N := Nat.cast_nonneg N
  obtain ⟨hm0,hm1⟩ := singleMean_bounds hN y
  by_cases hp : 1/2 < singleMean y
  · rw [blockOpt,if_pos hp,blockLoss_majority hN,blockLoss_majority hN]
    exact Majority.global_minimizer N _ hNR (by linarith) (by linarith) t
  · by_cases hn : singleMean y < 1/2
    · rw [blockOpt,if_neg hp,if_pos hn,blockLoss_majority hN,blockLoss_majority hN]
      have he : singleMean y-1/2 = -(1/2-singleMean y) := by ring
      rw [he]
      exact Majority.negative_global_minimizer N _ hNR (by linarith) (by linarith) t
    · have hm : singleMean y = 1/2 := by linarith
      rw [blockOpt,if_neg hp,if_neg hn,blockLoss_midpoint,blockLoss_majority hN,hm]
      have h₁ := abs_sub_half_le_huber (4*t)
      have h₂ := abs_sub_half_le_huber (4*(t-1))
      have ha := le_abs_self (4*t)
      have hb := neg_le_abs (4*(t-1))
      have hs : 3 ≤ huber (4*t)+huber (4*(t-1)) := by linarith
      have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ (N:ℝ)/2 by positivity)
      unfold majorityObjective
      norm_num
      nlinarith only [hh]

def decode (t : ℝ) : Bool := decide ((1/2:ℝ)<t)

/-- Each wrongly decoded good block pays the actual beta*N excess loss. -/
theorem good_block_wrong_gap {N : ℕ} (hN : 0 < N) (β : ℝ) (hβ : 0 < β)
    (s : Bool) (y : Fin N → Bool) (t : ℝ) (hgood : blockGood β s y) (hwrong : decode t ≠ s) :
    β*N ≤ blockLoss y t-blockLoss y (blockOpt y) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hm0,hm1⟩ := singleMean_bounds hN y
  cases s with
  | true =>
    have hg : β/2 ≤ singleMean y-1/2 := by simpa [blockGood,sign,singleMean] using hgood
    have ht : t ≤ 1/2 := by simpa [decode] using hwrong
    have hm : 1/2 < singleMean y := by linarith
    have hh := Majority.exact_scalar_majority_gap N (singleMean y-1/2) hNR
      (by linarith) (by linarith) t ht
    rw [blockLoss_majority hN,blockOpt,if_pos hm,blockLoss_majority hN]
    have hp := mul_le_mul_of_nonneg_right hg (show 0 ≤ 2*(N:ℝ) by positivity)
    nlinarith only [hh.1,hh.2,hp]
  | false =>
    have hg : β/2 ≤ 1/2-singleMean y := by
      simpa [blockGood,sign,singleMean,neg_sub] using hgood
    have ht : 1/2 ≤ t := by
      have hh : 1/2 < t := by simpa [decode] using hwrong
      exact hh.le
    have hm : singleMean y < 1/2 := by linarith
    have hh := Majority.negative_exact_scalar_majority_gap N (1/2-singleMean y) hNR
      (by linarith) (by linarith) t ht
    rw [blockLoss_majority hN,blockOpt,if_neg (by linarith),if_pos hm,blockLoss_majority hN]
    have he : singleMean y-1/2 = -(1/2-singleMean y) := by ring
    rw [he]
    have hp := mul_le_mul_of_nonneg_right hg (show 0 ≤ 2*(N:ℝ) by positivity)
    nlinarith only [hh.1,hh.2,hp]

end Paper29.HardDistribution
