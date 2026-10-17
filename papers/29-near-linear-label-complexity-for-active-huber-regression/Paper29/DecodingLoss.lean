import Paper29.BlockLoss
import Paper29.InformationDefs

noncomputable section
open scoped BigOperators Classical
namespace Paper29.HardDistribution

def productLoss {r N : ℕ} (y : Bits r N) (x : Fin r → ℝ) : ℝ :=
  ∑ j, blockLoss (fun k => y (j,k)) (x j)

def productOpt {r N : ℕ} (y : Bits r N) : Fin r → ℝ := fun j => blockOpt (fun k => y (j,k))

def wrongGoodCount {r N : ℕ} (β : ℝ) (s : Signs r) (y : Bits r N) (x : Fin r → ℝ) : ℝ :=
  ∑ j, if GoodBlock β s y j ∧ decode (x j) ≠ s j then 1 else 0

def badBlockCount {r N : ℕ} (β : ℝ) (s : Signs r) (y : Bits r N) : ℝ :=
  ∑ j, if GoodBlock β s y j then 0 else 1

theorem productOpt_minimizes {r N : ℕ} (hN : 0 < N) (y : Bits r N) (x : Fin r → ℝ) :
    productLoss y (productOpt y) ≤ productLoss y x :=
  Finset.sum_le_sum (fun j _ => blockOpt_minimizes hN _ _)

theorem productLoss_midpoint {r N : ℕ} (y : Bits r N) :
    productLoss y (fun _ => 1/2) = (3/2:ℝ)*N*r := by
  simp only [productLoss,blockLoss_midpoint,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  ring

theorem good_wrong_count_excess {r N : ℕ} (hN : 0 < N) (β : ℝ) (hβ : 0 < β)
    (s : Signs r) (y : Bits r N) (x : Fin r → ℝ) :
    β*N*wrongGoodCount β s y x ≤ productLoss y x-productLoss y (productOpt y) := by
  unfold wrongGoodCount productLoss
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : GoodBlock β s y j ∧ decode (x j) ≠ s j
  · simp only [if_pos hj,mul_one]
    exact good_block_wrong_gap hN β hβ (s j) (fun k => y (j,k)) (x j) hj.1 hj.2
  · simp only [if_neg hj,mul_zero]
    exact sub_nonneg.mpr (blockOpt_minimizes hN _ _)

/-- Quantitative wrong-good-block count on any successful regression output. -/
theorem successful_wrong_good_count {r N : ℕ} (hN : 0 < N) (β ε : ℝ)
    (hβ : 0 < β) (hε : 0 ≤ ε) (hεhi : ε ≤ 1) (hscale : 200*ε ≤ β)
    (s : Signs r) (y : Bits r N) (x : Fin r → ℝ)
    (hgood : Real.sqrt (productLoss y x) ≤ (1+ε)*Real.sqrt (productLoss y (productOpt y))) :
    wrongGoodCount β s y x ≤ (9/400:ℝ)*r := by
  have hNpos : (0:ℝ)<N := by exact_mod_cast hN
  have hopt0 : 0 ≤ productLoss y (productOpt y) :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => huber_nonneg _))
  have hx0 : 0 ≤ productLoss y x :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => huber_nonneg _))
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).2 hgood
  rw [Real.sq_sqrt hx0,mul_pow,Real.sq_sqrt hopt0] at hs
  have hopt := productOpt_minimizes hN y (fun _ => 1/2)
  rw [productLoss_midpoint] at hopt
  have hcoef : 2*ε+ε^2 ≤ 3*ε := by nlinarith [mul_nonneg hε (sub_nonneg.mpr hεhi)]
  have herr : productLoss y x-productLoss y (productOpt y) ≤ (9/2:ℝ)*ε*N*r := by
    have h₁ := mul_le_mul_of_nonneg_right hcoef hopt0
    have h₂ := mul_le_mul_of_nonneg_left hopt (show 0 ≤ 3*ε by positivity)
    nlinarith only [hs,h₁,h₂]
  have hcount := good_wrong_count_excess hN β hβ s y x
  have hbound : β*N*wrongGoodCount β s y x ≤ β*N*((9/400:ℝ)*r) := by
    have hp := mul_le_mul_of_nonneg_right hscale (show 0 ≤ (9/400:ℝ)*N*r by positivity)
    nlinarith only [hcount,herr,hp]
  exact (mul_le_mul_iff_right₀ (mul_pos hβ hNpos)).mp hbound

/-- Hamming errors split pointwise into nongood blocks and wrongly decoded good
blocks. Failure probability is accounted for separately, not hidden here. -/
theorem hamming_le_bad_add_wrong {r N : ℕ} (β : ℝ) (s : Signs r) (y : Bits r N) (x : Fin r → ℝ) :
    RateDistortion.hamming s (fun j => decode (x j)) ≤ badBlockCount β s y + wrongGoodCount β s y x := by
  unfold RateDistortion.hamming badBlockCount wrongGoodCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  by_cases hg : GoodBlock β s y j <;> by_cases hd : decode (x j) = s j <;> simp [hg,hd,eq_comm]
  all_goals split_ifs <;> norm_num

end Paper29.HardDistribution
