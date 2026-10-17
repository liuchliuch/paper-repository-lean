/-
Copyright (c) 2026. Finite Markov kernels and the total-variation bridges
used in Appendix A. These results do not assert the missing spectral
representation or construction of the heat-bath semigroup.
-/
import Paper09.Dynamics
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open Finset BigOperators Classical Real

noncomputable section

namespace Paper09

variable {α : Type*} [Fintype α]

theorem tvDist_nonneg (μ ν : FinProb α) : 0 ≤ tvDist μ ν := by
  exact mul_nonneg (by norm_num) (sum_nonneg fun _ _ => abs_nonneg _)

@[simp] theorem tvDist_self (μ : FinProb α) : tvDist μ μ = 0 := by
  simp [tvDist]

theorem tvDist_comm (μ ν : FinProb α) : tvDist μ ν = tvDist ν μ := by
  simp only [tvDist, abs_sub_comm]

theorem tvDist_triangle (μ ν ξ : FinProb α) :
    tvDist μ ξ ≤ tvDist μ ν + tvDist ν ξ := by
  unfold tvDist
  rw [← mul_add, ← sum_add_distrib]
  exact mul_le_mul_of_nonneg_left
    (sum_le_sum fun x _ => abs_sub_le (μ.w x) (ν.w x) (ξ.w x)) (by norm_num)

theorem tvDist_le_one (μ ν : FinProb α) : tvDist μ ν ≤ 1 := by
  have h : ∑ x, |μ.w x - ν.w x| ≤ 2 := by
    calc
      ∑ x, |μ.w x - ν.w x| ≤ ∑ x, (μ.w x + ν.w x) := by
        apply sum_le_sum
        intro x _
        rw [abs_le]
        constructor <;> linarith [μ.nonneg x, ν.nonneg x]
      _ = 2 := by rw [sum_add_distrib, μ.sum_one, ν.sum_one]; norm_num
  unfold tvDist
  linarith

/-- The dual estimate used in the eigenfunction lower bound of Appendix A.1. -/
theorem abs_expect_sub_le_two_tv (μ ν : FinProb α) (f : α → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    |FinProb.expect μ f - FinProb.expect ν f| ≤ 2 * tvDist μ ν := by
  have he : FinProb.expect μ f - FinProb.expect ν f =
      ∑ x, (μ.w x - ν.w x) * f x := by
    simp only [FinProb.expect, sub_mul, sum_sub_distrib]
  rw [he]
  calc
    |∑ x, (μ.w x - ν.w x) * f x|
      ≤ ∑ x, |(μ.w x - ν.w x) * f x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |μ.w x - ν.w x| := by
      apply sum_le_sum
      intro x _
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_left (hf x) (abs_nonneg (μ.w x - ν.w x))
    _ = 2 * tvDist μ ν := by unfold tvDist; ring

/-- A finite stochastic kernel: each row is a probability law. -/
abbrev MarkovKernel (α : Type*) [Fintype α] := α → FinProb α

namespace MarkovKernel

/-- The law obtained by sampling `x ~ μ` and then taking one `K(x, ·)` step. -/
def push (K : MarkovKernel α) (μ : FinProb α) : FinProb α where
  w y := ∑ x, μ.w x * (K x).w y
  nonneg y := sum_nonneg fun x _ => mul_nonneg (μ.nonneg x) ((K x).nonneg y)
  sum_one := by
    rw [sum_comm]
    simp_rw [← mul_sum, FinProb.sum_one, mul_one]
    exact μ.sum_one

/-- The action of a kernel on a statistic. -/
def act (K : MarkovKernel α) (f : α → ℝ) (x : α) : ℝ :=
  FinProb.expect (K x) f

/-- Stationarity is equality of the pushed probability weights. -/
def Stationary (K : MarkovKernel α) (p : FinProb α) : Prop :=
  ∀ y, (push K p).w y = p.w y

/-- Detailed balance is an algebraic relation on the actual transition weights. -/
def Reversible (K : MarkovKernel α) (p : FinProb α) : Prop :=
  ∀ x y, p.w x * (K x).w y = p.w y * (K y).w x

theorem stationary_of_reversible (K : MarkovKernel α) (p : FinProb α)
    (h : Reversible K p) : Stationary K p := by
  intro y
  change (∑ x, p.w x * (K x).w y) = p.w y
  calc
    (∑ x, p.w x * (K x).w y) = ∑ x, p.w y * (K y).w x :=
      sum_congr rfl (fun x _ => h x y)
    _ = p.w y := by rw [← mul_sum, (K y).sum_one, mul_one]

/-- A genuine Markov step contracts total variation. -/
theorem tvDist_push_le (K : MarkovKernel α) (μ ν : FinProb α) :
    tvDist (push K μ) (push K ν) ≤ tvDist μ ν := by
  have he (y : α) : (push K μ).w y - (push K ν).w y =
      ∑ x, (μ.w x - ν.w x) * (K x).w y := by
    simp only [push, sub_mul, sum_sub_distrib]
  unfold tvDist
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    ∑ y, |(push K μ).w y - (push K ν).w y|
      ≤ ∑ y, ∑ x, |μ.w x - ν.w x| * (K x).w y := by
        apply sum_le_sum
        intro y _
        rw [he]
        calc
          |∑ x, (μ.w x - ν.w x) * (K x).w y|
            ≤ ∑ x, |(μ.w x - ν.w x) * (K x).w y| := abs_sum_le_sum_abs _ _
          _ = ∑ x, |μ.w x - ν.w x| * (K x).w y := by
            simp_rw [abs_mul, abs_of_nonneg ((K _).nonneg _)]
    _ = ∑ x, |μ.w x - ν.w x| := by
      rw [sum_comm]
      simp_rw [← mul_sum, FinProb.sum_one, mul_one]

theorem tvDist_to_stationary_le (K : MarkovKernel α) (μ p : FinProb α)
    (hp : Stationary K p) : tvDist (push K μ) p ≤ tvDist μ p := by
  have he : tvDist (push K μ) p = tvDist (push K μ) (push K p) := by
    unfold tvDist
    change ∀ y, (push K p).w y = p.w y at hp
    simp only [hp]
  rw [he]
  exact tvDist_push_le K μ p

/-- Reversibility turns the row density into the evolution of a point density. -/
theorem reversible_row_density (K : MarkovKernel α) (p : FinProb α)
    (hp : ∀ x, 0 < p.w x) (hK : Reversible K p) (x y : α) :
    (K x).w y / p.w y = (K y).w x / p.w x := by
  apply (div_eq_div_iff (ne_of_gt (hp y)) (ne_of_gt (hp x))).mpr
  simpa [mul_comm] using hK x y

/-- Finite Jensen inequality, proved from the variance identity. -/
theorem act_sq_le (K : MarkovKernel α) (f : α → ℝ) (x : α) :
    (act K f x) ^ 2 ≤ act K (fun y => (f y) ^ 2) x := by
  let m := FinProb.expect (K x) f
  have halg (y : α) : (f y - m) * (f y - m) =
      (f y) ^ 2 - 2 * m * f y + m ^ 2 := by ring
  have hv : FinProb.variance (K x) f =
      FinProb.expect (K x) (fun y => (f y) ^ 2) - m ^ 2 := by
    unfold FinProb.variance
    change FinProb.expect (K x) (fun y => (f y - m) * (f y - m)) = _
    simp_rw [halg]
    rw [FinProb.expect_add, FinProb.expect_sub, FinProb.expect_smul,
      FinProb.expect_const]
    change FinProb.expect (K x) (fun y => (f y) ^ 2) - 2 * m * m + m ^ 2 = _
    ring
  have hn := FinProb.variance_nonneg (K x) f
  rw [hv] at hn
  dsimp [act, m]
  dsimp [m] at hn
  linarith

/-- An invariant Markov kernel is an `L²` contraction; this is derived from
its rows and stationarity, rather than stored as an assumed certificate. -/
theorem l2_contraction (K : MarkovKernel α) (p : FinProb α)
    (hp : Stationary K p) (f : α → ℝ) :
    FinProb.expect p (fun x => (act K f x) ^ 2) ≤
      FinProb.expect p (fun x => (f x) ^ 2) := by
  calc
    FinProb.expect p (fun x => (act K f x) ^ 2) ≤
        FinProb.expect p (act K (fun y => (f y) ^ 2)) :=
      FinProb.expect_mono (act_sq_le K f)
    _ = FinProb.expect p (fun y => (f y) ^ 2) := by
      unfold FinProb.expect act
      simp_rw [FinProb.expect, mul_sum]
      rw [sum_comm]
      change (∑ y, ∑ x, p.w x * ((K x).w y * (f y) ^ 2)) = _
      have he (y : α) : (∑ x, p.w x * ((K x).w y * (f y) ^ 2)) =
          (push K p).w y * (f y) ^ 2 := by
        dsimp [push]
        rw [sum_mul]
        apply sum_congr rfl
        intro x _
        ring
      change ∀ y, (push K p).w y = p.w y at hp
      simp only [he, hp]

end MarkovKernel

/-- Pearson's squared `L²(p)` density distance. Strictly positive `p` is
required by the bounds below rather than silently assumed in this definition. -/
def chiSquare (μ p : FinProb α) : ℝ :=
  ∑ x, (μ.w x - p.w x) ^ 2 / p.w x

theorem chiSquare_nonneg (μ p : FinProb α) : 0 ≤ chiSquare μ p := by
  exact sum_nonneg fun x _ => div_nonneg (sq_nonneg _) (p.nonneg x)

/-- The Cauchy–Schwarz step in Appendix A.1, with its exact factor `1/4`. -/
theorem tvDist_sq_le_chiSquare (μ p : FinProb α) (hp : ∀ x, 0 < p.w x) :
    (tvDist μ p) ^ 2 ≤ chiSquare μ p / 4 := by
  have h := sq_sum_div_le_sum_sq_div (univ : Finset α)
    (fun x => |μ.w x - p.w x|) (fun x _ => hp x)
  simp only [p.sum_one, div_one, sq_abs] at h
  unfold tvDist chiSquare
  nlinarith

/-- The exact `L²` norm of a point density minus one. -/
theorem point_density_sq (p : FinProb α) (hp : ∀ x, 0 < p.w x) (x : α) :
    (∑ y, p.w y * ((if y = x then 1 / p.w x else 0) - 1) ^ 2) =
      1 / p.w x - 1 := by
  have hsum : ∑ y, p.w y * ((if y = x then 1 / p.w x else 0) - 1) ^ 2 =
      ∑ y, (p.w y + if y = x then 1 / p.w x - 2 else 0) := by
    apply sum_congr rfl
    intro y _
    split_ifs with h
    · subst y
      field_simp [ne_of_gt (hp x)]
      <;> ring
    · ring
  rw [hsum, sum_add_distrib, p.sum_one]
  simp
  <;> ring

end Paper09
