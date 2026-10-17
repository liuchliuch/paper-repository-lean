/-
Copyright (c) 2026. From local simulated-kernel contraction and actual
continuous-time censoring to worst-start heat-bath mixing.
-/
import Paper09.Censoring
import Paper09.OrderMixing
import Paper09.MixingTimes
import Paper09.UpperScale

open Finset BigOperators Classical Real Matrix

noncomputable section
namespace Paper09.CensoredMixing

variable {V : Type*} [Fintype V]

/-- The two independently introduced finite-kernel push operations have the
same actual probability weights. -/
theorem push_eq_bind (K : Config V → FinProb (Config V)) (α : FinProb (Config V)) :
    MarkovKernel.push K α = α.bind K := by
  apply Censoring.law_ext
  intro η
  rfl

/-- The actual averaged censored stages equal iteration of their actual kernel. -/
theorem colorRun_eq_evolve {Ω : Type*} [Fintype Ω]
    (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) (q : FinProb Ω)
    (blocks : Ω → Finset V) (T : ℝ) (α : FinProb (Config V)) (k : ℕ) :
    Censoring.colorRun p hp q blocks T α k =
      FinProb.evolve (Censoring.colorKernel p hp q blocks T) k α := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Censoring.colorRun, Censoring.colorStep_kernel, push_eq_bind, ih]
    rfl

/-- The extremal transport estimate is derived from the actual one-discrepancy
kernel inequality by the proved path and distribution coupling theorems. -/
theorem extreme_transport_le {Ω : Type*} [Fintype Ω]
    (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η) (q : FinProb Ω)
    (blocks : Ω → Finset V) (T a : ℝ) (ha : 0 ≤ a)
    (hstep : ∀ η ξ, hamming η ξ = 1 →
      hammingWasserstein (Censoring.colorKernel p hp q blocks T η)
        (Censoring.colorKernel p hp q blocks T ξ) ≤ a)
    (k : ℕ) :
    hammingWasserstein (Censoring.colorRun p hp q blocks T (Censoring.dirac ⊥) k)
      (Censoring.colorRun p hp q blocks T (Censoring.dirac ⊤) k) ≤
        (Fintype.card V : ℝ) * a^k := by
  rw [colorRun_eq_evolve, colorRun_eq_evolve]
  have hh := hamming_path_coupling_iterate (Censoring.colorKernel p hp q blocks T)
    a ha hstep (Censoring.dirac ⊥) (Censoring.dirac ⊤) k
  exact hh.trans (by
    have hd := mul_le_mul_of_nonneg_left
      (hammingWasserstein_le_card (Censoring.dirac (⊥ : Config V)) (Censoring.dirac ⊤))
      (pow_nonneg ha k)
    simpa only [mul_comm] using hd)

/-- Integer-rounded contraction time, retaining the precise ceiling and the
paper's factor `16N`. -/
theorem rounded_contraction (C M N c : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hc : 0 < c) (hCc : 1 ≤ C*c) (hratio : c/M ≤ 1) :
    N * (1-c/M) ^ UpperScale.stepCount C M N ≤ 1/16 := by
  let k := UpperScale.stepCount C M N
  have hMp : 0 < M := by linarith
  have hNp : 0 < N := by linarith
  have hr : 0 < c/M := div_pos hc hMp
  have hbase : 0 ≤ 1-c/M := sub_nonneg.mpr hratio
  have hlog : 0 < Real.log (16*N) := Real.log_pos (by nlinarith)
  have hk : C*M*Real.log (16*N) ≤ (k : ℝ) := Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_right hk hr.le
  have hcancel : C*M*Real.log (16*N)*(c/M) = (C*c)*Real.log (16*N) := by
    field_simp [ne_of_gt hMp]
    <;> ring
  rw [hcancel] at hmul
  have hkg : Real.log (16*N) ≤ (k : ℝ)*(c/M) := by
    have hh := mul_le_mul_of_nonneg_right hCc hlog.le
    nlinarith only [hmul, hh]
  have hpow : (1-c/M)^k ≤ Real.exp (-(k : ℝ)*(c/M)) := by
    have hh : 1-c/M ≤ Real.exp (-(c/M)) := by
      linarith only [Real.add_one_le_exp (-(c/M))]
    have hh' := pow_le_pow_left₀ hbase hh k
    rw [← Real.exp_nat_mul] at hh'
    simpa only [mul_neg, neg_mul] using hh'
  have hbound : Real.exp (-(k : ℝ)*(c/M)) ≤ 1/(16*N) := by
    calc
      _ ≤ Real.exp (-Real.log (16*N)) := Real.exp_le_exp.mpr (by linarith)
      _ = 1/(16*N) := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
  have hh := mul_le_mul_of_nonneg_left (hpow.trans hbound) hNp.le
  have he : N*(1/(16*N)) = (1/16 : ℝ) := by field_simp [ne_of_gt hNp]
  rw [he] at hh
  exact hh

/-- Actual heat-bath transition laws preserve the stationary law. -/
theorem heatBath_stationary (p : FinProb (Config V)) (t : ℝ) :
    p.bind (heatBathTransition p t) = p := by
  apply Censoring.law_ext
  intro η
  exact heatBathTransition_stationary p t η

/-- Attractiveness of the actual full heat-bath semigroup follows from the
proved local conditional monotonicity and positive exponential series. -/
theorem heatBath_attractive (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (hq : ∀ x, Monotone (Censoring.plusProbability p x)) (t : ℝ) (ht : 0 ≤ t) :
    ∀ η ξ, η ≤ ξ → OrderMixing.StochLE (heatBathTransition p t η) (heatBathTransition p t ξ) := by
  intro η ξ hηξ f hf
  have hh := Censoring.siteSemigroup_monotone p hp hq univ t ht f hf hηξ
  rw [Censoring.siteSemigroup_univ] at hh
  change (∑ ζ, (heatBathTransition p t η).w ζ * f ζ) ≤
    ∑ ζ, (heatBathTransition p t ξ).w ζ * f ζ
  simp only [heatBathTransition_w p t ht]
  exact hh

/-- Censoring transfers the actual simulated color-kernel contraction to a
uniform TV bound for the actual full rate-one heat-bath chain. The only local
analytic input is the one-discrepancy contraction still to be instantiated
from the block influence and simulation proofs. -/
theorem worst_start_from_one_site {Ω : Type*} [Fintype Ω]
    (Λ : Lattice V) (h : V → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset V) (φ : Config V) (q : FinProb Ω) (blocks : Ω → Finset V)
    (T : ℝ) (hT : 0 ≤ T) (C M N c : ℝ)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hcard : (Fintype.card V : ℝ) ≤ N)
    (hc : 0 < c) (hCc : 1 ≤ C*c) (hratio : c/M ≤ 1)
    (hstep : ∀ η ξ, hamming η ξ = 1 →
      hammingWasserstein
        (Censoring.colorKernel (gibbs Λ h β univ S φ) (Censoring.gibbs_positive Λ h β S φ) q blocks T η)
        (Censoring.colorKernel (gibbs Λ h β univ S φ) (Censoring.gibbs_positive Λ h β S φ) q blocks T ξ)
        ≤ 1-c/M) :
    let p := gibbs Λ h β univ S φ
    let k := UpperScale.stepCount C M N
    ∀ η, tvDist (heatBathTransition p ((k : ℝ)*T) η) p ≤ 1/8 := by
  dsimp only
  let p := gibbs Λ h β univ S φ
  let hp := Censoring.gibbs_positive Λ h β S φ
  let k := UpperScale.stepCount C M N
  let l := Censoring.colorRun p hp q blocks T (Censoring.dirac ⊥) k
  let u := Censoring.colorRun p hp q blocks T (Censoring.dirac ⊤) k
  have ha : 0 ≤ 1-c/M := sub_nonneg.mpr hratio
  have hW : hammingWasserstein l u ≤ 1/16 := by
    have hh := extreme_transport_le p hp q blocks T (1-c/M) ha hstep k
    have hdiam := mul_le_mul_of_nonneg_right hcard (pow_nonneg ha k)
    exact hh.trans (hdiam.trans (rounded_contraction C M N c hM hN hc hCc hratio))
  have hs := Censoring.ising_ct_censoring_colors Λ h β hβ S φ q blocks T hT k
  have ht : 0 ≤ (k : ℝ)*T := mul_nonneg (Nat.cast_nonneg _) hT
  have hq (x : V) : Monotone (Censoring.plusProbability p x) :=
    Censoring.gibbs_plusProbability_monotone Λ h β hβ S φ x
  have hh := OrderMixing.worst_start_tv_from_censoring
    (heatBathTransition p ((k : ℝ)*T)) p l u
    (heatBath_stationary p _) (heatBath_attractive p hp hq _ ht) hs.1 hs.2.2
  intro η
  exact (hh η).trans (by linarith only [hW])

/-- Actual `t_mix(1/4)` is at most the rounded number of physical color-stage
intervals, derived from local simulated-kernel contraction and censoring. -/
theorem mixingTime_from_one_site {Ω : Type*} [Fintype Ω]
    (Λ : Lattice V) (h : V → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset V) (φ : Config V) (q : FinProb Ω) (blocks : Ω → Finset V)
    (T : ℝ) (hT : 0 ≤ T) (C M N c : ℝ)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hcard : (Fintype.card V : ℝ) ≤ N)
    (hc : 0 < c) (hCc : 1 ≤ C*c) (hratio : c/M ≤ 1)
    (hstep : ∀ η ξ, hamming η ξ = 1 →
      hammingWasserstein
        (Censoring.colorKernel (gibbs Λ h β univ S φ) (Censoring.gibbs_positive Λ h β S φ) q blocks T η)
        (Censoring.colorKernel (gibbs Λ h β univ S φ) (Censoring.gibbs_positive Λ h β S φ) q blocks T ξ)
        ≤ 1-c/M) :
    let p := gibbs Λ h β univ S φ
    tMix p (heatBathTransition p) (1/4) ≤ (UpperScale.stepCount C M N : ℝ)*T := by
  dsimp only
  apply tMix_le _ _ (mul_nonneg (Nat.cast_nonneg _) hT)
  intro η
  have hh := worst_start_from_one_site Λ h β hβ S φ q blocks T hT C M N c
    hM hN hcard hc hCc hratio hstep η
  exact hh.trans (by norm_num)

end Paper09.CensoredMixing
