import Paper29.ExternalCovering
import Paper29.ScaleBookkeeping

noncomputable section
open scoped BigOperators Classical ENNReal
namespace Paper29.Chaining
open WeightConstruction ExternalCovering ProcessTools

/-- Summing a finite window gives a valid score witness with the same mass
order as its coordinatewise maximum. It is a finite design-only construction. -/
def windowScore {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (s : Finset ℤ)
    (w : ℤ → PositiveWeights n) (i : Fin n) : ℝ :=
  ∑ j ∈ s, Leverage.leverage A (w j) i

theorem leverage_pos {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : A.rank = d) (hrows : ∀ i, A i ≠ 0) (w : PositiveWeights n) (i : Fin n) :
    0 < Leverage.leverage A w i :=
  mul_pos (w.property i) (Leverage.radiusSq_pos A w
    (Leverage.mulVec_injective_of_rank_eq A hA) w.property i (hrows i))

theorem maxScore_pos {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : A.rank = d) (hrows : ∀ i, A i ≠ 0) (s : Finset ℤ) (hs : s.Nonempty)
    (w : ℤ → PositiveWeights n) (i : Fin n) : 0 < maxScore A s w i := by
  obtain ⟨j, hj⟩ := hs
  exact (leverage_pos A hA hrows (w j) i).trans_le
    (le_supremum (fun k : {k : ℤ // k ∈ s} => Leverage.leverage A (w k) i)
      ((Set.finite_range _).bddAbove) ⟨j,hj⟩)

theorem windowScore_nonneg {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : A.rank = d) (s : Finset ℤ) (w : ℤ → PositiveWeights n) (i : Fin n) :
    0 ≤ windowScore A s w i := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg ((w j).property i).le (Leverage.radiusSq_nonneg A (w j)
    (Leverage.mulVec_injective_of_rank_eq A hA) (w j).property i)

theorem maxScore_le_window {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : A.rank = d) (s t : Finset ℤ) (hs : s.Nonempty) (hst : s ⊆ t)
    (w : ℤ → PositiveWeights n) (i : Fin n) : maxScore A s w i ≤ windowScore A t w i := by
  haveI : Nonempty {j : ℤ // j ∈ s} := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  apply supremum_le
  intro j
  exact Finset.single_le_sum (fun k _ => mul_nonneg ((w k).property i).le
    (Leverage.radiusSq_nonneg A (w k) (Leverage.mulVec_injective_of_rank_eq A hA)
      (w k).property i)) (hst j.property)

theorem windowScore_mass {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : A.rank = d) (s : Finset ℤ) (w : ℤ → PositiveWeights n) :
    (∑ i, windowScore A s w i) = (s.card : ℝ) * d := by
  unfold windowScore
  rw [Finset.sum_comm]
  simp only [Leverage.leverage_sum_of_rank_eq A _ hA (fun i => (w _).property i),
    Finset.sum_const, nsmul_eq_mul]

/-- The own transition-radius argument: one constructed finite window covers
every middle Huber radius through a verified contiguous subinterval. -/
theorem transition_radius_cover {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : A.rank = d) (hrows : ∀ i, A i ≠ 0)
    (scheme : HuberScheme A (-2-(transitionLength n:ℤ)) (2+transitionTop n) 4)
    (τ : Fin n → ℝ) (hdom : ∀ i, windowScore A (transitionScales n) scheme.w i ≤ τ i)
    (C : ℝ) (hC : 0 ≤ C) (external : HuberPrimitive 4 C)
    {R : ℝ} (hlo : 1/2 ≤ R) (hhi : R ≤ (n:ℝ)/2) :
    gamma2 (T := Ball A R) (fun h k => huberMetric A τ h k) ≤
      ENNReal.ofReal (2*C*ProcessTools.logFactor n*Real.sqrt R) := by
  let k : ℤ := ⌈Real.logb 2 R⌉
  let a : ℤ := k-(transitionLength n:ℤ)
  let b : ℤ := k-1
  have hR : 0 < R := by linarith
  have hab : a ≤ b := by have hh := transitionLength_pos n; dsimp [a,b]; omega
  have hs : (Finset.Icc a b).Nonempty := Finset.nonempty_Icc.mpr hab
  have hsub : Finset.Icc a b ⊆ transitionScales n := radiusBlock_subset hlo hhi
  let sub : HuberScheme A a b 4 := ⟨scheme.w,
    (fun j hj i => scheme.normalized j (hsub hj) i),
    (fun j hj hj' i => scheme.step j (hsub hj) (hsub hj') i)⟩
  have hcard : 4*Real.log (2*(n:ℝ)) ≤ ((Finset.Icc a b).card : ℝ) := by
    change _ ≤ ((radiusBlock n R).card : ℝ)
    rw [radiusBlock_card]
    exact transitionLength_large n
  have raw := external n d A hA hrows a b hab hcard sub
  have hb : b+1 = k := by dsimp [b]; omega
  rw [hb] at raw
  have hscore (i) : maxScore A (Finset.Icc a b) scheme.w i ≤ τ i :=
    (maxScore_le_window A hA _ _ hs hsub scheme.w i).trans (hdom i)
  let f : Ball A R → Ball A ((2:ℝ)^k) := fun h =>
    ⟨h, h.property.trans (dyadic_ceiling hR).1⟩
  have hmono := gamma2_pullback f (fun x y => huberMetric A τ x y)
    (fun x y => huberMetric A (maxScore A (Finset.Icc a b) scheme.w) x y)
    (fun x y => huberMetric_antitone A _ _ (maxScore_pos A hA hrows _ hs scheme.w) hscore x y)
  apply (hmono.trans raw).trans
  apply ENNReal.ofReal_le_ofReal
  have hroot : Real.sqrt ((2:ℝ)^k) ≤ 2*Real.sqrt R := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
    rw [Real.sq_sqrt (zpow_pos (by norm_num) k).le, mul_pow, Real.sq_sqrt hR.le]
    have hh := (dyadic_ceiling hR).2
    change (2:ℝ)^k < 2*R at hh
    nlinarith
  have hn : 1 ≤ n := by
    have hnR : (1:ℝ) ≤ n := by linarith
    exact_mod_cast hnR
  have hlog := (ProcessTools.logFactor_pos hn).le
  nlinarith [mul_le_mul_of_nonneg_left hroot (mul_nonneg hC hlog)]

end Paper29.Chaining
