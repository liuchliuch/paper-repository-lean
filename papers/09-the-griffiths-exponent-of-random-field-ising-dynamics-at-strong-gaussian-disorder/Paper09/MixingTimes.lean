/-
Copyright (c) 2026. Actual relaxation and total-variation mixing estimates
for the rate-one heat-bath semigroup (Appendix A.1).
-/
import Paper09.SpectralMixing
import Paper09.CanonicalPath

open Finset BigOperators Classical Matrix Real

noncomputable section
namespace Paper09

variable {V : Type*} [Fintype V]

/-- The actual gap is strictly positive for a full-support law on a nonempty
spin system; connectivity is established by the ordered configuration paths. -/
theorem heatBath_gap_pos (p : FinProb (Config V)) (hp : ∀ a, 0 < p.w a) (x : V) :
    0 < spectralGap p := by
  by_contra h
  have hgap : spectralGap p = 0 :=
    le_antisymm (le_of_not_gt h) (spectralGap_nonneg p)
  obtain ⟨f, hf, hv, he⟩ := SpectralMixing.gap_attained p hp x
  rw [hgap, zero_mul] at he
  have hn (a b : Config V) : 0 ≤
      (if oneSite a b then conductance p a b * (f a - f b)^2 else 0) := by
    split_ifs
    · exact mul_nonneg (conductance_nonneg p a b) (sq_nonneg _)
    · exact le_rfl
  have hsum : (∑ a : Config V, ∑ b : Config V,
      if oneSite a b then conductance p a b * (f a - f b)^2 else 0) = 0 := by
    change (1 / 2 : ℝ) * (∑ a : Config V, ∑ b : Config V,
      if oneSite a b then conductance p a b * (f a - f b)^2 else 0) = 0 at he
    linarith
  have hedge (a b : Config V) (hab : oneSite a b) : f a = f b := by
    have h1 := single_le_sum (fun b (_ : b ∈ (univ : Finset (Config V))) => hn a b)
      (mem_univ b)
    have h2 : (∑ b : Config V, if oneSite a b then conductance p a b * (f a - f b)^2 else 0) ≤
        ∑ a : Config V, ∑ b : Config V,
          if oneSite a b then conductance p a b * (f a - f b)^2 else 0 :=
      single_le_sum (fun a _ => sum_nonneg fun b _ => hn a b) (mem_univ a)
    rw [hsum] at h2
    rw [if_pos hab] at h1
    have hc : 0 < conductance p a b :=
      div_pos (mul_pos (hp a) (hp b)) (add_pos (hp a) (hp b))
    have hs : (f a - f b)^2 = 0 := by
      have hle : conductance p a b * (f a - f b)^2 ≤ 0 := h1.trans h2
      nlinarith [sq_nonneg (f a - f b)]
    nlinarith [sq_nonneg (f a - f b)]
  have hconstant (a b : Config V) : f a = f b := by
    let order : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
    have ht := CanonicalPath.telescope_bound order a b f
    have hz (k : Fin (Fintype.card V)) :
        f (CanonicalPath.hybrid (CanonicalPath.initialSegment order k.val) a b) -
          f (CanonicalPath.hybrid (CanonicalPath.initialSegment order (k.val + 1)) a b) = 0 := by
      by_cases hh : CanonicalPath.hybrid (CanonicalPath.initialSegment order k.val) a b =
          CanonicalPath.hybrid (CanonicalPath.initialSegment order (k.val + 1)) a b
      · rw [hh, sub_self]
      · have hs := CanonicalPath.path_step_siteEdge order k a b hh
        exact sub_eq_zero.mpr (hedge _ _ ⟨order k, hs⟩)
    simp only [hz, zero_pow (by omega : 2 ≠ 0), sum_const_zero, mul_zero] at ht
    nlinarith [sq_nonneg (f a - f b)]
  have hfconst : f = fun _ => f (fun _ => 0) := funext fun a => hconstant a _
  rw [hfconst] at hv
  simp [FinProb.variance, FinProb.expect_const] at hv

/-- An actual minimum-weight state, chosen from the finite state space. -/
def minimumWeightState (p : FinProb (Config V)) : Config V :=
  (univ.exists_min_image p.w univ_nonempty).choose

def minimumWeight (p : FinProb (Config V)) : ℝ := p.w (minimumWeightState p)

theorem minimumWeight_le (p : FinProb (Config V)) (a : Config V) : minimumWeight p ≤ p.w a := by
  exact (univ.exists_min_image p.w univ_nonempty).choose_spec.2 a (mem_univ a)

theorem minimumWeight_pos (p : FinProb (Config V)) (hp : ∀ a, 0 < p.w a) :
    0 < minimumWeight p := hp _

theorem weight_le_one (p : FinProb (Config V)) (a : Config V) : p.w a ≤ 1 := by
  simpa only [p.sum_one] using single_le_sum (fun b _ => p.nonneg b) (mem_univ a)

theorem minimumWeight_le_one (p : FinProb (Config V)) : minimumWeight p ≤ 1 :=
  weight_le_one p _

/-- The mean-zero density of a point mass relative to the actual stationary law. -/
def pointDensity (p : FinProb (Config V)) (x : Config V) (y : Config V) : ℝ :=
  (if y = x then 1 / p.w x else 0) - 1

theorem pointDensity_mean (p : FinProb (Config V)) (hp : ∀ a, 0 < p.w a) (x : Config V) :
    p.expect (pointDensity p x) = 0 := by
  classical
  unfold pointDensity
  rw [FinProb.expect_sub, FinProb.expect_const]
  unfold FinProb.expect
  simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
  field_simp [ne_of_gt (hp x)]
  <;> ring

/-- Detailed balance identifies the evolved point density with the row density. -/
theorem pointDensity_evolved (p : FinProb (Config V)) (hp : ∀ a, 0 < p.w a)
    (t : ℝ) (x y : Config V) :
    (heatBathSemigroup p t *ᵥ pointDensity p x) y =
      heatBathSemigroup p t x y / p.w y - 1 := by
  classical
  unfold pointDensity Matrix.mulVec dotProduct
  simp only [mul_sub, sum_sub_distrib, mul_one, heatBathSemigroup_rows,
    mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
  congr 1
  rw [mul_one_div]
  apply (div_eq_div_iff (ne_of_gt (hp x)) (ne_of_gt (hp y))).mpr
  simpa [mul_comm] using (heatBathSemigroup_reversible p t x y).symm

/-- Exact density-square identity for the actual transition law. -/
theorem heatBath_chiSquare_eq (p : FinProb (Config V)) (hp : ∀ a, 0 < p.w a)
    (t : ℝ) (ht : 0 ≤ t) (x : Config V) :
    chiSquare (heatBathTransition p t x) p =
      ∑ y, p.w y * ((heatBathSemigroup p t *ᵥ pointDensity p x) y)^2 := by
  unfold chiSquare
  apply sum_congr rfl
  intro y _
  rw [heatBathTransition_w p t ht, pointDensity_evolved p hp]
  field_simp [ne_of_gt (hp y)]

/-- The actual `L²` decay and the exact initial density give the chain's
chi-square estimate, with no mixing or spectral-decay hypothesis. -/
theorem heatBath_chiSquare_le (p : FinProb (Config V)) (hp : ∀ a, 0 < p.w a)
    (t : ℝ) (ht : 0 ≤ t) (x : Config V) :
    chiSquare (heatBathTransition p t x) p ≤
      Real.exp (-2 * spectralGap p * t) * (1 / p.w x - 1) := by
  rw [heatBath_chiSquare_eq p hp t ht]
  have hh := SpectralMixing.weighted_l2_decay p (pointDensity p x)
    (pointDensity_mean p hp x) t ht
  have hnorm : (∑ y, p.w y * (pointDensity p x y)^2) = 1 / p.w x - 1 := by
    convert point_density_sq p hp x using 1
    apply sum_congr rfl
    intro y _
    unfold pointDensity
    by_cases hh : y = x <;> simp [hh]
  rw [hnorm] at hh
  exact hh

/-- The explicit comparison time from Appendix A.1, using the actual minimum weight. -/
def mixingUpperTime (p : FinProb (Config V)) (ε : ℝ) : ℝ :=
  Real.log (1 / (ε * minimumWeight p)) / spectralGap p

/-- The comparison time is an actual good time for every starting configuration. -/
theorem heatBath_good_upper_time (p : FinProb (Config V)) (hp : ∀ a, 0 < p.w a)
    (x : V) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    0 ≤ mixingUpperTime p ε ∧
      ∀ a, tvDist (heatBathTransition p (mixingUpperTime p ε) a) p ≤ ε := by
  let m := minimumWeight p
  let g := spectralGap p
  let T := mixingUpperTime p ε
  have hm : 0 < m := minimumWeight_pos p hp
  have hm1 : m ≤ 1 := minimumWeight_le_one p
  have hg : 0 < g := heatBath_gap_pos p hp x
  have hu : 0 < ε * m := mul_pos hε hm
  have hu1 : ε * m < 1 := by nlinarith
  have hv : 1 < 1 / (ε * m) := (lt_div_iff₀ hu).mpr (by linarith)
  have hT : 0 ≤ T := (div_pos (Real.log_pos hv) hg).le
  refine ⟨hT, ?_⟩
  have hE : Real.exp (-g * T) = ε * m := by
    have he : -g * T = - Real.log (1 / (ε * m)) := by
      change -g * (Real.log (1 / (ε * m)) / g) = -Real.log (1 / (ε * m))
      field_simp [ne_of_gt hg]
      <;> ring
    rw [he, Real.exp_neg, Real.exp_log (one_div_pos.mpr hu)]
    field_simp [ne_of_gt hu]
  have hE2 : Real.exp (-2 * g * T) = (ε * m)^2 := by
    rw [show -2 * g * T = (-g * T) + (-g * T) by ring, Real.exp_add, hE]
    ring
  intro a
  have hma : m ≤ p.w a := minimumWeight_le p a
  have hm2 : m^2 ≤ p.w a := by nlinarith
  have hi : 0 < 1 / p.w a := one_div_pos.mpr (hp a)
  have hcancel : p.w a * (1 / p.w a) = 1 := by field_simp [ne_of_gt (hp a)]
  have hcoef : m^2 * (1 / p.w a - 1) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hm2 hi.le
    nlinarith [sq_nonneg m]
  have hχ := heatBath_chiSquare_le p hp T hT a
  change chiSquare (heatBathTransition p T a) p ≤
    Real.exp (-2 * g * T) * (1 / p.w a - 1) at hχ
  rw [hE2] at hχ
  have hχ' : chiSquare (heatBathTransition p T a) p ≤ ε^2 := by
    have hh := mul_le_mul_of_nonneg_left hcoef (sq_nonneg ε)
    nlinarith only [hχ, hh]
  have hTV := tvDist_sq_le_chiSquare (heatBathTransition p T a) p hp
  have hn := tvDist_nonneg (heatBathTransition p T a) p
  nlinarith

/-- The mixing upper bound for the actual rate-one heat-bath transition laws. -/
theorem heatBath_mixing_upper (p : FinProb (Config V)) (hp : ∀ a, 0 < p.w a)
    (x : V) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    tMix p (heatBathTransition p) ε ≤
      (spectralGap p)⁻¹ * Real.log (1 / (ε * minimumWeight p)) := by
  obtain ⟨hT, hgood⟩ := heatBath_good_upper_time p hp x ε hε (by linarith)
  have hh := tMix_le p (heatBathTransition p) hT hgood
  simpa only [mixingUpperTime, div_eq_mul_inv, mul_comm] using hh

private theorem abs_expect_sub_le_bound {A : Type*} [Fintype A]
    (μ ν : FinProb A) (f : A → ℝ) (M : ℝ) (hf : ∀ a, |f a| ≤ M) :
    |μ.expect f - ν.expect f| ≤ (2 * tvDist μ ν) * M := by
  have he : μ.expect f - ν.expect f = ∑ a, (μ.w a - ν.w a) * f a := by
    simp only [FinProb.expect, sub_mul, sum_sub_distrib]
  rw [he]
  calc
    |∑ a, (μ.w a - ν.w a) * f a| ≤ ∑ a, |(μ.w a - ν.w a) * f a| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |μ.w a - ν.w a| * M := by
      apply sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hf a) (abs_nonneg _)
    _ = (2 * tvDist μ ν) * M := by rw [← sum_mul]; unfold tvDist; ring

/-- An attained gap eigenfunction gives the worst-start TV lower bound for
this actual semigroup, rather than for an assumed scalar decay profile. -/
theorem heatBath_tv_lower (p : FinProb (Config V)) (hp : ∀ a, 0 < p.w a)
    (x : V) :
    ∃ a : Config V, ∀ t : ℝ, 0 ≤ t →
      Real.exp (-spectralGap p * t) / 2 ≤ tvDist (heatBathTransition p t a) p := by
  obtain ⟨f, hf, hvar, heigen⟩ := SpectralMixing.gap_eigenfunction p hp x
  obtain ⟨a, _, hmax⟩ := univ.exists_max_image (fun a => |f a|) univ_nonempty
  have hmax' : ∀ b, |f b| ≤ |f a| := fun b => hmax b (mem_univ b)
  have hM : 0 < |f a| := by
    by_contra h
    have hzero : f = fun _ => 0 := by
      funext b
      have hb := hmax' b
      have ha := abs_nonneg (f a)
      have hh : |f b| = 0 := le_antisymm (by linarith) (abs_nonneg _)
      exact abs_eq_zero.mp hh
    rw [hzero] at hvar
    simp [FinProb.variance, FinProb.expect_const] at hvar
  refine ⟨a, ?_⟩
  intro t ht
  have hexp := heatBathSemigroup_eigenfunction p f (-spectralGap p) t heigen
  have hrow : (heatBathTransition p t a).expect f = Real.exp (-spectralGap p * t) * f a := by
    have hh := congrFun hexp a
    change (∑ b, heatBathSemigroup p t a b * f b) = _ at hh
    unfold FinProb.expect
    simp_rw [heatBathTransition_w p t ht]
    simpa only [mul_neg, neg_mul, mul_comm t (spectralGap p)] using hh
  have hd := abs_expect_sub_le_bound (heatBathTransition p t a) p f (|f a|) hmax'
  rw [hf, sub_zero, hrow, abs_mul, abs_of_pos (Real.exp_pos _)] at hd
  have hh : Real.exp (-spectralGap p * t) ≤ 2 * tvDist (heatBathTransition p t a) p :=
    (mul_le_mul_iff_left₀ hM).mp hd
  linarith

/-- The relaxation-to-mixing lower bound for the actual heat-bath chain. -/
theorem heatBath_mixing_lower (p : FinProb (Config V)) (hp : ∀ a, 0 < p.w a) (x : V) :
    Real.log 2 * (spectralGap p)⁻¹ ≤ tMix p (heatBathTransition p) (1 / 4) := by
  obtain ⟨hT, hgood⟩ := heatBath_good_upper_time p hp x (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨a, ha⟩ := heatBath_tv_lower p hp x
  have hg := heatBath_gap_pos p hp x
  apply le_tMix p (heatBathTransition p) ⟨_, hT, hgood⟩
  intro t ht hmixed
  have he : Real.exp (-spectralGap p * t) ≤ 1 / 2 := by
    have hh := ha t ht
    have hmix := hmixed a
    linarith
  have hlog := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hlog
  have hhalf : Real.log (1 / 2) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  rw [hhalf] at hlog
  change Real.log 2 / spectralGap p ≤ t
  apply (div_le_iff₀ hg).mpr
  linarith

/-- Both inequalities of Appendix A.1 for the paper's actual rate-one
heat-bath semigroup, using its variational spectral gap and minimum mass. -/
theorem lemma_A_1_heatBath (p : FinProb (Config V)) (hp : ∀ a, 0 < p.w a)
    (x : V) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    Real.log 2 * (spectralGap p)⁻¹ ≤ tMix p (heatBathTransition p) (1 / 4) ∧
      tMix p (heatBathTransition p) ε ≤
        (spectralGap p)⁻¹ * Real.log (1 / (ε * minimumWeight p)) :=
  ⟨heatBath_mixing_lower p hp x, heatBath_mixing_upper p hp x ε hε hε1⟩

end Paper09
