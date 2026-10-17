import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The family of geometric schedules (paper Section 7.1)

The history and cost ratios are defined from their stated formulas.  Their
fixed product is proved, and the balanced schedule is proved to minimize the
larger ratio over every positive schedule multiplier.
-/

namespace P31.ScheduleFamily

noncomputable section

open scoped BigOperators

def historyRatio (ρ p τ : ℝ) : ℝ := τ / ρ ^ (p - 1)

def costRatio (ρ p κ τ : ℝ) : ℝ := ρ ^ (p - κ) / τ

def balancedTau (ρ p κ : ℝ) : ℝ := ρ ^ (p - (κ + 1) / 2)

def balancedRatio (ρ κ : ℝ) : ℝ := ρ ^ (-(κ - 1) / 2)

theorem historyRatio_pos {ρ p τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) :
    0 < historyRatio ρ p τ :=
  div_pos hτ (Real.rpow_pos_of_pos hρ _)

theorem costRatio_pos {ρ p κ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) :
    0 < costRatio ρ p κ τ :=
  div_pos (Real.rpow_pos_of_pos hρ _) hτ

theorem balancedTau_pos {ρ p κ : ℝ} (hρ : 0 < ρ) :
    0 < balancedTau ρ p κ :=
  Real.rpow_pos_of_pos hρ _

theorem balancedRatio_pos {ρ κ : ℝ} (hρ : 0 < ρ) :
    0 < balancedRatio ρ κ :=
  Real.rpow_pos_of_pos hρ _

/-- The product in Section 7.1 is independent of the chosen multiplier `τ`. -/
theorem ratio_product {ρ p κ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) :
    historyRatio ρ p τ * costRatio ρ p κ τ = ρ ^ (-(κ - 1)) := by
  have hA : ρ ^ (p - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hρ _)
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  calc
    historyRatio ρ p τ * costRatio ρ p κ τ = ρ ^ (p - κ) / ρ ^ (p - 1) := by
      unfold historyRatio costRatio
      field_simp
    _ = ρ ^ ((p - κ) - (p - 1)) := (Real.rpow_sub hρ _ _).symm
    _ = ρ ^ (-(κ - 1)) := by congr 1; ring

/-- The two geometric series decrease exactly in the open interval (7.3). -/
theorem both_ratios_lt_one_iff {ρ p κ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) :
    (historyRatio ρ p τ < 1 ∧ costRatio ρ p κ τ < 1) ↔
      (ρ ^ (p - κ) < τ ∧ τ < ρ ^ (p - 1)) := by
  have hA : 0 < ρ ^ (p - 1) := Real.rpow_pos_of_pos hρ _
  simp only [historyRatio, costRatio, div_lt_one hA, div_lt_one hτ]
  exact and_comm

/-- Substitution of (7.4) equalizes the history ratio at the stated value. -/
theorem balanced_history_ratio {ρ p κ : ℝ} (hρ : 0 < ρ) :
    historyRatio ρ p (balancedTau ρ p κ) = balancedRatio ρ κ := by
  unfold historyRatio balancedTau balancedRatio
  rw [← Real.rpow_sub hρ]
  congr 1
  ring

/-- Substitution of (7.4) equalizes the cost ratio at the same value. -/
theorem balanced_cost_ratio {ρ p κ : ℝ} (hρ : 0 < ρ) :
    costRatio ρ p κ (balancedTau ρ p κ) = balancedRatio ρ κ := by
  unfold costRatio balancedTau balancedRatio
  rw [← Real.rpow_sub hρ]
  congr 1
  ring

theorem balancedRatio_sq {ρ κ : ℝ} (hρ : 0 < ρ) :
    balancedRatio ρ κ * balancedRatio ρ κ = ρ ^ (-(κ - 1)) := by
  unfold balancedRatio
  rw [← Real.rpow_add hρ]
  congr 1
  ring

/-- A fixed positive product forces the larger factor to be at least their
balanced value.  This is an inequality proof, not a minimization premise. -/
theorem balanced_le_max_of_product {a b r : ℝ}
    (_ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hprod : a * b = r * r) :
    r ≤ max a b := by
  by_contra! h
  have ha' : a < r := (le_max_left a b).trans_lt h
  have hb' : b < r := (le_max_right a b).trans_lt h
  have hlt : a * b < r * r := mul_lt_mul ha' hb'.le hb hr.le
  linarith

/-- The balanced schedule globally minimizes the worse of the two ratios,
over all `τ > 0`, for every positive base `ρ`. -/
theorem balanced_minimizes_max {ρ p κ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) :
    max (historyRatio ρ p (balancedTau ρ p κ))
        (costRatio ρ p κ (balancedTau ρ p κ)) ≤
      max (historyRatio ρ p τ) (costRatio ρ p κ τ) := by
  rw [balanced_history_ratio hρ, balanced_cost_ratio hρ, max_self]
  apply balanced_le_max_of_product (historyRatio_pos hρ hτ) (costRatio_pos hρ hτ)
    (balancedRatio_pos hρ)
  rw [ratio_product hρ hτ, balancedRatio_sq hρ]

theorem balancedRatio_lt_one {ρ κ : ℝ} (hρ : 1 < ρ) (hκ : 1 < κ) :
    balancedRatio ρ κ < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg hρ
  linarith

/-- In the paper's parameter range the balanced schedule is admissible, so
the global minimizer above also minimizes over all admissible schedules. -/
theorem balanced_admissible {ρ p κ : ℝ} (hρ : 1 < ρ) (hκ : 1 < κ) :
    ρ ^ (p - κ) < balancedTau ρ p κ ∧ balancedTau ρ p κ < ρ ^ (p - 1) := by
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  apply (both_ratios_lt_one_iff hρ0 (balancedTau_pos hρ0)).mp
  rw [balanced_history_ratio hρ0, balanced_cost_ratio hρ0]
  exact ⟨balancedRatio_lt_one hρ hκ, balancedRatio_lt_one hρ hκ⟩

/-- The minimizer of the maximum is unique. -/
theorem balanced_unique {ρ p κ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ)
    (hmax : max (historyRatio ρ p τ) (costRatio ρ p κ τ) = balancedRatio ρ κ) :
    τ = balancedTau ρ p κ := by
  have ha := historyRatio_pos (p := p) hρ hτ
  have hb := costRatio_pos (p := p) (κ := κ) hρ hτ
  have hr := balancedRatio_pos (κ := κ) hρ
  have hprod : historyRatio ρ p τ * costRatio ρ p κ τ =
      balancedRatio ρ κ * balancedRatio ρ κ := by
    rw [ratio_product hρ hτ, balancedRatio_sq hρ]
  have ha_le : historyRatio ρ p τ ≤ balancedRatio ρ κ :=
    (le_max_left _ _).trans_eq hmax
  have hb_le : costRatio ρ p κ τ ≤ balancedRatio ρ κ :=
    (le_max_right _ _).trans_eq hmax
  have ha_eq : historyRatio ρ p τ = balancedRatio ρ κ := by
    apply le_antisymm ha_le
    by_contra! hlt
    have h₁ := mul_le_mul_of_nonneg_left hb_le ha.le
    have h₂ := mul_lt_mul_of_pos_right hlt hr
    linarith
  have hHist : historyRatio ρ p τ = historyRatio ρ p (balancedTau ρ p κ) :=
    ha_eq.trans (balanced_history_ratio hρ).symm
  exact (div_left_inj' (ne_of_gt (Real.rpow_pos_of_pos hρ (p - 1)))).mp hHist

/-- The conventional choice `ρ = 2` recovers the two ratios used in the main
algorithm without assuming the balance as a hypothesis. -/
theorem balanced_two_ratios (p κ : ℝ) :
    historyRatio 2 p (balancedTau 2 p κ) = (2 : ℝ) ^ (-(κ - 1) / 2) ∧
      costRatio 2 p κ (balancedTau 2 p κ) = (2 : ℝ) ^ (-(κ - 1) / 2) := by
  exact ⟨balanced_history_ratio (by norm_num), balanced_cost_ratio (by norm_num)⟩

/-- The leading query factor in (7.5), with its actual two ratio arguments. -/
def leadingFactor (β history cost : ℝ) : ℝ :=
  1 / ((1 - history) ^ β * (1 - cost ^ β))

def optimalHistory (c β : ℝ) : ℝ := c ^ (β / (β + 1))

def optimalCost (c β : ℝ) : ℝ := c ^ (1 / (β + 1))

/-- Equality in the two-variable positive-weight AM-GM inequality. -/
theorem weighted_amgm_eq_iff {u v a b : ℝ} (hu : 0 < u) (hv : 0 < v)
    (huv : u + v = 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ u * b ^ v = u * a + v * b ↔ a = b := by
  have hw : ∀ j ∈ (Finset.univ : Finset (Fin 2)), 0 < (![u, v] : Fin 2 → ℝ) j := by
    intro j _
    fin_cases j
    · simpa using hu
    · simpa using hv
  have hz : ∀ j ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ (![a, b] : Fin 2 → ℝ) j := by
    intro j _
    fin_cases j
    · simpa using ha
    · simpa using hb
  have h := Real.geom_mean_eq_arith_mean_weighted_iff'
    (Finset.univ : Finset (Fin 2)) (![u, v] : Fin 2 → ℝ) (![a, b] : Fin 2 → ℝ)
    hw (by simpa using huv) hz
  constructor
  · intro heq
    have heq' : (∏ j : Fin 2, (![a, b] : Fin 2 → ℝ) j ^ (![u, v] : Fin 2 → ℝ) j) =
        ∑ j : Fin 2, (![u, v] : Fin 2 → ℝ) j * (![a, b] : Fin 2 → ℝ) j := by
      simpa [Fin.prod_univ_succ, Fin.sum_univ_succ] using heq
    have h₀ := h.mp heq' 0 (Finset.mem_univ _)
    have h₁ := h.mp heq' 1 (Finset.mem_univ _)
    simpa using h₀.trans h₁.symm
  · intro hab
    subst b
    rw [← Real.rpow_add' ha (by rw [huv]; exact one_ne_zero), huv, Real.rpow_one]
    nlinarith

/-- Complementary weighted geometric means sum to at most one.  Its equality
condition is retained so the eventual leading-factor minimum is unique. -/
theorem complementary_geometric_bound {u v a b : ℝ}
    (hu : 0 < u) (hv : 0 < v) (huv : u + v = 1)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    (1 - a) ^ u * (1 - b) ^ v ≤ 1 - a ^ u * b ^ v ∧
      ((1 - a) ^ u * (1 - b) ^ v = 1 - a ^ u * b ^ v → a = b) := by
  have hgeom := Real.geom_mean_le_arith_mean2_weighted hu.le hv.le ha hb huv
  have hcomp := Real.geom_mean_le_arith_mean2_weighted hu.le hv.le
    (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1) huv
  constructor
  · nlinarith
  · intro heq
    apply (weighted_amgm_eq_iff hu hv huv ha hb).mp
    nlinarith

theorem optimal_ratios {c β : ℝ} (hc : 0 < c) (hc1 : c < 1) (hβ : 0 < β) :
    0 < optimalHistory c β ∧ optimalHistory c β < 1 ∧
      0 < optimalCost c β ∧ optimalCost c β < 1 ∧
      optimalHistory c β * optimalCost c β = c ∧
      optimalCost c β ^ β = optimalHistory c β := by
  have hβ1 : 0 < β + 1 := by linarith
  have hw : 0 < β / (β + 1) := div_pos hβ hβ1
  have hv : 0 < (1 : ℝ) / (β + 1) := div_pos zero_lt_one hβ1
  refine ⟨Real.rpow_pos_of_pos hc _, Real.rpow_lt_one hc.le hc1 hw,
    Real.rpow_pos_of_pos hc _, Real.rpow_lt_one hc.le hc1 hv, ?_, ?_⟩
  · unfold optimalHistory optimalCost
    rw [← Real.rpow_add hc]
    convert Real.rpow_one c using 1
    congr 1
    field_simp
  · unfold optimalHistory optimalCost
    rw [← Real.rpow_mul hc.le]
    congr 1
    ring

/-- The bound behind the unique optimum (7.6).  It is proved by two weighted
AM-GM inequalities; no claim about a stationary point is used as a premise. -/
theorem leading_denominator_bound {a b c β : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hβ : 0 < β) (hprod : a * b = c) :
    (1 - a) ^ β * (1 - b ^ β) ≤ (1 - optimalHistory c β) ^ (β + 1) ∧
      ((1 - a) ^ β * (1 - b ^ β) = (1 - optimalHistory c β) ^ (β + 1) →
        a = optimalHistory c β ∧ b = optimalCost c β) := by
  have hβ1 : 0 < β + 1 := by linarith
  have hβ10 : β + 1 ≠ 0 := ne_of_gt hβ1
  let u := β / (β + 1)
  let v := 1 / (β + 1)
  have hu : 0 < u := div_pos hβ hβ1
  have hv : 0 < v := div_pos zero_lt_one hβ1
  have huv : u + v = 1 := by dsimp [u, v]; field_simp
  have hvβ : β * v = u := by dsimp [u, v]; ring
  have huβ1 : u * (β + 1) = β := div_mul_cancel₀ _ hβ10
  have hvβ1 : v * (β + 1) = 1 := div_mul_cancel₀ _ hβ10
  have hy0 : 0 ≤ b ^ β := Real.rpow_nonneg hb.le _
  have hy1 : b ^ β < 1 := Real.rpow_lt_one hb.le hb1 hβ
  have hgeom : a ^ u * (b ^ β) ^ v = optimalHistory c β := by
    rw [← Real.rpow_mul hb.le, hvβ, ← Real.mul_rpow ha.le hb.le, hprod]
    rfl
  have hroot := complementary_geometric_bound hu hv huv ha.le ha1.le hy0 hy1.le
  rw [hgeom] at hroot
  have hRootNonneg : 0 ≤ (1 - a) ^ u * (1 - b ^ β) ^ v :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  have hCompNonneg : 0 ≤ 1 - optimalHistory c β := hRootNonneg.trans hroot.1
  have hRootPower : ((1 - a) ^ u * (1 - b ^ β) ^ v) ^ (β + 1) =
      (1 - a) ^ β * (1 - b ^ β) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _),
      ← Real.rpow_mul (by linarith : 0 ≤ 1 - a),
      ← Real.rpow_mul (by linarith : 0 ≤ 1 - b ^ β), huβ1, hvβ1, Real.rpow_one]
  constructor
  · rw [← hRootPower]
    exact Real.rpow_le_rpow hRootNonneg hroot.1 hβ1.le
  · intro heq
    have hRootEq : (1 - a) ^ u * (1 - b ^ β) ^ v = 1 - optimalHistory c β := by
      apply (Real.rpow_left_inj hRootNonneg hCompNonneg hβ1.ne').mp
      rwa [hRootPower]
    have hab : a = b ^ β := hroot.2 hRootEq
    have haOpt : a = optimalHistory c β := by
      rw [← hab, ← Real.rpow_add ha, huv, Real.rpow_one] at hgeom
      exact hgeom
    have hc : 0 < c := by rw [← hprod]; positivity
    have hc1 : c < 1 := by rw [← hprod]; simpa using mul_lt_mul ha1 hb1.le hb zero_le_one
    have hopt := optimal_ratios hc hc1 hβ
    refine ⟨haOpt, ?_⟩
    apply (Real.rpow_left_inj hb.le hopt.2.2.1.le hβ.ne').mp
    rw [hopt.2.2.2.2.2, ← haOpt, ← hab]

/-- The ratios (7.6) globally minimize the leading factor (7.5) over all
positive ratios below one with the same product. -/
theorem leading_factor_minimum {a b c β : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hc : 0 < c) (hc1 : c < 1) (hβ : 0 < β) (hprod : a * b = c) :
    leadingFactor β (optimalHistory c β) (optimalCost c β) ≤ leadingFactor β a b ∧
      (leadingFactor β (optimalHistory c β) (optimalCost c β) = leadingFactor β a b ↔
        a = optimalHistory c β ∧ b = optimalCost c β) := by
  have hopt := optimal_ratios hc hc1 hβ
  have hDpos : 0 < (1 - a) ^ β * (1 - b ^ β) :=
    mul_pos (Real.rpow_pos_of_pos (sub_pos.mpr ha1) _)
      (sub_pos.mpr (Real.rpow_lt_one hb.le hb1 hβ))
  have hDopt : (1 - optimalHistory c β) ^ β * (1 - optimalCost c β ^ β) =
      (1 - optimalHistory c β) ^ (β + 1) := by
    rw [hopt.2.2.2.2.2, Real.rpow_add (sub_pos.mpr hopt.2.1), Real.rpow_one]
  have hbound := leading_denominator_bound ha ha1 hb hb1 hβ hprod
  constructor
  · unfold leadingFactor
    rw [hDopt]
    exact one_div_le_one_div_of_le hDpos hbound.1
  · constructor
    · intro heq
      apply hbound.2
      have h := congrArg (fun z : ℝ => 1 / z) heq
      simpa only [leadingFactor, one_div_one_div, hDopt] using h.symm
    · rintro ⟨rfl, rfl⟩
      rfl

/-- The multiplier `τ*` stated after (7.6). -/
def optimalTau (ρ p κ β : ℝ) : ℝ :=
  ρ ^ (p - 1 - (κ - 1) * β / (β + 1))

/-- The abstract optimum at the fixed product has precisely the powers of
`ρ` displayed in (7.6). -/
theorem optimal_ratio_formulas {ρ κ β : ℝ} (hρ : 0 < ρ) :
    optimalHistory (ρ ^ (-(κ - 1))) β = ρ ^ (-(κ - 1) * β / (β + 1)) ∧
      optimalCost (ρ ^ (-(κ - 1))) β = ρ ^ (-(κ - 1) / (β + 1)) := by
  constructor
  · unfold optimalHistory
    rw [← Real.rpow_mul hρ.le]
    congr 1
    ring
  · unfold optimalCost
    rw [← Real.rpow_mul hρ.le]
    congr 1
    ring

theorem optimalTau_ratios {ρ p κ β : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) :
    historyRatio ρ p (optimalTau ρ p κ β) = optimalHistory (ρ ^ (-(κ - 1))) β ∧
      costRatio ρ p κ (optimalTau ρ p κ β) = optimalCost (ρ ^ (-(κ - 1))) β := by
  have hβ10 : β + 1 ≠ 0 := ne_of_gt (by linarith : 0 < β + 1)
  rw [(optimal_ratio_formulas hρ).1, (optimal_ratio_formulas hρ).2]
  constructor
  · unfold historyRatio optimalTau
    rw [← Real.rpow_sub hρ]
    congr 1
    ring
  · unfold costRatio optimalTau
    rw [← Real.rpow_sub hρ]
    congr 1
    field_simp
    ring

/-- The exact Section 7.1 optimization over schedule multipliers: `τ*` is
admissible, minimizes (7.5) globally, and is its unique minimizer.  The paper's
`β = p/(κ*p+κ-p)` is positive in its stated parameter range, so it is a direct
instance of this theorem. -/
theorem optimalTau_minimizes_leading {ρ p κ β τ : ℝ}
    (hρ : 1 < ρ) (hκ : 1 < κ) (hβ : 0 < β)
    (hτlo : ρ ^ (p - κ) < τ) (hτhi : τ < ρ ^ (p - 1)) :
    (ρ ^ (p - κ) < optimalTau ρ p κ β ∧
        optimalTau ρ p κ β < ρ ^ (p - 1)) ∧
      leadingFactor β (historyRatio ρ p (optimalTau ρ p κ β))
          (costRatio ρ p κ (optimalTau ρ p κ β)) ≤
        leadingFactor β (historyRatio ρ p τ) (costRatio ρ p κ τ) ∧
      (leadingFactor β (historyRatio ρ p (optimalTau ρ p κ β))
          (costRatio ρ p κ (optimalTau ρ p κ β)) =
        leadingFactor β (historyRatio ρ p τ) (costRatio ρ p κ τ) ↔
          τ = optimalTau ρ p κ β) := by
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hτ : 0 < τ := (Real.rpow_pos_of_pos hρ0 (p - κ)).trans hτlo
  have hc : 0 < ρ ^ (-(κ - 1)) := Real.rpow_pos_of_pos hρ0 _
  have hc1 : ρ ^ (-(κ - 1)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hρ (by linarith)
  have hτopt : 0 < optimalTau ρ p κ β := Real.rpow_pos_of_pos hρ0 _
  have hRatios := (both_ratios_lt_one_iff hρ0 hτ).mpr ⟨hτlo, hτhi⟩
  have hOpt := optimal_ratios hc hc1 hβ
  have hOptRatios := optimalTau_ratios (p := p) (κ := κ) hρ0 hβ
  have hMin := leading_factor_minimum (historyRatio_pos hρ0 hτ) hRatios.1
    (costRatio_pos hρ0 hτ) hRatios.2 hc hc1 hβ (ratio_product hρ0 hτ)
  constructor
  · apply (both_ratios_lt_one_iff hρ0 hτopt).mp
    rw [hOptRatios.1, hOptRatios.2]
    exact ⟨hOpt.2.1, hOpt.2.2.2.1⟩
  · constructor
    · rw [hOptRatios.1, hOptRatios.2]
      exact hMin.1
    · constructor
      · intro heq
        rw [hOptRatios.1, hOptRatios.2] at heq
        have hHistory := (hMin.2.mp heq).1
        have hHistEq : historyRatio ρ p τ = historyRatio ρ p (optimalTau ρ p κ β) :=
          hHistory.trans hOptRatios.1.symm
        exact (div_left_inj' (ne_of_gt (Real.rpow_pos_of_pos hρ0 (p - 1)))).mp hHistEq
      · intro heq
        rw [heq]

end

end P31.ScheduleFamily
