import MEJF.RankFrontier
import Mathlib.Analysis.SpecificLimits.Basic

namespace MEJF.RankFrontier

noncomputable section

open Filter Topology

/-- Floors have an error bounded by one; after division by a diverging denominator
this error vanishes. This lemma allows moving, rather than fixed, numerators. -/
lemma tendsto_floor_ratio {x d : ℕ → ℝ} {c : ℝ}
    (hd : Tendsto d atTop atTop) (hx : ∀ᶠ k in atTop, 0 ≤ x k)
    (hr : Tendsto (fun k => x k / d k) atTop (𝓝 c)) :
    Tendsto (fun k => (⌊x k⌋₊ : ℝ) / d k) atTop (𝓝 c) := by
  have hi : Tendsto (fun k => 1 / d k) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hd
  have hlo : Tendsto (fun k => x k / d k - 1 / d k) atTop (𝓝 c) := by
    simpa only [sub_zero] using hr.sub hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hr
  · filter_upwards [hd.eventually_gt_atTop 0] with k hk
    rw [← sub_div, div_le_div_iff_of_pos_right hk]
    have := Nat.lt_floor_add_one (x k)
    linarith
  · filter_upwards [hd.eventually_gt_atTop 0, hx] with k hk hxk
    exact (div_le_div_iff_of_pos_right hk).mpr (Nat.floor_le hxk)

/-- Subtracting one from a natural numerator, with truncation, changes its
normalized limit by zero. -/
lemma tendsto_pred_ratio {v m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto m atTop atTop)
    (hv : Tendsto (fun k => (v k : ℝ) / m k) atTop (𝓝 c)) :
    Tendsto (fun k => (v k - 1 : ℕ) / (m k : ℝ)) atTop (𝓝 c) := by
  have hmR : Tendsto (fun k => (m k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hi : Tendsto (fun k => 1 / (m k : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hmR
  have hlo : Tendsto (fun k => (v k : ℝ) / m k - 1 / m k) atTop (𝓝 c) := by
    simpa only [sub_zero] using hv.sub hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hv
  · filter_upwards [hmR.eventually_gt_atTop 0] with k hk
    rw [← sub_div, div_le_div_iff_of_pos_right hk]
    have h : v k ≤ (v k - 1) + 1 := by omega
    have h' : (v k : ℝ) ≤ (v k - 1 : ℕ) + 1 := by exact_mod_cast h
    linarith
  · filter_upwards [hmR.eventually_gt_atTop 0] with k hk
    apply (div_le_div_iff_of_pos_right hk).mpr
    exact_mod_cast Nat.sub_le (v k) 1

/-- Exact rounding for the source's shifted rank `floor (a (m+1))`. -/
lemma tendsto_shifted_floor_ratio {m : ℕ → ℕ} {a : ℝ}
    (hm : Tendsto m atTop atTop) (ha : 0 ≤ a) :
    Tendsto (fun k => (⌊a * (m k + 1 : ℕ)⌋₊ : ℝ) / m k) atTop (𝓝 a) := by
  have hmR : Tendsto (fun k => (m k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hi : Tendsto (fun k => (m k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hmR
  have hr : Tendsto (fun k => a * ((m k : ℝ) + 1) / m k) atTop (𝓝 a) := by
    have hh : Tendsto (fun k => a * (1 + (m k : ℝ)⁻¹)) atTop (𝓝 a) := by
      have hc : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
      have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      simpa using hc.mul (h1.add hi)
    apply hh.congr'
    filter_upwards [hmR.eventually_gt_atTop 0] with k hk
    field_simp
  simpa only [Nat.cast_add, Nat.cast_one] using
    tendsto_floor_ratio hmR (Eventually.of_forall (fun k => by positivity)) hr

/-- The source's failure threshold `(floor (α n))+1`, normalized by `n`. -/
lemma tendsto_failureThreshold_ratio {n : ℕ → ℕ} {α : ℝ}
    (hn : Tendsto n atTop atTop) (hα : 0 ≤ α) :
    Tendsto (fun k => (⌊α * (n k : ℝ)⌋₊ + 1 : ℕ) / (n k : ℝ)) atTop (𝓝 α) := by
  have hnR : Tendsto (fun k => (n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hi : Tendsto (fun k => (n k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hnR
  have hf := (tendsto_nat_floor_mul_div_atTop hα).comp hnR
  simpa only [Nat.cast_add, Nat.cast_one, add_div, one_div, add_zero] using hf.add hi

/-- A moving natural quotient has the expected normalized capacity limit,
including the floor and the truncation at `m`. -/
lemma capacity_ratio_limit {m F t ell : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto m atTop atTop)
    (hr : Tendsto (fun k =>
      ((F k : ℝ) * (ell k - 1 : ℕ) / (F k - t k + 1 : ℕ)) / m k)
      atTop (𝓝 c)) :
    Tendsto (fun k => (capacity (m k) (F k) (t k) (ell k) : ℝ) / m k)
      atTop (𝓝 (min 1 c)) := by
  have hmR : Tendsto (fun k => (m k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hf := tendsto_floor_ratio hmR (Eventually.of_forall (fun k => by positivity)) hr
  have hraw : Tendsto (fun k => (F k * (ell k - 1) / (F k - t k + 1) : ℕ) / (m k : ℝ))
      atTop (𝓝 c) := by
    convert hf using 1
    ext k
    rw [← Nat.cast_mul, Nat.floor_div_eq_div]
  have hmin : Tendsto (fun k => min 1
      ((F k * (ell k - 1) / (F k - t k + 1) : ℕ) / (m k : ℝ)))
      atTop (𝓝 (min 1 c)) := tendsto_const_nhds.min hraw
  apply hmin.congr'
  filter_upwards [hmR.eventually_gt_atTop 0] with k hk
  rw [capacity, Nat.cast_min, ← min_div_div_right hk.le, div_self hk.ne']

/-- Turning a normalized capacity limit into the normalized failure formula. -/
lemma failureRate_limit_of_capacity {m F t ell : ℕ → ℕ} {C : ℝ}
    (hm : Tendsto m atTop atTop) (htF : ∀ᶠ k in atTop, t k ≤ F k)
    (hc : Tendsto (fun k => (capacity (m k) (F k) (t k) (ell k) : ℝ) / m k)
      atTop (𝓝 C)) :
    Tendsto (fun k => failureRate (m k) (F k) (t k) (ell k))
      atTop (𝓝 (min 1 (2 * C))) := by
  have hmR : Tendsto (fun k => (m k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hi : Tendsto (fun k => 1 / (m k : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hmR
  have hr : Tendsto (fun k =>
      (2 * ((capacity (m k) (F k) (t k) (ell k) : ℝ) / m k) + 1 / m k) /
        (1 + 1 / m k)) atTop (𝓝 (2 * C)) := by
    simpa using ((tendsto_const_nhds.mul hc).add hi).div
      (tendsto_const_nhds.add hi) (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have hmin : Tendsto (fun k => min 1
      ((2 * ((capacity (m k) (F k) (t k) (ell k) : ℝ) / m k) + 1 / m k) /
        (1 + 1 / m k))) atTop (𝓝 (min 1 (2 * C))) := tendsto_const_nhds.min hr
  apply hmin.congr'
  filter_upwards [hmR.eventually_gt_atTop 0, htF] with k hk htFk
  rw [failureRate_eq_min htFk]
  congr 1
  push_cast
  field_simp

lemma min_two_mul_min (c : ℝ) : min 1 (2 * min 1 c) = min 1 (2 * c) := by
  by_cases hc : c ≤ 1
  · rw [min_eq_right hc]
  · rw [min_eq_left (by linarith : 1 ≤ c)]
    norm_num [min_eq_left (by linarith : 1 ≤ 2 * c)]

/-- Corollary 3.4, the branch `a < α`, for the full source rounding and every
pair of diverging integer sequences. This concerns the explicit formula (3.2). -/
theorem arithmetic_asymptotic_low {m n : ℕ → ℕ} {a b α : ℝ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hα : 0 ≤ α) (haα : a < α) :
    Tendsto (fun k => failureRate (m k)
      (⌊α * (n k : ℝ)⌋₊ + 1) ⌊a * (n k + 1 : ℕ)⌋₊ ⌊b * (m k + 1 : ℕ)⌋₊)
      atTop (𝓝 (min 1 (2 * α * b / (α - a)))) := by
  let FF : ℕ → ℕ := fun k => ⌊α * (n k : ℝ)⌋₊ + 1
  let TT : ℕ → ℕ := fun k => ⌊a * (n k + 1 : ℕ)⌋₊
  let LL : ℕ → ℕ := fun k => ⌊b * (m k + 1 : ℕ)⌋₊
  have hF : Tendsto (fun k => (FF k : ℝ) / n k) atTop (𝓝 α) :=
    tendsto_failureThreshold_ratio hn hα
  have hT : Tendsto (fun k => (TT k : ℝ) / n k) atTop (𝓝 a) :=
    tendsto_shifted_floor_ratio hn ha
  have hL : Tendsto (fun k => (LL k - 1 : ℕ) / (m k : ℝ)) atTop (𝓝 b) :=
    tendsto_pred_ratio hm (tendsto_shifted_floor_ratio hm hb)
  have hnR : Tendsto (fun k => (n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hi : Tendsto (fun k => (n k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hnR
  have htF : ∀ᶠ k in atTop, TT k ≤ FF k := by
    filter_upwards [hT.eventually_lt hF haα, hnR.eventually_gt_atTop 0] with k hk hnk
    have h : (TT k : ℝ) < FF k := (div_lt_div_iff_of_pos_right hnk).mp hk
    exact_mod_cast h.le
  have hD : Tendsto (fun k => (FF k - TT k + 1 : ℕ) / (n k : ℝ))
      atTop (𝓝 (α - a)) := by
    have hh := (hF.sub hT).add hi
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [htF] with k hk
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hk, add_div, sub_div, one_div]
  have hr : Tendsto (fun k =>
      ((FF k : ℝ) * (LL k - 1 : ℕ) / (FF k - TT k + 1 : ℕ)) / m k)
      atTop (𝓝 (α * b / (α - a))) := by
    have hh := (hF.mul hL).div hD (by linarith : α - a ≠ 0)
    apply hh.congr'
    filter_upwards [hnR.eventually_gt_atTop 0] with k hnk
    change ((FF k : ℝ) / n k * ((LL k - 1 : ℕ) / (m k : ℝ))) /
      ((FF k - TT k + 1 : ℕ) / (n k : ℝ)) =
      ((FF k : ℝ) * (LL k - 1 : ℕ) / (FF k - TT k + 1 : ℕ)) / m k
    field_simp [hnk.ne']
  have hc := capacity_ratio_limit hm hr
  have hrate := failureRate_limit_of_capacity hm htF hc
  rw [min_two_mul_min] at hrate
  simpa only [mul_div_assoc, mul_assoc] using hrate

/-- At the boundary `a = α < 1`, the two inner ranks differ by at most one. -/
lemma equal_parameter_rank_bounds {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (n : ℕ) :
    ⌊α * (n + 1 : ℕ)⌋₊ ≤ ⌊α * (n : ℝ)⌋₊ + 1 ∧
      ⌊α * (n : ℝ)⌋₊ + 1 ≤ ⌊α * (n + 1 : ℕ)⌋₊ + 1 := by
  have hmono : ⌊α * (n : ℝ)⌋₊ ≤ ⌊α * (n + 1 : ℕ)⌋₊ := by
    apply Nat.floor_mono
    push_cast
    nlinarith
  have hlt : ⌊α * (n + 1 : ℕ)⌋₊ < ⌊α * (n : ℝ)⌋₊ + 2 := by
    rw [Nat.floor_lt (by positivity : 0 ≤ α * (n + 1 : ℕ))]
    have := Nat.lt_floor_add_one (α * (n : ℝ))
    push_cast
    nlinarith
  omega

/-- Corollary 3.4 at `a = α`: the denominator of (3.1) is bounded by two,
while its numerator forces the capacity to saturate at `m`. -/
theorem arithmetic_asymptotic_boundary {m n : ℕ → ℕ} {b α : ℝ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hb : 0 < b) (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (fun k => failureRate (m k)
      (⌊α * (n k : ℝ)⌋₊ + 1) ⌊α * (n k + 1 : ℕ)⌋₊ ⌊b * (m k + 1 : ℕ)⌋₊)
      atTop (𝓝 1) := by
  let FF : ℕ → ℕ := fun k => ⌊α * (n k : ℝ)⌋₊ + 1
  let TT : ℕ → ℕ := fun k => ⌊α * (n k + 1 : ℕ)⌋₊
  let LL : ℕ → ℕ := fun k => ⌊b * (m k + 1 : ℕ)⌋₊
  have hFNat : Tendsto FF atTop atTop :=
    (tendsto_add_atTop_nat 1).comp ((tendsto_nat_floor_mul_atTop α hα).comp hn)
  have hFR : Tendsto (fun k => (FF k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hFNat
  have hmR : Tendsto (fun k => (m k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hL : Tendsto (fun k => (LL k - 1 : ℕ) / (m k : ℝ)) atTop (𝓝 b) :=
    tendsto_pred_ratio hm (tendsto_shifted_floor_ratio hm hb.le)
  have hevent : ∀ᶠ k in atTop, failureRate (m k) (FF k) (TT k) (LL k) = 1 := by
    filter_upwards [hmR.eventually_gt_atTop 0,
      hFR.eventually_gt_atTop (4 / b),
      hL.eventually_const_lt (by linarith : b / 2 < b)] with k hmk hFk hLk
    have hbnd := equal_parameter_rank_bounds hα.le hα1 (n k)
    change TT k ≤ FF k ∧ FF k ≤ TT k + 1 at hbnd
    have hD : FF k - TT k + 1 ≤ 2 := by omega
    have hLF : b / 2 * (m k : ℝ) ≤ (LL k - 1 : ℕ) :=
      ((lt_div_iff₀ hmk).mp hLk).le
    have hF2 : (2 : ℝ) ≤ (FF k : ℝ) * (b / 2) := by
      have := (div_lt_iff₀ hb).mp hFk
      nlinarith
    have hprod : (2 : ℝ) * m k ≤ (FF k : ℝ) * (LL k - 1 : ℕ) := by
      calc
        (2 : ℝ) * m k ≤ ((FF k : ℝ) * (b / 2)) * m k :=
          mul_le_mul_of_nonneg_right hF2 (Nat.cast_nonneg _)
        _ = (FF k : ℝ) * (b / 2 * m k) := by ring
        _ ≤ (FF k : ℝ) * (LL k - 1 : ℕ) :=
          mul_le_mul_of_nonneg_left hLF (Nat.cast_nonneg _)
    have hprodN : 2 * m k ≤ FF k * (LL k - 1) := by exact_mod_cast hprod
    have hraw : m k ≤ FF k * (LL k - 1) / (FF k - TT k + 1) := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < FF k - TT k + 1)).mpr
      calc
        m k * (FF k - TT k + 1) ≤ m k * 2 := Nat.mul_le_mul_left _ hD
        _ = 2 * m k := Nat.mul_comm _ _
        _ ≤ FF k * (LL k - 1) := hprodN
    have hcap : capacity (m k) (FF k) (TT k) (LL k) = m k := min_eq_left hraw
    rw [failureRate_eq_min hbnd.1, hcap]
    apply min_eq_left
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (m k + 1 : ℕ))]
    push_cast
    nlinarith [show (0 : ℝ) ≤ m k from Nat.cast_nonneg _]
  apply tendsto_const_nhds.congr'
  filter_upwards [hevent] with k hk
  exact hk.symm

/-- The `a > α` branch of Corollary 3.4 becomes the high-inner-rank branch eventually. -/
theorem arithmetic_asymptotic_high {m n : ℕ → ℕ} {a b α : ℝ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (ha : 0 ≤ a) (hα : 0 ≤ α) (hαa : α < a) :
    Tendsto (fun k => failureRate (m k)
      (⌊α * (n k : ℝ)⌋₊ + 1) ⌊a * (n k + 1 : ℕ)⌋₊ ⌊b * (m k + 1 : ℕ)⌋₊)
      atTop (𝓝 1) := by
  have hF := tendsto_failureThreshold_ratio hn hα
  have hT := tendsto_shifted_floor_ratio hn ha
  have hnR : Tendsto (fun k => (n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hevent : ∀ᶠ k in atTop,
      failureRate (m k) (⌊α * (n k : ℝ)⌋₊ + 1)
        ⌊a * (n k + 1 : ℕ)⌋₊ ⌊b * (m k + 1 : ℕ)⌋₊ = 1 := by
    filter_upwards [hF.eventually_lt hT hαa, hnR.eventually_gt_atTop 0] with k hk hnk
    apply failureRate_high_inner
    have h := (div_lt_div_iff_of_pos_right hnk).mp hk
    exact_mod_cast h
  apply tendsto_const_nhds.congr'
  filter_upwards [hevent] with k hk
  exact hk.symm

/-- Corollary 3.4's complete asymptotic assertion for the explicit formula (3.2),
along any two sequences tending to infinity, with all source floors retained. -/
theorem arithmetic_asymptotic {m n : ℕ → ℕ} {a b α : ℝ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (fun k => failureRate (m k)
      (⌊α * (n k : ℝ)⌋₊ + 1) ⌊a * (n k + 1 : ℕ)⌋₊ ⌊b * (m k + 1 : ℕ)⌋₊)
      atTop (𝓝 (limitingRate a b α)) := by
  unfold limitingRate
  by_cases haα : a < α
  · rw [if_pos haα]
    exact arithmetic_asymptotic_low hm hn ha.le hb.le hα.le haα
  · rw [if_neg haα]
    by_cases heq : a = α
    · subst a
      exact arithmetic_asymptotic_boundary hm hn hb hα hα1
    · have hlt : α < a := by
        rcases lt_or_eq_of_le (le_of_not_gt haα) with h | h
        · exact h
        · exact False.elim (heq h.symm)
      exact arithmetic_asymptotic_high hm hn ha.le hα.le hlt


end

end MEJF.RankFrontier
