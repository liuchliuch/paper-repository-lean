import Paper37.Boundary
import Paper37.RenewalLikelihood
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Supporting lemmas for Appendix F of P37. These prove the finite posterior
reweighting calculation and the numerical assembly, without presupposing the
stationary renewal representation or the hard-prior combinatorics.
-/
namespace Paper37.LowerBound

open scoped BigOperators ENNReal

/-- A finite probability law, with real-valued masses. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

namespace FiniteLaw

variable {α : Type*} [Fintype α] (P : FiniteLaw α)

noncomputable def eventMass (E : α → Prop) [DecidablePred E] : ℝ :=
  ∑ x, if E x then P.mass x else 0

noncomputable def expectation (f : α → ℝ) : ℝ := ∑ x, P.mass x * f x

lemma eventMass_nonneg (E : α → Prop) [DecidablePred E] :
    0 ≤ P.eventMass E := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact P.nonneg x
  · exact le_rfl

lemma eventMass_compl (E : α → Prop) [DecidablePred E] :
    P.eventMass E + P.eventMass (fun x => ¬ E x) = 1 := by
  rw [eventMass, eventMass, ← Finset.sum_add_distrib, ← P.total]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E x <;> simp [hx]

lemma eventMass_le_one (E : α → Prop) [DecidablePred E] :
    P.eventMass E ≤ 1 := by
  have := P.eventMass_nonneg (fun x => ¬ E x)
  have := P.eventMass_compl E
  linarith

lemma expectation_nonneg {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ P.expectation f := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (P.nonneg x) (hf x))

/-- Discarding nonnegative loss outside an event. -/
lemma mass_mul_le_expectation (E : α → Prop) [DecidablePred E]
    {f : α → ℝ} {c : ℝ} (hf : ∀ x, 0 ≤ f x) (hc : ∀ x, E x → c ≤ f x) :
    P.eventMass E * c ≤ P.expectation f := by
  rw [eventMass, expectation, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : E x
  · simp only [if_pos hx]
    exact mul_le_mul_of_nonneg_left (hc x hx) (P.nonneg x)
  · simp only [if_neg hx, zero_mul]
    exact mul_nonneg (P.nonneg x) (hf x)

end FiniteLaw

/-- The scalar calculation behind the reweighting inequality in F.5. -/
lemma reweight_lower {p C m x y : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hC : 1 ≤ C)
    (hx : m * p ≤ x) (hy : y ≤ C * m * (1 - p))
    (hxy : 0 < x + y) :
    p / (p + C * (1 - p)) ≤ x / (x + y) := by
  have hd : 0 < p + C * (1 - p) := by
    have := mul_le_mul_of_nonneg_right hC (sub_nonneg.mpr hp1)
    nlinarith
  apply (div_le_div_iff₀ hd hxy).2
  have h1 := mul_le_mul_of_nonneg_left hy hp
  have h2 := mul_le_mul_of_nonneg_left hx (mul_nonneg (le_trans (by norm_num) hC)
    (sub_nonneg.mpr hp1))
  nlinarith

/-- A finite-law version: weights in [m,Cm] yield the precise odds bound. -/
lemma finite_reweight_lower {α : Type*} [Fintype α] (P : FiniteLaw α)
    (E : α → Prop) [DecidablePred E] (w : α → ℝ) {m C : ℝ}
    (hm : 0 < m) (hC : 1 ≤ C) (hw : ∀ x, m ≤ w x ∧ w x ≤ C * m) :
    P.eventMass E / (P.eventMass E + C * (1 - P.eventMass E)) ≤
      P.expectation (fun x => if E x then w x else 0) / P.expectation w := by
  let x := P.expectation (fun x => if E x then w x else 0)
  let y := P.expectation (fun x => if ¬ E x then w x else 0)
  have hsplit : x + y = P.expectation w := by
    simp only [x, y, FiniteLaw.expectation, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : E z <;> simp [hz]
  have hx : m * P.eventMass E ≤ x := by
    dsimp [x, FiniteLaw.expectation, FiniteLaw.eventMass]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : E z
    · simpa [hz, mul_comm] using mul_le_mul_of_nonneg_left (hw z).1 (P.nonneg z)
    · simp [hz]
  have hy : y ≤ C * m * (1 - P.eventMass E) := by
    have hcomp := P.eventMass_compl E
    have heq : 1 - P.eventMass E = P.eventMass (fun z => ¬ E z) := by linarith
    rw [heq]
    dsimp [y, FiniteLaw.expectation, FiniteLaw.eventMass]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : E z
    · simp [hz]
    · simpa [hz, mul_comm] using mul_le_mul_of_nonneg_left (hw z).2 (P.nonneg z)
  have hw0 : ∀ z, 0 ≤ w z := fun z => le_trans hm.le (hw z).1
  have hxy : 0 < x + y := by
    rw [hsplit]
    have hmexp : m ≤ P.expectation w := by
      calc
        m = (∑ z, P.mass z) * m := by rw [P.total, one_mul]
        _ = ∑ z, P.mass z * m := Finset.sum_mul _ _ _
        _ ≤ P.expectation w := Finset.sum_le_sum (fun z _ =>
          mul_le_mul_of_nonneg_left (hw z).1 (P.nonneg z))
    exact lt_of_lt_of_le hm hmexp
  have h := reweight_lower (P.eventMass_nonneg E) (P.eventMass_le_one E)
    hC hx hy hxy
  simpa only [hsplit] using h

/-- Averaging over a common conditional high-support law preserves the
pointwise factor-four comparison in F.5. -/
lemma marginalized_weight_comparison {H : Type*} [Fintype H]
    (P : FiniteLaw H) (w₁ w₂ : H → ℝ) {C : ℝ}
    (hw : ∀ h, w₁ h ≤ C * w₂ h) :
    P.expectation w₁ ≤ C * P.expectation w₂ := by
  unfold FiniteLaw.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  have := mul_le_mul_of_nonneg_left (hw h) (P.nonneg h)
  simpa only [mul_left_comm] using this

/-- The global weight range when J ≤ a. Its ratio is 16. -/
lemma two_boundary_weight_range {a UJ Ug m : ℝ} (ha : 0 < a)
    (hJlo : a / 2 ≤ UJ) (hJhi : UJ ≤ a)
    (hglo : a / 2 ≤ Ug) (hghi : Ug ≤ a)
    (hmlo : a / 2 ≤ m) (hmhi : m ≤ 2 * a) :
    a / 8 ≤ UJ * Ug / m ∧ UJ * Ug / m ≤ 2 * a := by
  have hm : 0 < m := by linarith
  have hJ : 0 ≤ UJ := by linarith
  have hg : 0 ≤ Ug := by linarith
  constructor
  · apply (le_div_iff₀ hm).2
    have hprod := mul_le_mul hJlo hglo (by linarith : 0 ≤ a / 2) hJ
    nlinarith
  · apply (div_le_iff₀ hm).2
    have hprod := mul_le_mul hJhi hghi hg ha.le
    nlinarith

/-- Comparing two low supports after fixing the high support, as required
when J > a. The left boundary factor UJ is shared, including UJ = 0. -/
lemma fixed_high_weight_comparison {UJ U₁ U₂ m₁ m₂ : ℝ}
    (hJ : 0 ≤ UJ) (hU₂ : 0 ≤ U₂)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hU : U₁ ≤ 2 * U₂) (hm : m₂ ≤ 2 * m₁) :
    UJ * U₁ / m₁ ≤ 4 * (UJ * U₂ / m₂) := by
  rw [show 4 * (UJ * U₂ / m₂) = (4 * UJ * U₂) / m₂ by ring]
  apply (div_le_div_iff₀ hm₁ hm₂).2
  have hprod := mul_le_mul hU hm hm₂.le (by linarith : 0 ≤ 2 * U₂)
  have h := mul_le_mul_of_nonneg_left hprod hJ
  convert h using 1 <;> ring

/-- The exact conditional-prior membership interval in (F.9). -/
lemma unseen_low_membership_interval {a ℓ : ℝ} (ha : 0 < a)
    (hl : 0 ≤ ℓ) (hl24 : ℓ ≤ a / 24) :
    11 / 23 ≤ (a / 2 - ℓ) / (a - ℓ) ∧
      (a / 2 - ℓ) / (a - ℓ) ≤ 1 / 2 := by
  have hd : 0 < a - ℓ := by linarith
  constructor
  · apply (le_div_iff₀ hd).2
    linarith
  · apply (div_le_iff₀ hd).2
    linarith

/-- The constant-ratio 16 case of F.5, including both event and complement. -/
lemma posterior_stability_constants {p x : ℝ}
    (hp : 11 / 23 ≤ p) (hp1 : p ≤ 1 / 2)
    (hx : p / (p + 16 * (1 - p)) ≤ x)
    (hxc : (1 - p) / (16 * p + (1 - p)) ≤ 1 - x) :
    11 / 203 ≤ x ∧ 11 / 203 ≤ 1 - x := by
  have hp0 : 0 ≤ p := by linarith
  have hd : 0 < p + 16 * (1 - p) := by linarith
  have hdc : 0 < 16 * p + (1 - p) := by linarith
  constructor
  · apply le_trans _ hx
    apply (le_div_iff₀ hd).2
    linarith
  · apply le_trans _ hxc
    apply (le_div_iff₀ hdc).2
    linarith

/-- The conditional-on-high-support ratio four case is stronger than required. -/
lemma posterior_stability_constants_high {p x : ℝ}
    (hp : 11 / 23 ≤ p) (hp1 : p ≤ 1 / 2)
    (hx : p / (p + 4 * (1 - p)) ≤ x)
    (hxc : (1 - p) / (4 * p + (1 - p)) ≤ 1 - x) :
    11 / 59 ≤ x ∧ 1 / 5 ≤ 1 - x := by
  have hd : 0 < p + 4 * (1 - p) := by linarith
  have hdc : 0 < 4 * p + (1 - p) := by linarith
  constructor
  · apply le_trans _ hx
    apply (le_div_iff₀ hd).2
    linarith
  · apply le_trans _ hxc
    apply (le_div_iff₀ hdc).2
    linarith

/-- F.3's numerical union-bound calculation. This does not assert its
stationary probability premises. -/
lemma good_event_probability_arithmetic {p badMany badCollision good : ℝ}
    (hp : 1 / 4 ≤ p) (hmany : badMany ≤ 1 / 12)
    (hcollision : badCollision ≤ 1 / 24)
    (hgood : p - badMany - badCollision ≤ good) : 1 / 8 ≤ good := by
  linarith

/-- Final numerical conversion in F.1, after the probabilistic lower bound. -/
lemma lower_bound_constant_assembly {a n risk : ℝ} (ha : 0 < a) (hn : 0 < n)
    (ha25 : a ≤ 25 * Real.sqrt n)
    (hlog : 0 ≤ Real.log 2 - 1 / 2)
    (hrisk : (1 / 8) * ((11 / 203) * (Real.log 2 - 1 / 2) / a) ≤ risk) :
    11 * (Real.log 2 - 1 / 2) / (40600 * Real.sqrt n) ≤ risk := by
  apply le_trans _ hrisk
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hc : 0 ≤ 11 * (Real.log 2 - 1 / 2) := mul_nonneg (by norm_num) hlog
  have h := div_le_div_of_nonneg_left hc ha ha25
  calc
    11 * (Real.log 2 - 1 / 2) / (40600 * Real.sqrt n) =
      (11 * (Real.log 2 - 1 / 2) / (25 * Real.sqrt n)) / 1624 := by ring
    _ ≤ (11 * (Real.log 2 - 1 / 2) / a) / 1624 :=
      div_le_div_of_nonneg_right h (by norm_num)
    _ = (1 / 8) * ((11 / 203) * (Real.log 2 - 1 / 2) / a) := by ring


namespace FiniteLaw

variable {α : Type*} [Fintype α] (P : FiniteLaw α)

/-- Normalize a nonnegative likelihood against a finite prior. -/
noncomputable def reweight (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hZ : 0 < P.expectation w) : FiniteLaw α where
  mass x := P.mass x * w x / P.expectation w
  nonneg x := div_nonneg (mul_nonneg (P.nonneg x) (hw x)) hZ.le
  total := by
    rw [← Finset.sum_div]
    exact div_self hZ.ne'

lemma reweight_eventMass (E : α → Prop) [DecidablePred E]
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hZ : 0 < P.expectation w) :
    (P.reweight w hw hZ).eventMass E =
      P.expectation (fun x => if E x then w x else 0) / P.expectation w := by
  unfold eventMass expectation reweight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E x <;> simp [hx, expectation]

/-- F.5's posterior stability conclusion for any explicitly normalized finite
prior and likelihood with the ratio-16 weight range. -/
lemma reweighted_membership_stable (E : α → Prop) [DecidablePred E]
    (w : α → ℝ) {m : ℝ} (hm : 0 < m)
    (hw : ∀ x, m ≤ w x ∧ w x ≤ 16 * m)
    (hZ : 0 < P.expectation w)
    (hp : 11 / 23 ≤ P.eventMass E) (hp1 : P.eventMass E ≤ 1 / 2) :
    11 / 203 ≤ (P.reweight w (fun x => le_trans hm.le (hw x).1) hZ).eventMass E ∧
    11 / 203 ≤ (P.reweight w (fun x => le_trans hm.le (hw x).1) hZ).eventMass
      (fun x => ¬ E x) := by
  let R := P.reweight w (fun x => le_trans hm.le (hw x).1) hZ
  have he := finite_reweight_lower P E w hm (by norm_num : (1:ℝ) ≤ 16) hw
  have hec := finite_reweight_lower P (fun x => ¬ E x) w hm
    (by norm_num : (1:ℝ) ≤ 16) hw
  rw [← P.reweight_eventMass E w (fun x => le_trans hm.le (hw x).1) hZ] at he
  rw [← P.reweight_eventMass (fun x => ¬ E x) w
    (fun x => le_trans hm.le (hw x).1) hZ] at hec
  have hpc := P.eventMass_compl E
  have hRc := R.eventMass_compl E
  have hec' : (1 - P.eventMass E) /
      (16 * P.eventMass E + (1 - P.eventMass E)) ≤ 1 - R.eventMass E := by
    have hcomp : P.eventMass (fun x => ¬ E x) = 1 - P.eventMass E := by linarith
    rw [hcomp] at hec
    have hden : 1 - P.eventMass E + 16 * (1 - (1 - P.eventMass E)) =
        16 * P.eventMass E + (1 - P.eventMass E) := by ring
    rw [hden] at hec
    change _ ≤ R.eventMass (fun x => ¬ E x) at hec
    linarith
  have h := posterior_stability_constants hp hp1 he hec'
  constructor
  · exact h.1
  · change _ ≤ R.eventMass (fun x => ¬ E x)
    linarith [h.2]

end FiniteLaw
/-- Elementary nonnegative-coefficient log inequality, including a zero numerator. -/
lemma mul_log_ratio_lower {u v : ℝ} (hu : 0 ≤ u) (hv : 0 < v) :
    u - v ≤ u * Real.log (u / v) := by
  rcases eq_or_lt_of_le hu with hu | hu
  · subst u
    simp only [zero_sub, zero_div, zero_mul]
    linarith
  · have h := Real.one_sub_inv_le_log_of_pos (div_pos hu hv)
    have h' := mul_le_mul_of_nonneg_left h hu.le
    have heq : u * (1 - (u / v)⁻¹) = u - v := by
      field_simp
    rwa [heq] at h'

lemma klReal_nonneg {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q < 1) : 0 ≤ Paper37.Boundary.klReal p q := by
  have h1 := mul_log_ratio_lower hp hq
  have h2 := mul_log_ratio_lower (sub_nonneg.mpr hp1) (sub_pos.mpr hq1)
  unfold Paper37.Boundary.klReal
  linarith

/-- The positive-parameter side of F.6, avoiding differentiability assumptions. -/
lemma klReal_positive_radius {p q : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q < 1) (hqp : q ≤ p / 2) :
    (Real.log 2 - 1 / 2) * p ≤ Paper37.Boundary.klReal p q := by
  have hcomp := mul_log_ratio_lower (sub_nonneg.mpr hp1) (sub_pos.mpr hq1)
  have hlog := Real.log_le_sub_one_of_pos (div_pos (mul_pos (show (0:ℝ) < 2 by norm_num) hq) hp)
  have hmul := mul_le_mul_of_nonneg_left hlog hp.le
  have heq : p * (2 * q / p - 1) = 2 * q - p := by
    field_simp
  rw [heq] at hmul
  have hlogeq : Real.log (p / q) = Real.log 2 - Real.log (2 * q / p) := by
    rw [Real.log_div hp.ne' hq.ne',
      Real.log_div (mul_ne_zero (by norm_num) hq.ne') hp.ne',
      Real.log_mul (by norm_num) hq.ne']
    ring
  unfold Paper37.Boundary.klReal
  rw [hlogeq]
  nlinarith

lemma klReal_zero_lower {q : ℝ} (hq1 : q < 1) :
    q ≤ Paper37.Boundary.klReal 0 q := by
  have h := mul_log_ratio_lower (u := 1) (v := 1-q) (by norm_num)
    (sub_pos.mpr hq1)
  simpa [Paper37.Boundary.klReal] using h

lemma radius_coefficient_nonneg : 0 ≤ Real.log 2 - 1 / 2 := by
  have := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
  norm_num at this ⊢
  linarith

lemma radius_coefficient_le_half : Real.log 2 - 1 / 2 ≤ 1 / 2 := by
  have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
  linarith

/-- F.6 for every interior output, for the actual finite posterior law.
The assumptions state the two membership masses and the source parameter range. -/
lemma finite_posterior_radius_interior {α : Type*} [Fintype α]
    (P : FiniteLaw α) (M : α → Prop) [DecidablePred M]
    (θ : α → ℝ) {a η q : ℝ} (ha : 0 < a) (hη : 0 ≤ η)
    (hθ : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1)
    (hzero : ∀ x, ¬ M x → θ x = 0)
    (hpositive : ∀ x, M x → 1 / a ≤ θ x)
    (hm : η ≤ P.eventMass M) (hmc : η ≤ P.eventMass (fun x => ¬ M x))
    (hq : 0 < q) (hq1 : q < 1) :
    η * (Real.log 2 - 1 / 2) / a ≤
      P.expectation (fun x => Paper37.Boundary.klReal (θ x) q) := by
  have hnonneg : ∀ x, 0 ≤ Paper37.Boundary.klReal (θ x) q :=
    fun x => klReal_nonneg (hθ x).1 (hθ x).2 hq hq1
  have hc := radius_coefficient_nonneg
  by_cases hqhalf : 1 / (2 * a) ≤ q
  · have hmass := P.mass_mul_le_expectation (fun x => ¬ M x) hnonneg
      (c := q) (by
        intro x hx
        rw [hzero x hx]
        exact klReal_zero_lower hq1)
    have hηq : η * q ≤ P.eventMass (fun x => ¬ M x) * q :=
      mul_le_mul_of_nonneg_right hmc hq.le
    apply le_trans _ (le_trans hηq hmass)
    have hc2 := radius_coefficient_le_half
    have hca : (Real.log 2 - 1 / 2) / a ≤ 1 / (2 * a) := by
      apply (div_le_iff₀ ha).2
      have heq : 1 / (2 * a) * a = (1:ℝ) / 2 := by field_simp
      rw [heq]
      exact hc2
    have h := mul_le_mul_of_nonneg_left (le_trans hca hqhalf) hη
    simpa only [mul_div_assoc] using h
  · have hmass := P.mass_mul_le_expectation M hnonneg
      (c := (Real.log 2 - 1 / 2) / a) (by
        intro x hx
        have hθpos : 0 < θ x := lt_of_lt_of_le (one_div_pos.mpr ha) (hpositive x hx)
        have hqp : q ≤ θ x / 2 := by
          have := hpositive x hx
          have heq : 1 / (2 * a) = (1 / a) / 2 := by ring
          rw [heq] at hqhalf
          push_neg at hqhalf
          linarith
        have hrad := klReal_positive_radius hθpos (hθ x).2 hq hq1 hqp
        apply le_trans _ hrad
        have := mul_le_mul_of_nonneg_left (hpositive x hx) hc
        simpa only [mul_one_div] using this)
    apply le_trans _ hmass
    have := mul_le_mul_of_nonneg_right hm (div_nonneg hc ha.le)
    simpa only [mul_div_assoc] using this

namespace FiniteLaw

variable {α : Type*} [Fintype α] (P : FiniteLaw α)

/-- Extended-valued Bayes loss: positive prior mass at infinite loss stays infinite. -/
noncomputable def expectedKL (θ : α → ℝ) (q : ℝ) : ℝ≥0∞ :=
  ∑ x, ENNReal.ofReal (P.mass x) * Paper37.Boundary.kl (θ x) q

lemma exists_pos_mass_of_pos_event (E : α → Prop) [DecidablePred E]
    (h : 0 < P.eventMass E) : ∃ x, E x ∧ 0 < P.mass x := by
  by_contra! hnot
  have hnonpos : P.eventMass E ≤ 0 := by
    apply Finset.sum_nonpos
    intro x _
    by_cases hx : E x
    · simpa [hx] using hnot x hx
    · simp [hx]
  linarith

lemma expectedKL_top_of_atom {θ : α → ℝ} {q : ℝ} {x : α}
    (hm : 0 < P.mass x) (hkl : Paper37.Boundary.kl (θ x) q = ∞) :
    P.expectedKL θ q = ∞ := by
  have hne : ENNReal.ofReal (P.mass x) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hm)
  have hterm : ENNReal.ofReal (P.mass x) * Paper37.Boundary.kl (θ x) q = ∞ := by
    rw [hkl, ENNReal.mul_top hne]
  exact ENNReal.sum_eq_top.mpr ⟨x, Finset.mem_univ x, hterm⟩

lemma expectedKL_eq_ofReal_interior {θ : α → ℝ} {q : ℝ}
    (hθ : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    P.expectedKL θ q = ENNReal.ofReal
      (P.expectation (fun x => Paper37.Boundary.klReal (θ x) q)) := by
  unfold expectedKL expectation
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ =>
    mul_nonneg (P.nonneg x) (klReal_nonneg (hθ x).1 (hθ x).2 hq hq1))]
  apply Finset.sum_congr rfl
  intro x _
  rw [ENNReal.ofReal_mul (P.nonneg x)]
  congr 1
  unfold Paper37.Boundary.kl
  rw [if_neg]
  intro h
  rcases h with h | h
  · exact hq.ne' h.1
  · exact hq1.ne h.1

end FiniteLaw

/-- The full finite-posterior version of F.6, including q = 0 and q = 1
with their true infinite losses. -/
lemma finite_posterior_radius {α : Type*} [Fintype α]
    (P : FiniteLaw α) (M : α → Prop) [DecidablePred M]
    (θ : α → ℝ) {a η q : ℝ} (ha : 0 < a) (hη : 0 < η)
    (hθ : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1)
    (hzero : ∀ x, ¬ M x → θ x = 0)
    (hpositive : ∀ x, M x → 1 / a ≤ θ x)
    (hm : η ≤ P.eventMass M) (hmc : η ≤ P.eventMass (fun x => ¬ M x))
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ENNReal.ofReal (η * (Real.log 2 - 1 / 2) / a) ≤ P.expectedKL θ q := by
  rcases eq_or_lt_of_le hq with hq0 | hq0
  · subst q
    obtain ⟨x, hx, hpx⟩ := P.exists_pos_mass_of_pos_event M (lt_of_lt_of_le hη hm)
    have hθpos := lt_of_lt_of_le (one_div_pos.mpr ha) (hpositive x hx)
    have hkl : Paper37.Boundary.kl (θ x) 0 = ∞ := by
      simp [Paper37.Boundary.kl, hθpos.ne']
    rw [P.expectedKL_top_of_atom hpx hkl]
    exact le_top
  rcases eq_or_lt_of_le hq1 with hqone | hqone
  · subst q
    obtain ⟨x, hx, hpx⟩ := P.exists_pos_mass_of_pos_event (fun x => ¬ M x)
      (lt_of_lt_of_le hη hmc)
    have hkl : Paper37.Boundary.kl (θ x) 1 = ∞ := by
      rw [hzero x hx, Paper37.Boundary.kl_zero_one]
    rw [P.expectedKL_top_of_atom hpx hkl]
    exact le_top
  rw [P.expectedKL_eq_ofReal_interior hθ hq0 hqone]
  exact ENNReal.ofReal_le_ofReal (finite_posterior_radius_interior P M θ
    ha hη.le hθ hzero hpositive hm hmc hq0 hqone)

lemma radius_coefficient_pos : 0 < Real.log 2 - 1 / 2 := by
  have h := Real.log_lt_sub_one_of_pos (x := (1:ℝ)/2) (by norm_num) (by norm_num)
  have heq : Real.log ((1:ℝ)/2) = -Real.log 2 := by
    simpa using Real.log_inv (2:ℝ)
  rw [heq] at h
  linarith

/-- F.12 gives the parameter interval used by F.6. -/
lemma indicator_hazard_interval {α : Type*} (M : α → Prop) [DecidablePred M]
    (U : α → ℝ) {a : ℝ} (ha : 2 ≤ a)
    (hU : ∀ x, a / 2 ≤ U x ∧ U x ≤ a) :
    (∀ x, 0 ≤ (if M x then 1 / U x else 0) ∧
      (if M x then 1 / U x else 0) ≤ 1) ∧
    (∀ x, ¬ M x → (if M x then 1 / U x else 0) = 0) ∧
    (∀ x, M x → 1 / a ≤ (if M x then 1 / U x else 0) ∧
      (if M x then 1 / U x else 0) ≤ 2 / a) := by
  have ha0 : 0 < a := by linarith
  have hU1 : ∀ x, 1 ≤ U x := fun x => by linarith [(hU x).1]
  have hU0 : ∀ x, 0 < U x := fun x => lt_of_lt_of_le zero_lt_one (hU1 x)
  constructor
  · intro x
    by_cases hx : M x
    · simp only [if_pos hx]
      constructor
      · exact (one_div_pos.mpr (hU0 x)).le
      · simpa using one_div_le_one_div_of_le zero_lt_one (hU1 x)
    · simp [hx]
  constructor
  · intro x hx
    simp [hx]
  · intro x hx
    simp only [if_pos hx]
    constructor
    · exact one_div_le_one_div_of_le (hU0 x) (hU x).2
    · have h := one_div_le_one_div_of_le (half_pos ha0) (hU x).1
      simpa only [one_div_div] using h

/-- Full finite-posterior Bernoulli radius, directly for the F.12 hazard.
All outputs in [0,1] are covered, including infinite endpoint losses. -/
lemma finite_hazard_posterior_radius {α : Type*} [Fintype α]
    (P : FiniteLaw α) (M : α → Prop) [DecidablePred M]
    (U : α → ℝ) {a q : ℝ} (ha : 2 ≤ a)
    (hU : ∀ x, a / 2 ≤ U x ∧ U x ≤ a)
    (hm : 11 / 203 ≤ P.eventMass M)
    (hmc : 11 / 203 ≤ P.eventMass (fun x => ¬ M x))
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ENNReal.ofReal ((11 / 203) * (Real.log 2 - 1 / 2) / a) ≤
      P.expectedKL (fun x => if M x then 1 / U x else 0) q := by
  obtain ⟨hθ, hzero, hpositive⟩ := indicator_hazard_interval M U ha hU
  exact finite_posterior_radius P M _ (by linarith) (by norm_num) hθ hzero
    (fun x hx => (hpositive x hx).1) hm hmc hq hq1

/-- The posterior analytical step F.5--F.6 from an explicit prior and
likelihood, before the stationary observation model is instantiated. -/
lemma reweighted_hazard_radius {α : Type*} [Fintype α]
    (P : FiniteLaw α) (M : α → Prop) [DecidablePred M]
    (w U : α → ℝ) {m a q : ℝ} (hm : 0 < m)
    (hw : ∀ x, m ≤ w x ∧ w x ≤ 16 * m) (hZ : 0 < P.expectation w)
    (hp : 11 / 23 ≤ P.eventMass M) (hp1 : P.eventMass M ≤ 1 / 2)
    (ha : 2 ≤ a) (hU : ∀ x, a / 2 ≤ U x ∧ U x ≤ a)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ENNReal.ofReal ((11 / 203) * (Real.log 2 - 1 / 2) / a) ≤
      (P.reweight w (fun x => le_trans hm.le (hw x).1) hZ).expectedKL
        (fun x => if M x then 1 / U x else 0) q := by
  obtain ⟨hmem, hnonmem⟩ := P.reweighted_membership_stable M w hm hw hZ hp hp1
  exact finite_hazard_posterior_radius _ M U ha hU hmem hnonmem hq hq1

namespace FiniteLaw

variable {α : Type*} [Fintype α] [Nonempty α] (P : FiniteLaw α)

/-- The ratio formulation used after high-support marginalization in F.5. -/
lemma reweighted_membership_stable_of_pairwise (E : α → Prop) [DecidablePred E]
    (w : α → ℝ) (hwpos : ∀ x, 0 < w x)
    (hw : ∀ x y, w x ≤ 16 * w y)
    (hZ : 0 < P.expectation w)
    (hp : 11 / 23 ≤ P.eventMass E) (hp1 : P.eventMass E ≤ 1 / 2) :
    11 / 203 ≤ (P.reweight w (fun x => (hwpos x).le) hZ).eventMass E ∧
    11 / 203 ≤ (P.reweight w (fun x => (hwpos x).le) hZ).eventMass
      (fun x => ¬ E x) := by
  obtain ⟨x, _, hmin⟩ := Finset.exists_min_image Finset.univ w Finset.univ_nonempty
  exact P.reweighted_membership_stable E w (hwpos x)
    (fun y => ⟨hmin y (Finset.mem_univ y), hw y x⟩) hZ hp hp1

lemma expectation_pos_of_atom {f : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    {x : α} (hx : 0 < P.mass x) (hfx : 0 < f x) : 0 < P.expectation f := by
  have hsingle : P.mass x * f x ≤ P.expectation f := by
    unfold expectation
    exact Finset.single_le_sum (fun y _ => mul_nonneg (P.nonneg y) (hf y))
      (Finset.mem_univ x)
  exact lt_of_lt_of_le (mul_pos hx hfx) hsingle

/-- A common conditional high-support law and pointwise comparison give
positive, mutually comparable low-support marginal weights. -/
lemma marginalized_weights_positive_and_comparable
    {H : Type*} [Fintype H] (Q : FiniteLaw H) (w : α → H → ℝ)
    (hw0 : ∀ x h, 0 ≤ w x h)
    (hpositive : ∀ x, ∃ h, 0 < Q.mass h ∧ 0 < w x h)
    (hcomp : ∀ x y h, w x h ≤ 4 * w y h) :
    (∀ x, 0 < Q.expectation (w x)) ∧
    (∀ x y, Q.expectation (w x) ≤ 4 * Q.expectation (w y)) := by
  constructor
  · intro x
    obtain ⟨h, hh, hw⟩ := hpositive x
    have hsingle : Q.mass h * w x h ≤ Q.expectation (w x) := by
      unfold expectation
      exact Finset.single_le_sum (fun h' _ => mul_nonneg (Q.nonneg h') (hw0 x h'))
        (Finset.mem_univ h)
    exact lt_of_lt_of_le (mul_pos hh hw) hsingle
  · intro x y
    exact marginalized_weight_comparison Q (w x) (w y) (hcomp x y)

end FiniteLaw

/-- Pointwise F.6 remains valid after arbitrary private randomization of the
prediction. The source posterior remains the finite law P. -/
lemma randomized_finite_posterior_radius
    {α Ω : Type*} [Fintype α] [MeasurableSpace Ω]
    (ρ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ρ]
    (P : FiniteLaw α) (M : α → Prop) [DecidablePred M]
    (θ : α → ℝ) {a η : ℝ} (ha : 0 < a) (hη : 0 < η)
    (hθ : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1)
    (hzero : ∀ x, ¬ M x → θ x = 0)
    (hpositive : ∀ x, M x → 1 / a ≤ θ x)
    (hm : η ≤ P.eventMass M) (hmc : η ≤ P.eventMass (fun x => ¬ M x))
    (q : Ω → ℝ) (hq : ∀ ω, 0 ≤ q ω ∧ q ω ≤ 1) :
    ENNReal.ofReal (η * (Real.log 2 - 1 / 2) / a) ≤
      ∫⁻ ω, P.expectedKL θ (q ω) ∂ρ := by
  calc
    ENNReal.ofReal (η * (Real.log 2 - 1 / 2) / a) =
        ∫⁻ _ : Ω, ENNReal.ofReal (η * (Real.log 2 - 1 / 2) / a) ∂ρ := by simp
    _ ≤ ∫⁻ ω, P.expectedKL θ (q ω) ∂ρ := by
      exact MeasureTheory.lintegral_mono (fun ω => finite_posterior_radius P M θ
        ha hη hθ hzero hpositive hm hmc (hq ω).1 (hq ω).2)

/-- Tail cardinalities of the finite uniform support, with the source's gap
length d encoded by the natural index d-1. -/
lemma uniform_support_tail (μ : Paper37.Renewal.Law) (S : Finset ℕ) (a : ℝ)
    (hmass : ∀ d, μ.mass d = if d ∈ S then 1 / a else 0) (j : ℕ) :
    Paper37.Renewal.tail μ j = ((S.filter (fun d => j ≤ d)).card : ℝ) / a := by
  classical
  unfold Paper37.Renewal.tail
  rw [tsum_eq_sum (s := S) (fun d hd => by simp [hmass, hd])]
  calc
    (∑ d ∈ S, if j ≤ d then μ.mass d else 0) =
        ∑ d ∈ S, if j ≤ d then 1 / a else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [hmass, hd]
    _ = ((S.filter (fun d => j ≤ d)).card : ℝ) / a := by
      rw [← Finset.sum_filter]
      simp [div_eq_mul_inv]

/-- The mean of that same uniform support, matching m(S) in F.2. -/
lemma uniform_support_mean (μ : Paper37.Renewal.Law) (S : Finset ℕ) (a : ℝ)
    (hmass : ∀ d, μ.mass d = if d ∈ S then 1 / a else 0) :
    Paper37.Renewal.mean μ = (∑ d ∈ S, ((d : ℝ) + 1)) / a := by
  classical
  unfold Paper37.Renewal.mean
  rw [tsum_eq_sum (s := S) (fun d hd => by simp [hmass, hd])]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  simp [hmass, hd, div_eq_mul_inv]

/-- The completed-gap product is zero exactly on incompatible supports. -/
lemma uniform_support_gap_product (μ : Paper37.Renewal.Law)
    (S : Finset ℕ) (a : ℝ)
    (hmass : ∀ d, μ.mass d = if d ∈ S then 1 / a else 0) (ds : List ℕ) :
    (ds.map μ.mass).prod = if ds.toFinset ⊆ S then (1 / a) ^ ds.length else 0 := by
  classical
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.prod_cons, List.toFinset_cons,
      Finset.insert_subset_iff, List.length_cons, ih, hmass]
    by_cases hd : d ∈ S <;> by_cases hs : ds.toFinset ⊆ S <;>
      simp [hd, hs, pow_succ, mul_comm]

/-- Source F.8 for the actual stationary block mass, including both censoring
factors. This is valid for every uniform finite-support law, without assuming
a likelihood factorization. The block starts with j zeros, so J = j+1;
its terminal age is g-1. -/
lemma uniform_support_two_boundary_likelihood (μ : Paper37.Renewal.Law)
    (S : Finset ℕ) (a : ℝ)
    (hmass : ∀ d, μ.mass d = if d ∈ S then 1 / a else 0)
    (j : ℕ) (x : List Bool) :
    Paper37.Renewal.blockMass μ (List.replicate j false ++ true :: x) =
      (if (Paper37.Renewal.gapsFrom 0 x).toFinset ⊆ S then (1 : ℝ) else 0) *
        (1 / a) ^ ((Paper37.Renewal.gapsFrom 0 x).length + 2) *
        (((S.filter (fun d => j ≤ d)).card : ℝ) *
          ((S.filter (fun d => Paper37.Renewal.ageFrom 0 x ≤ d)).card : ℝ) /
            Paper37.Renewal.mean μ) := by
  classical
  rw [Paper37.Renewal.blockMass_two_boundaries, uniform_support_tail μ S a hmass,
    uniform_support_tail μ S a hmass, uniform_support_gap_product μ S a hmass]
  by_cases hs : (Paper37.Renewal.gapsFrom 0 x).toFinset ⊆ S
  · simp only [if_pos hs, one_mul, pow_add, pow_two]
    ring
  · simp [hs]

/-- An actual renewal law uniform on any nonempty finite set of gap indices.
Index d represents the strictly positive gap length d+1. -/
noncomputable def uniformSupportLaw (S : Finset ℕ) (hS : S.Nonempty) :
    Paper37.Renewal.Law := by
  classical
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  refine {
    mass := fun d => if d ∈ S then 1 / (S.card : ℝ) else 0
    nonneg := ?_
    total := ?_
    finiteMean := ?_ }
  · intro d
    split_ifs
    · exact (one_div_pos.mpr hcard).le
    · rfl
  · have h := hasSum_sum_of_ne_finset_zero (s := S) (L := .unconditional ℕ)
      (f := fun d => if d ∈ S then (1 : ℝ) / S.card else 0)
      (fun d hd => by simp [hd])
    have heq : (∑ d ∈ S, if d ∈ S then (1 : ℝ) / S.card else 0) = 1 := by
      calc
        _ = ∑ _d ∈ S, (1 : ℝ) / S.card := by
          apply Finset.sum_congr rfl
          intro d hd
          exact if_pos hd
        _ = 1 := by simp [hcard.ne']
    rw [heq] at h
    exact h
  · exact summable_of_ne_finset_zero (s := S)
      (fun d hd => by simp [hd])

@[simp] lemma uniformSupportLaw_mass (S : Finset ℕ) (hS : S.Nonempty) (d : ℕ) :
    (uniformSupportLaw S hS).mass d = if d ∈ S then 1 / (S.card : ℝ) else 0 := rfl

lemma uniformSupportLaw_mean (S : Finset ℕ) (hS : S.Nonempty) :
    Paper37.Renewal.mean (uniformSupportLaw S hS) =
      (∑ d ∈ S, ((d : ℝ) + 1)) / S.card :=
  uniform_support_mean _ S S.card (uniformSupportLaw_mass S hS)

lemma uniformSupportLaw_tail (S : Finset ℕ) (hS : S.Nonempty) (j : ℕ) :
    Paper37.Renewal.tail (uniformSupportLaw S hS) j =
      ((S.filter (fun d => j ≤ d)).card : ℝ) / S.card :=
  uniform_support_tail _ S S.card (uniformSupportLaw_mass S hS) j

/-- F.8 over every actual nonempty finite support; no Law or likelihood
relation is supplied as a premise. -/
lemma uniformSupportLaw_two_boundary_likelihood (S : Finset ℕ) (hS : S.Nonempty)
    (j : ℕ) (x : List Bool) :
    Paper37.Renewal.blockMass (uniformSupportLaw S hS)
      (List.replicate j false ++ true :: x) =
      (if (Paper37.Renewal.gapsFrom 0 x).toFinset ⊆ S then (1 : ℝ) else 0) *
        (1 / (S.card : ℝ)) ^ ((Paper37.Renewal.gapsFrom 0 x).length + 2) *
        (((S.filter (fun d => j ≤ d)).card : ℝ) *
          ((S.filter (fun d => Paper37.Renewal.ageFrom 0 x ≤ d)).card : ℝ) /
            Paper37.Renewal.mean (uniformSupportLaw S hS)) :=
  uniform_support_two_boundary_likelihood _ S S.card (uniformSupportLaw_mass S hS) j x

/-- The hard-prior half above a gives m(S) ≥ a/2. The hypothesis is only the
source support-cardinality condition, not a mean bound. -/
lemma uniformSupportLaw_mean_ge_half (S : Finset ℕ) (hS : S.Nonempty)
    {a : ℝ} (hcard : (S.card : ℝ) = a)
    (hlarge : a / 2 ≤ ((S.filter (fun d : ℕ => a ≤ (d : ℝ) + 1)).card : ℝ)) :
    a / 2 ≤ Paper37.Renewal.mean (uniformSupportLaw S hS) := by
  classical
  have ha : 0 < a := by rw [← hcard]; exact_mod_cast hS.card_pos
  have hsum : ((S.filter (fun d : ℕ => a ≤ (d : ℝ) + 1)).card : ℝ) * a ≤
      ∑ d ∈ S, ((d : ℝ) + 1) := by
    calc
      _ = ∑ _d ∈ S.filter (fun d : ℕ => a ≤ (d : ℝ) + 1), a := by simp
      _ = ∑ d ∈ S, if a ≤ (d : ℝ) + 1 then a else 0 := by rw [Finset.sum_filter]
      _ ≤ ∑ d ∈ S, ((d : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro d _
        split_ifs with hd
        · exact hd
        · positivity
  rw [uniformSupportLaw_mean, hcard]
  apply (le_div_iff₀ ha).2
  exact le_trans (mul_le_mul_of_nonneg_right hlarge ha.le) hsum

/-- The mean is bounded by any bound on all supported positive lengths. -/
lemma uniformSupportLaw_mean_le_support_cap (S : Finset ℕ) (hS : S.Nonempty)
    {B : ℝ} (hcap : ∀ d ∈ S, (d : ℝ) + 1 ≤ B) :
    Paper37.Renewal.mean (uniformSupportLaw S hS) ≤ B := by
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  rw [uniformSupportLaw_mean]
  apply (div_le_iff₀ hcard).2
  calc
    (∑ d ∈ S, ((d : ℝ) + 1)) ≤ ∑ _d ∈ S, B := Finset.sum_le_sum hcap
    _ = B * S.card := by simp [mul_comm]

/-- Every positive-probability gap in the hard-prior support is at most four
means, from the actual finite uniform law. -/
lemma uniformSupportLaw_standardized_support (S : Finset ℕ) (hS : S.Nonempty)
    {a : ℝ} (hcard : (S.card : ℝ) = a)
    (hlarge : a / 2 ≤ ((S.filter (fun d : ℕ => a ≤ (d : ℝ) + 1)).card : ℝ))
    (hcap : ∀ d ∈ S, (d : ℝ) + 1 ≤ 2 * a) :
    ∀ d, 0 < (uniformSupportLaw S hS).mass d →
      (d : ℝ) + 1 ≤ 4 * Paper37.Renewal.mean (uniformSupportLaw S hS) := by
  have hm := uniformSupportLaw_mean_ge_half S hS hcard hlarge
  intro d hd
  have hmem : d ∈ S := by
    by_contra hnot
    simpa [uniformSupportLaw_mass, hnot] using hd
  have := hcap d hmem
  linarith

/-- Two consecutive positive gap lengths force period one. Here the support
contains indices d and d+1, representing lengths d+1 and d+2. -/
lemma support_gcd_one_of_consecutive (S : Finset ℕ) {d : ℕ}
    (hd : d ∈ S) (hd1 : d + 1 ∈ S) : S.gcd (fun i => i + 1) = 1 := by
  have h1 : S.gcd (fun i => i + 1) ∣ d + 1 := Finset.gcd_dvd hd
  have h2 : S.gcd (fun i => i + 1) ∣ (d + 1) + 1 := Finset.gcd_dvd hd1
  have h := Nat.dvd_sub h2 h1
  have hone : S.gcd (fun i => i + 1) ∣ 1 := by simpa using h
  exact Nat.dvd_one.mp hone

end Paper37.LowerBound
