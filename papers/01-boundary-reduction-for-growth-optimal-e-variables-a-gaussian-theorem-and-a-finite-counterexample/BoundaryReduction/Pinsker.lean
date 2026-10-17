/- Pinsker's inequality, with the natural logarithm, on a finite alphabet. -/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Deriv
import BoundaryReduction.FiniteKL

open Real Set BigOperators
open scoped Classical
namespace BoundaryReduction

noncomputable def negEntropyOpen (t : ℝ) : ℝ :=
  t * log t + (1 - t) * log (1 - t)

lemma hasDerivAt_negEntropyOpen {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt negEntropyOpen (log t - log (1 - t)) t := by
  have ht1 : 1 - t ≠ 0 := by linarith [ht.2]
  have h := (hasDerivAt_mul_log (ne_of_gt ht.1)).add
    ((hasDerivAt_mul_log ht1).comp t
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)))
  convert h using 1 <;> simp [negEntropyOpen] <;> ring

lemma hasDerivAt_negEntropyOpen' {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => log x - log (1 - x)) (t⁻¹ + (1 - t)⁻¹) t := by
  have ht1 : 1 - t ≠ 0 := by linarith [ht.2]
  convert (hasDerivAt_log (ne_of_gt ht.1)).sub
    ((hasDerivAt_log ht1).comp t
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))) using 1 <;> simp <;> ring

lemma inv_add_inv_ge_four {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    4 ≤ t⁻¹ + (1 - t)⁻¹ := by
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have heq : t⁻¹ + (1 - t)⁻¹ = 1 / (t * (1 - t)) := by
    field_simp [ne_of_gt ht.1, ne_of_gt ht1]
    <;> ring
  rw [heq, le_div_iff₀ (mul_pos ht.1 ht1)]
  nlinarith [sq_nonneg (2 * t - 1)]

lemma two_point_pinsker {p q : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    2 * (p - q) ^ 2 ≤
      p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := by
  let H : ℝ → ℝ := fun x => negEntropyOpen x - 2 * x ^ 2
  let D : ℝ → ℝ := fun x => log x - log (1 - x) - 4 * x
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt H (D x) x := by
    intro x hx
    convert (hasDerivAt_negEntropyOpen hx).sub
      (((hasDerivAt_id x).pow 2).const_mul 2) using 1 <;> simp [H, D] <;> ring
  have hdd : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt D (x⁻¹ + (1 - x)⁻¹ - 4) x := by
    intro x hx
    convert (hasDerivAt_negEntropyOpen' hx).sub
      ((hasDerivAt_id x).const_mul 4) using 1 <;> simp [D]
  have hc : ConvexOn ℝ (Ioo (0 : ℝ) 1) H := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo _ _)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (f' := D) (f'' := fun x => x⁻¹ + (1 - x)⁻¹ - 4)
    · intro x hx
      exact (hd x (by simpa using hx)).hasDerivWithinAt
    · intro x hx
      exact (hdd x (by simpa using hx)).hasDerivWithinAt
    · intro x hx
      have := inv_add_inv_ge_four (t := x) (by simpa using hx)
      linarith
  have htangent : D q * (p - q) ≤ H p - H q := by
    rcases lt_trichotomy q p with h | h | h
    · have hs := hc.le_slope_of_hasDerivAt hq hp h (hd q hq)
      rw [slope_def_field] at hs
      exact (le_div_iff₀ (sub_pos.mpr h)).mp hs
    · subst p; simp
    · have hs := hc.slope_le_of_hasDerivAt hp hq h (hd q hq)
      rw [slope_def_field] at hs
      have hs' := (div_le_iff₀ (sub_pos.mpr h)).mp hs
      linarith
  have hp1 : 1 - p ≠ 0 := by linarith [hp.2]
  have hq1 : 1 - q ≠ 0 := by linarith [hq.2]
  rw [log_div (ne_of_gt hp.1) (ne_of_gt hq.1), log_div hp1 hq1]
  dsimp [H, D, negEntropyOpen] at htangent
  nlinarith
namespace FinProb

/-- The log-sum inequality on any finite event, for positive masses. -/
lemma log_sum_event {α : Type*} [Fintype α] (p q : FinProb α)
    (hp : ∀ y, 0 < p.w y) (hq : ∀ y, 0 < q.w y)
    (s : Finset α) (hs : s.Nonempty) :
    (∑ y ∈ s, p.w y) * log ((∑ y ∈ s, p.w y) / (∑ y ∈ s, q.w y)) ≤
      ∑ y ∈ s, p.w y * log (p.w y / q.w y) := by
  let P := ∑ y ∈ s, p.w y
  let Q := ∑ y ∈ s, q.w y
  have hP : 0 < P := Finset.sum_pos (fun y _ => hp y) hs
  have hQ : 0 < Q := Finset.sum_pos (fun y _ => hq y) hs
  have hpt : ∀ y ∈ s, p.w y * log (P / Q) + p.w y - q.w y * P / Q ≤
      p.w y * log (p.w y / q.w y) := by
    intro y _
    have hpy := hp y
    have hqy := hq y
    have hratio : 0 < q.w y * P / (p.w y * Q) := by positivity
    have hlog := log_le_sub_one_of_pos hratio
    rw [log_div (by positivity) (by positivity),
      log_mul (ne_of_gt (hq y)) (ne_of_gt hP),
      log_mul (ne_of_gt (hp y)) (ne_of_gt hQ)] at hlog
    have hm := mul_le_mul_of_nonneg_left hlog (le_of_lt (hp y))
    have heq : p.w y * (q.w y * P / (p.w y * Q) - 1) = q.w y * P / Q - p.w y := by
      field_simp [ne_of_gt hpy]
    rw [heq] at hm
    rw [log_div (ne_of_gt hP) (ne_of_gt hQ),
      log_div (ne_of_gt (hp y)) (ne_of_gt (hq y))]
    nlinarith
  have hsum := Finset.sum_le_sum hpt
  have heq : (∑ y ∈ s, (p.w y * log (P / Q) + p.w y - q.w y * P / Q)) =
      P * log (P / Q) := by
    simp only [div_eq_mul_inv, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul]
    change P * log (P * Q⁻¹) + P - Q * P * Q⁻¹ = P * log (P * Q⁻¹)
    field_simp
    <;> ring
  rw [heq] at hsum
  exact hsum

/-- Data processing to the indicator of a finite event. -/
lemma binary_kl_le {α : Type*} [Fintype α] (p q : FinProb α)
    (hp : ∀ y, 0 < p.w y) (hq : ∀ y, 0 < q.w y)
    (s : Finset α) (hs : s.Nonempty) (hsc : sᶜ.Nonempty) :
    let P := ∑ y ∈ s, p.w y
    let Q := ∑ y ∈ s, q.w y
    P * log (P / Q) + (1 - P) * log ((1 - P) / (1 - Q)) ≤ klPos p q := by
  dsimp
  have hpc : ∑ y ∈ sᶜ, p.w y = 1 - ∑ y ∈ s, p.w y := by
    have h := Finset.sum_add_sum_compl s p.w
    rw [p.sum_eq_one] at h
    linarith
  have hqc : ∑ y ∈ sᶜ, q.w y = 1 - ∑ y ∈ s, q.w y := by
    have h := Finset.sum_add_sum_compl s q.w
    rw [q.sum_eq_one] at h
    linarith
  have h := add_le_add (log_sum_event p q hp hq s hs)
    (log_sum_event p q hp hq sᶜ hsc)
  rw [hpc, hqc, Finset.sum_add_sum_compl] at h
  exact h

/-- Pinsker for an event; all constants use natural logarithms. -/
lemma pinsker_event {α : Type*} [Fintype α] (p q : FinProb α)
    (hp : ∀ y, 0 < p.w y) (hq : ∀ y, 0 < q.w y)
    (s : Finset α) (hs : s.Nonempty) (hsc : sᶜ.Nonempty) :
    2 * ((∑ y ∈ s, p.w y) - (∑ y ∈ s, q.w y)) ^ 2 ≤ klPos p q := by
  have hmem (r : FinProb α) (hr : ∀ y, 0 < r.w y) :
      (∑ y ∈ s, r.w y) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact Finset.sum_pos (fun y _ => hr y) hs
    · have hcomp : 0 < ∑ y ∈ sᶜ, r.w y :=
        Finset.sum_pos (fun y _ => hr y) hsc
      have h := Finset.sum_add_sum_compl s r.w
      rw [r.sum_eq_one] at h
      linarith
  exact (two_point_pinsker (hmem p hp) (hmem q hq)).trans
    (binary_kl_le p q hp hq s hs hsc)

/-- Pinsker's inequality on a finite alphabet with positive probabilities. -/
theorem pinsker {α : Type*} [Fintype α] (p q : FinProb α)
    (hp : ∀ y, 0 < p.w y) (hq : ∀ y, 0 < q.w y) :
    2 * (tv p q) ^ 2 ≤ klPos p q := by
  let s := Finset.univ.filter (fun y => q.w y ≤ p.w y)
  have hsum : (∑ y ∈ s, (p.w y - q.w y)) +
      (∑ y ∈ sᶜ, (p.w y - q.w y)) = 0 := by
    rw [Finset.sum_add_sum_compl, Finset.sum_sub_distrib,
      p.sum_eq_one, q.sum_eq_one, sub_self]
  have ht : tv p q = (∑ y ∈ s, p.w y) - (∑ y ∈ s, q.w y) := by
    unfold tv
    rw [← Finset.sum_add_sum_compl s]
    have hpos : ∑ y ∈ s, |p.w y - q.w y| = ∑ y ∈ s, (p.w y - q.w y) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact abs_of_nonneg (sub_nonneg.mpr (Finset.mem_filter.mp hy).2)
    have hneg : ∑ y ∈ sᶜ, |p.w y - q.w y| = -(∑ y ∈ sᶜ, (p.w y - q.w y)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      have h : ¬q.w y ≤ p.w y := by simpa [s] using hy
      exact abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))
    rw [hpos, hneg, ← Finset.sum_sub_distrib]
    linarith
  by_cases hs : s.Nonempty
  · by_cases hsc : sᶜ.Nonempty
    · rw [ht]
      exact pinsker_event p q hp hq s hs hsc
    · have he : sᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsc
      have ht0 : tv p q = 0 := by
        rw [ht, ← Finset.sum_sub_distrib]
        simpa [he] using hsum
      rw [ht0]
      simpa using klPos_nonneg hq (p := p)
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [ht, he]
    simpa using klPos_nonneg hq (p := p)

/-- The quantitative separator consequence used in Proposition 3.2. -/
theorem separator_kl_lower {α : Type*} [Fintype α] (p q : FinProb α)
    (hp : ∀ y, 0 < p.w y) (hq : ∀ y, 0 < q.w y)
    {g : α → ℝ} {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η)
    (hg : ∀ y, |g y| ≤ L) (hqg : expect q g = 0)
    (hpg : η ≤ expect p g) : η ^ 2 / (2 * L ^ 2) ≤ klPos p q := by
  have htv := abs_expect_le_two_mul_tv (p := p) hg hqg
  have ha : η ≤ 2 * L * tv p q := hpg.trans ((le_abs_self _).trans htv)
  have hb : 0 ≤ tv p q := by
    unfold tv
    positivity
  have hc := pinsker p q hp hq
  apply (div_le_iff₀ (by positivity : 0 < 2 * L ^ 2)).mpr
  nlinarith [sq_nonneg (2 * L * tv p q - η)]

end FinProb
end BoundaryReduction
