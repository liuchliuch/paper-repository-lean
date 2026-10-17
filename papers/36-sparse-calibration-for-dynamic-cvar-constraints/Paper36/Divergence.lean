import Paper36.CVaR
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Deterministic finite-law Hellinger and KL inequalities used by confidence-set transfer.
Zero denominator with positive numerator has infinite KL, as in the paper. -/
namespace Paper36.CVaR

open scoped BigOperators ENNReal

variable {Ω : Type*} [Fintype Ω]

theorem hellinger_nonneg (P Q : Law Ω) : 0 ≤ hellinger P Q := Real.sqrt_nonneg _

theorem hellinger_sq (P Q : Law Ω) : hellinger P Q ^ 2 = hellingerSq P Q :=
  Real.sq_sqrt (hellingerSq_nonneg P Q)

theorem hellingerSq_symm (P Q : Law Ω) : hellingerSq P Q = hellingerSq Q P := by
  unfold hellingerSq
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hellinger_symm (P Q : Law Ω) : hellinger P Q = hellinger Q P := by
  unfold hellinger
  rw [hellingerSq_symm]

/-- Hellinger is a genuine metric distance on finite probability laws: triangle inequality. -/
theorem hellinger_triangle (P Q R : Law Ω) :
    hellinger P R ≤ hellinger P Q + hellinger Q R := by
  let a : Ω → ℝ := fun i => Real.sqrt (P.mass i)-Real.sqrt (Q.mass i)
  let b : Ω → ℝ := fun i => Real.sqrt (Q.mass i)-Real.sqrt (R.mass i)
  let c : ℝ := ∑ i, a i*b i
  have ha : (∑ i, a i^2) = 2*hellingerSq P Q := by unfold a hellingerSq; ring
  have hb : (∑ i, b i^2) = 2*hellingerSq Q R := by unfold b hellingerSq; ring
  have hcross := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  rw [ha, hb] at hcross
  change c^2 ≤ (2*hellingerSq P Q)*(2*hellingerSq Q R) at hcross
  have hprod : 0 ≤ hellinger P Q*hellinger Q R :=
    mul_nonneg (hellinger_nonneg _ _) (hellinger_nonneg _ _)
  have hcp : c ≤ 2*hellinger P Q*hellinger Q R := by
    have hh : (2*hellinger P Q*hellinger Q R)^2 =
        (2*hellingerSq P Q)*(2*hellingerSq Q R) := by
      rw [mul_pow, mul_pow, hellinger_sq, hellinger_sq]
      ring
    nlinarith
  have hsum : hellingerSq P R = hellingerSq P Q+hellingerSq Q R+c := by
    unfold hellingerSq c a b
    have hi : ∀ i,
        (Real.sqrt (P.mass i)-Real.sqrt (R.mass i))^2 =
        (Real.sqrt (P.mass i)-Real.sqrt (Q.mass i))^2+
        (Real.sqrt (Q.mass i)-Real.sqrt (R.mass i))^2+
        2*((Real.sqrt (P.mass i)-Real.sqrt (Q.mass i))*
          (Real.sqrt (Q.mass i)-Real.sqrt (R.mass i))) := by intro i; ring
    simp only [hi, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hPR := hellinger_sq P R
  have hPQ := hellinger_sq P Q
  have hQR := hellinger_sq Q R
  nlinarith [hellinger_nonneg P R, hellinger_nonneg P Q, hellinger_nonneg Q R]

/-- Finite relative entropy, before adding the infinite-support branch. -/
noncomputable def klReal (P Q : Law Ω) : ℝ :=
  ∑ i, P.mass i*Real.log (P.mass i/Q.mass i)

/-- Absolute continuity of finite laws, stated as the exact support condition. -/
def SupportDominated (P Q : Law Ω) : Prop := ∀ i, 0 < P.mass i → 0 < Q.mass i

/-- KL retains the essential infinity convention whenever Q misses positive P mass. -/
noncomputable def kl (P Q : Law Ω) : ℝ≥0∞ := by
  classical
  exact if SupportDominated P Q then ENNReal.ofReal (klReal P Q) else ∞

private theorem sqrt_log_bound {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (Real.sqrt p-Real.sqrt q)^2 ≤ p*Real.log (p/q)-p+q := by
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hp2 := Real.sq_sqrt hp.le
  have hq2 := Real.sq_sqrt hq.le
  have hl : Real.log (Real.sqrt p/Real.sqrt q) = Real.log (p/q)/2 := by
    rw [Real.log_div (ne_of_gt hsp) (ne_of_gt hsq), Real.log_sqrt hp.le,
      Real.log_sqrt hq.le, Real.log_div (ne_of_gt hp) (ne_of_gt hq)]
    ring
  have hh := Real.one_sub_inv_le_log_of_pos (div_pos hsp hsq)
  rw [inv_div, hl] at hh
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*p by positivity)
  have he : p*(Real.sqrt q/Real.sqrt p) = Real.sqrt p*Real.sqrt q := by
    calc
      p*(Real.sqrt q/Real.sqrt p) = (Real.sqrt p)^2*(Real.sqrt q/Real.sqrt p) := by rw [hp2]
      _ = Real.sqrt p*Real.sqrt q := by field_simp
  nlinarith

/-- The deterministic KL--Hellinger comparison, with no positivity restrictions on P's zeros. -/
theorem two_hellingerSq_le_klReal (P Q : Law Ω) (hPQ : SupportDominated P Q) :
    2*hellingerSq P Q ≤ klReal P Q := by
  have hi : ∀ i, (Real.sqrt (P.mass i)-Real.sqrt (Q.mass i))^2 ≤
      P.mass i*Real.log (P.mass i/Q.mass i)-P.mass i+Q.mass i := by
    intro i
    rcases (P.nonneg i).eq_or_lt with hp | hp
    · rw [← hp]
      simp [Real.sq_sqrt (Q.nonneg i)]
    · exact sqrt_log_bound hp (hPQ i hp)
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ => hi i
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, P.total, Q.total,
    sub_add_cancel] at hh
  unfold hellingerSq klReal
  linarith

theorem klReal_nonneg (P Q : Law Ω) (hPQ : SupportDominated P Q) : 0 ≤ klReal P Q :=
  (mul_nonneg (by norm_num) (hellingerSq_nonneg P Q)).trans (two_hellingerSq_le_klReal P Q hPQ)

/-- 2 d_H²(P,Q) ≤ KL(P||Q), including the infinite case. -/
theorem two_hellingerSq_le_kl (P Q : Law Ω) :
    ENNReal.ofReal (2*hellingerSq P Q) ≤ kl P Q := by
  classical
  by_cases hPQ : SupportDominated P Q
  · simp only [kl, hPQ, if_true]
    exact ENNReal.ofReal_le_ofReal (two_hellingerSq_le_klReal P Q hPQ)
  · simp [kl, hPQ]

/-- A finite reverse-KL confidence radius implies the stated Hellinger radius. -/
theorem hellinger_le_of_kl_le (P Q : Law Ω) {ε : ℝ} (hε : 0 ≤ ε)
    (hkl : kl P Q ≤ ENNReal.ofReal ε) : hellinger P Q ≤ Real.sqrt (ε/2) := by
  have hh := (two_hellingerSq_le_kl P Q).trans hkl
  have hh' : 2*hellingerSq P Q ≤ ε := (ENNReal.ofReal_le_ofReal_iff hε).mp hh
  have hs : 0 ≤ ε/2 := div_nonneg hε (by norm_num)
  nlinarith [hellinger_sq P Q, Real.sq_sqrt hs,
    hellinger_nonneg P Q, Real.sqrt_nonneg (ε/2)]

/-- The confidence-set transfer used in C.5: both models are compared through the empirical law. -/
theorem hellinger_le_of_two_kl (P Q empirical : Law Ω) {εP εQ : ℝ}
    (hεP : 0 ≤ εP) (hεQ : 0 ≤ εQ)
    (hP : kl empirical P ≤ ENNReal.ofReal εP)
    (hQ : kl empirical Q ≤ ENNReal.ofReal εQ) :
    hellinger P Q ≤ Real.sqrt (εP/2)+Real.sqrt (εQ/2) := by
  have hp := hellinger_le_of_kl_le empirical P hεP hP
  have hq := hellinger_le_of_kl_le empirical Q hεQ hQ
  rw [hellinger_symm empirical P] at hp
  exact (hellinger_triangle P empirical Q).trans (add_le_add hp hq)

/-- Equal reverse-KL radii give the sqrt(2 ε) two-model radius. -/
theorem hellinger_le_of_two_kl_same (P Q empirical : Law Ω) {ε : ℝ} (hε : 0 ≤ ε)
    (hP : kl empirical P ≤ ENNReal.ofReal ε)
    (hQ : kl empirical Q ≤ ENNReal.ofReal ε) :
    hellinger P Q ≤ Real.sqrt (2*ε) := by
  have hh := hellinger_le_of_two_kl P Q empirical hε hε hP hQ
  have he : Real.sqrt (ε/2)+Real.sqrt (ε/2) = Real.sqrt (2*ε) := by
    have h1 := Real.sq_sqrt (show 0 ≤ ε/2 by positivity)
    have h2 := Real.sq_sqrt (show 0 ≤ 2*ε by positivity)
    nlinarith [Real.sqrt_nonneg (ε/2), Real.sqrt_nonneg (2*ε)]
  rwa [he] at hh

end Paper36.CVaR
