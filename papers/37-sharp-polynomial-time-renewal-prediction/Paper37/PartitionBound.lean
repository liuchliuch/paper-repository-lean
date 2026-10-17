import Paper37.AnalyticBounds
import Paper37.Envelope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.ZetaValues

/-! The classical integer-partition bound used in Appendix B. -/
noncomputable section
open scoped BigOperators
namespace Paper37.PartitionBound

open Paper37.AnalyticBounds

/-- A discrete exponential increment estimate. This gives the integral comparison
in B.5 without requiring a change of variables at the square-root endpoint. -/
lemma sqrt_exp_increment {c : ℝ} (hc : 0 < c) (n : ℕ) :
    (1 + 2 * Real.sqrt (n : ℝ) / c) * Real.exp (c * Real.sqrt (n : ℝ)) ≤
      (2 * Real.sqrt ((n+1 : ℕ) : ℝ) / c) *
        Real.exp (c * Real.sqrt ((n+1 : ℕ) : ℝ)) := by
  let u := Real.sqrt (n : ℝ)
  let v := Real.sqrt ((n+1 : ℕ) : ℝ)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have huv : u ≤ v := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n)
  have hu2 : u^2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hv2 : v^2 = (n : ℝ) + 1 := by simpa [v] using Real.sq_sqrt (show (0:ℝ) ≤ (n+1:ℕ) by positivity)
  have hlin : c + 2*u ≤ 2*v*(1 + c*(v-u)) := by
    have hsq : 0 ≤ (v-u)^2 := sq_nonneg (v-u)
    have hcq : 0 ≤ c * (v-u)^2 := mul_nonneg hc.le hsq
    nlinarith
  have hexp : 1 + c*(v-u) ≤ Real.exp (c*(v-u)) := by
    simpa [add_comm] using Real.add_one_le_exp (c*(v-u))
  have heq : Real.exp (c*v) = Real.exp (c*u) * Real.exp (c*(v-u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change (1+2*u/c)*Real.exp (c*u) ≤ (2*v/c)*Real.exp (c*v)
  rw [heq]
  apply (mul_le_mul_iff_left₀ hc).mp
  have hmain := (mul_le_mul_of_nonneg_right
    (hlin.trans (mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 2*v)))
    (Real.exp_nonneg (c*u)))
  field_simp at *
  nlinarith

/-- The elementary exponential sum estimate displayed after B.6. -/
theorem sum_exp_sqrt_lt_le {c : ℝ} (hc : 0 < c) (L : ℕ) :
    (∑ s ∈ Finset.range L, Real.exp (c * Real.sqrt (s : ℝ))) ≤
      (2 * Real.sqrt (L : ℝ) / c) * Real.exp (c * Real.sqrt (L : ℝ)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ]
    calc
      _ ≤ (2 * Real.sqrt (L : ℝ) / c) * Real.exp (c * Real.sqrt (L : ℝ)) +
          Real.exp (c * Real.sqrt (L : ℝ)) := add_le_add_right ih _
      _ = (1 + 2 * Real.sqrt (L : ℝ) / c) * Real.exp (c * Real.sqrt (L : ℝ)) := by ring
      _ ≤ _ := sqrt_exp_increment hc L

/-- The exact exponential cumulative estimate used in B.5, including `L = 0`. -/
theorem sum_exp_sqrt_le {c : ℝ} (hc : 0 < c) (L : ℕ) :
    (∑ s ∈ Finset.range (L+1), Real.exp (c * Real.sqrt (s : ℝ))) ≤
      (1 + 2 * Real.sqrt (L : ℝ) / c) * Real.exp (c * Real.sqrt (L : ℝ)) := by
  rw [Finset.sum_range_succ]
  calc
    _ ≤ (2 * Real.sqrt (L : ℝ) / c) * Real.exp (c * Real.sqrt (L : ℝ)) +
        Real.exp (c * Real.sqrt (L : ℝ)) := add_le_add_right (sum_exp_sqrt_lt_le hc L) _
    _ = _ := by ring

/-- A finite exponential progression is bounded by its continuous tail. -/
lemma sum_exp_neg_mul_le {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (∑ j : Fin n, Real.exp (-a * (j.val+1))) ≤ 1/a := by
  let r := Real.exp (-a)
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hp : 0 < 1-r := sub_pos.mpr hr1
  have hgeo : (∑ j : Fin n, r^(j.val+1)) ≤ r/(1-r) := by
    simp_rw [pow_succ]
    rw [← Finset.sum_mul]
    have hh := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hr0 hr1
    simp only [Nat.Ico_zero_eq_range, pow_zero] at hh
    simpa [mul_comm, div_mul_eq_mul_div, Fin.sum_univ_eq_sum_range] using
      mul_le_mul_of_nonneg_right hh hr0
  have hlin : a*r ≤ 1-r := by
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp a) hr0
    have he : Real.exp a * r = 1 := by
      dsimp [r]
      rw [← Real.exp_add]
      simp
    rw [he] at hh
    nlinarith
  have hfrac : r/(1-r) ≤ 1/a := by
    apply (div_le_div_iff₀ hp ha).2
    simpa [mul_comm] using hlin
  calc
    _ = ∑ j : Fin n, r^(j.val+1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    _ ≤ r/(1-r) := hgeo
    _ ≤ _ := hfrac

/-- The finite Euler product's logarithm has the sharp Basel bound. -/
theorem euler_log_sum_le {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    (∑ j : Fin n, -Real.log (1-Real.exp (-θ*(j.val+1)))) ≤ Real.pi^2/(6*θ) := by
  have hs (j : Fin n) : HasSum
      (fun m : ℕ => (Real.exp (-θ*(j.val+1)))^(m+1) / (m+1))
      (-Real.log (1-Real.exp (-θ*(j.val+1)))) := by
    apply Real.hasSum_pow_div_log_of_abs_lt_one
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_lt_one_iff.mpr
    have : (0:ℝ) < j.val+1 := by positivity
    nlinarith
  have hsum := hasSum_sum (s := Finset.univ) (fun j _ => hs j)
  have hz : HasSum (fun m : ℕ => (1:ℝ)/((m+1:ℝ)^2)) (Real.pi^2/6) := by
    have hh := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using hh
  have hbound : HasSum (fun m : ℕ => (1:ℝ)/((m+1:ℝ)^2) / θ)
      (Real.pi^2/(6*θ)) := by
    convert hz.div_const θ using 1 <;> ring
  apply hasSum_le _ hsum hbound
  intro m
  have hm : (0:ℝ) < m+1 := by positivity
  calc
    _ = (∑ j : Fin n, Real.exp (-(θ*(m+1))*(j.val+1))) / (m+1) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    _ ≤ (1/(θ*(m+1))) / (m+1) :=
      div_le_div_of_nonneg_right (sum_exp_neg_mul_le (mul_pos hθ hm) n) hm.le
    _ = _ := by field_simp

end Paper37.PartitionBound
