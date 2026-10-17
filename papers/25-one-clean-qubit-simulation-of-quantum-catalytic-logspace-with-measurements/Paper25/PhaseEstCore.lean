import Paper25.Filter
import Paper25.PhaseEst
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Appendix B: phase-estimation error bound (core)

For an eigenphase `2π φ` of `V`, phase estimation with `M = 2^m` labels has
amplitudes `α_j(φ) = (1/M) ∑_{r<M} exp(2π i r (φ - j/M))`.

If the circular distance between `φ` and `j/M` is `0 < Δ ≤ 1/2`, the geometric-sum
formula and `|sin(πΔ)| ≥ 2Δ` give `|α_j(φ)|² ≤ 1/(4 M² Δ²)`.

Fix `0 < ζ ≤ 1/2` with `Mζ ≥ 1`. The failure probability is at most
`(1/2) ∑_{r≥0} 1/(Mζ+r)² ≤ 1/(Mζ)`.

With `ζ = εδ/(32π)` and `M ≥ 4096/(δε²)`, the error in the ideal phase average
is at most `ε/8`.
-/

set_option maxHeartbeats 400000

noncomputable section

open scoped ComplexConjugate

namespace Paper25

/-! ## Sine lower bound -/

/-- `|sin(πΔ)| ≥ 2Δ` for `Δ ∈ [0, 1/2]`. -/
theorem sin_ge (Δ : ℝ) (h0 : 0 ≤ Δ) (h1 : Δ ≤ 1 / 2) :
    2 * Δ ≤ |Real.sin (Real.pi * Δ)| :=
  sin_pi_ge_two_mul Δ h0 h1

/-! ## Geometric sum for phase-estimation amplitudes -/

/-- `1 - cos θ = 2 sin²(θ/2)`. -/
lemma one_sub_cos_eq_two_sin_sq (θ : ℝ) :
    1 - Real.cos θ = 2 * Real.sin (θ / 2) ^ 2 := by
  have h : Real.sin (θ / 2) ^ 2 = 1 / 2 - Real.cos θ / 2 := by
    have := Real.sin_sq_eq_half_sub (θ / 2)
    rw [show (2:ℝ) * (θ / 2) = θ by ring] at this
    exact this
  nlinarith

/-- `|exp(iθ) - 1| = 2 |sin(θ/2)|`. -/
lemma norm_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp (θ * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hform : Complex.exp (θ * Complex.I) - 1
      = ((Real.cos θ - 1 : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hnsq : Complex.normSq (Complex.exp (θ * Complex.I) - 1)
      = (Real.cos θ - 1) ^ 2 + (Real.sin θ) ^ 2 := by
    rw [hform, Complex.normSq_add_mul_I]
  have htrig : (Real.cos θ - 1) ^ 2 + (Real.sin θ) ^ 2
      = 4 * Real.sin (θ / 2) ^ 2 := by
    have h1 : (Real.cos θ - 1) ^ 2 + Real.sin θ ^ 2 = 2 - 2 * Real.cos θ := by
      nlinarith [Real.cos_sq_add_sin_sq θ]
    have h2 : 2 - 2 * Real.cos θ = 4 * Real.sin (θ / 2) ^ 2 := by
      nlinarith [one_sub_cos_eq_two_sin_sq θ]
    nlinarith
  have hsq : ‖Complex.exp (θ * Complex.I) - 1‖ ^ 2
      = (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [Complex.sq_norm, hnsq, htrig, mul_pow, sq_abs, pow_two]
    ring
  have hnn : 0 ≤ ‖Complex.exp (θ * Complex.I) - 1‖ := norm_nonneg _
  have hnn2 : 0 ≤ 2 * |Real.sin (θ / 2)| := by positivity
  exact (sq_eq_sq₀ hnn hnn2).mp hsq

/-- Geometric-sum magnitude: `|∑_{r<M} exp(2π i r x)| ≤ 1/|sin(π x)|` when `sin(π x) ≠ 0`. -/
lemma geom_sum_exp_le (M : ℕ) (x : ℝ) (hM : 0 < M) (hsin : Real.sin (Real.pi * x) ≠ 0) :
    ‖∑ r ∈ Finset.range M, Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * x)‖
      ≤ 1 / |Real.sin (Real.pi * x)| := by
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * x) with hz
  have hzpow : ∀ r : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * x) = z ^ r := by
    intro r
    have h1 : (2 * Real.pi * Complex.I * (r : ℂ) * x : ℂ)
        = (r : ℂ) * (2 * Real.pi * Complex.I * x) := by ring
    rw [h1, Complex.exp_nat_mul]
  have hsum : (∑ r ∈ Finset.range M, Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * x))
      = ∑ r ∈ Finset.range M, z ^ r :=
    Finset.sum_congr rfl fun r _ => hzpow r
  have hzne : z ≠ 1 := by
    intro hc
    have h : Complex.exp (2 * Real.pi * Complex.I * x) = 1 := by rwa [hz] at hc
    have hform := norm_exp_mul_I_sub_one (2 * Real.pi * x)
    rw [show ((2 * Real.pi * x : ℝ) / 2) = Real.pi * x by ring] at hform
    have h0 : ‖Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) - 1‖ = 0 := by
      have h1 : Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)
          = Complex.exp (2 * Real.pi * Complex.I * x) := by
        congr 1
        push_cast
        ring
      rw [h1, h, sub_self, norm_zero]
    rw [h0] at hform
    have : (2:ℝ) * |Real.sin (Real.pi * x)| = 0 := by linarith
    exact hsin (by nlinarith [abs_eq_zero.1 (by nlinarith : |Real.sin (Real.pi * x)| = 0)])
  have hgeom : (∑ r ∈ Finset.range M, z ^ r) = (z ^ M - 1) / (z - 1) :=
    geom_sum_eq hzne M
  have hz1 : ‖z - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
    have h := norm_exp_mul_I_sub_one (2 * Real.pi * x)
    rw [show ((2 * Real.pi * x : ℝ) / 2) = Real.pi * x by ring] at h
    have h2 : Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) = z := by
      rw [hz]
      congr 1
      push_cast
      ring
    rw [h2] at h
    exact h
  have hzM : ‖z ^ M - 1‖ ≤ 2 := by
    have h := norm_exp_mul_I_sub_one (2 * Real.pi * (M : ℝ) * x)
    have h2 : Complex.exp ((2 * Real.pi * (M : ℝ) * x : ℝ) * Complex.I) = z ^ M := by
      have h3 : ((2 * Real.pi * (M : ℝ) * x : ℝ) * Complex.I)
          = ((M : ℂ) * (2 * Real.pi * Complex.I * x)) := by
        push_cast
        ring
      rw [h3, Complex.exp_nat_mul]
    rw [h2] at h
    have h3 : |Real.sin (2 * Real.pi * (M : ℝ) * x / 2)| ≤ 1 := Real.abs_sin_le_one _
    have h4 : (2:ℝ) * |Real.sin (2 * Real.pi * (M : ℝ) * x / 2)| ≤ 2 := by nlinarith
    rw [h]
    exact h4
  rw [hsum, hgeom, norm_div]
  have hsp : 0 < |Real.sin (Real.pi * x)| := abs_pos.mpr hsin
  have hz1pos : 0 < ‖z - 1‖ := by
    rw [hz1]
    positivity
  rw [div_le_iff₀ hz1pos, hz1]
  have h : (1 / |Real.sin (Real.pi * x)|) * (2 * |Real.sin (Real.pi * x)|) = 2 := by
    field_simp [hsp.ne']
  rw [h]
  exact hzM

/-- Phase-estimation geometric-sum bound:
`|(1/M) ∑_{r<M} exp(2π i r x)|² ≤ 1/(4 M² Δ²)` whenever `2Δ ≤ |sin(π x)|` and `0 < Δ`. -/
theorem geometric_sum_bound (M : ℕ) (x Δ : ℝ) (hM : 0 < M)
    (hΔ : 0 < Δ) (hsin : 2 * Δ ≤ |Real.sin (Real.pi * x)|) :
    ‖((M : ℂ)⁻¹ * ∑ r ∈ Finset.range M,
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * x))‖ ^ 2
      ≤ 1 / (4 * (M : ℝ) ^ 2 * Δ ^ 2) := by
  have hsin_ne : Real.sin (Real.pi * x) ≠ 0 := by
    intro hc
    have : |Real.sin (Real.pi * x)| = 0 := by rw [hc, abs_zero]
    nlinarith [abs_nonneg (Real.sin (Real.pi * x))]
  have hgeo := geom_sum_exp_le M x hM hsin_ne
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hnorm : ‖((M : ℂ)⁻¹ * ∑ r ∈ Finset.range M,
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * x))‖
      = ‖(∑ r ∈ Finset.range M,
          Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * x))‖ / (M : ℝ) := by
    rw [norm_mul, norm_inv]
    have hMnorm : ‖(M : ℂ)‖ = (M : ℝ) := RCLike.norm_natCast _
    rw [hMnorm, div_eq_mul_inv, mul_comm]
  rw [hnorm]
  have hsp : 0 < |Real.sin (Real.pi * x)| := abs_pos.mpr hsin_ne
  have hle2 : (1 / |Real.sin (Real.pi * x)|) / (M : ℝ) ≤ 1 / (2 * Δ * (M : ℝ)) := by
    rw [div_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsin]
  have hsq : (‖(∑ r ∈ Finset.range M,
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * x))‖ / (M : ℝ)) ^ 2
      ≤ (1 / (2 * Δ * (M : ℝ))) ^ 2 := by
    have hle : ‖(∑ r ∈ Finset.range M,
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * x))‖ / (M : ℝ)
        ≤ 1 / (2 * Δ * (M : ℝ)) := by
      calc ‖(∑ r ∈ Finset.range M,
            Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * x))‖ / (M : ℝ)
          ≤ (1 / |Real.sin (Real.pi * x)|) / (M : ℝ) := by gcongr
        _ ≤ 1 / (2 * Δ * (M : ℝ)) := hle2
    gcongr
  have hpow : (1 / (2 * Δ * (M : ℝ)) : ℝ) ^ 2 = 1 / (4 * (M : ℝ) ^ 2 * Δ ^ 2) := by
    have hΔne : (Δ : ℝ) ≠ 0 := ne_of_gt hΔ
    have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
    field_simp [hΔne, hMne]
    ring
  calc (‖(∑ r ∈ Finset.range M,
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * x))‖ / (M : ℝ)) ^ 2
      ≤ (1 / (2 * Δ * (M : ℝ))) ^ 2 := hsq
    _ = 1 / (4 * (M : ℝ) ^ 2 * Δ ^ 2) := hpow

/-- `|sin(π x)| = |sin(π · circDist x)|`. -/
lemma abs_sin_pi_eq_abs_sin_pi_circDist (x : ℝ) :
    |Real.sin (Real.pi * x)| = |Real.sin (Real.pi * circDist x)| := by
  have hsplit : Real.pi * x = Real.pi * (x - round x) + (round x : ℝ) * Real.pi := by
    push_cast
    ring
  rw [hsplit, Real.sin_add_int_mul_pi, abs_mul]
  have h1 : |(-1 : ℝ) ^ (round x)| = 1 := by
    have h : (-1 : ℝ) ^ (round x) = 1 ∨ (-1 : ℝ) ^ (round x) = -1 := by
      rcases Int.even_or_odd (round x : ℤ) with he | ho
      · obtain ⟨k, hk⟩ := he
        have hk2 : (round x : ℤ) = 2 * k := by omega
        rw [hk2, zpow_mul]
        have hz : ((-1 : ℝ) ^ (2 : ℤ)) = 1 := by
          rw [zpow_ofNat]
          norm_num
        rw [hz, one_zpow]
        exact Or.inl rfl
      · obtain ⟨k, hk⟩ := ho
        have hk2 : (round x : ℤ) = 2 * k + 1 := by omega
        rw [hk2, zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0), zpow_mul]
        have hz : ((-1 : ℝ) ^ (2 : ℤ)) = 1 := by
          rw [zpow_ofNat]
          norm_num
        rw [hz, one_zpow, one_mul]
        exact Or.inr rfl
    rcases h with h | h <;> rw [h] <;> norm_num
  rw [h1, one_mul]
  by_cases hle : 0 ≤ x - round x
  · have habs : |x - round x| = x - round x := abs_of_nonneg hle
    rw [circDist, habs]
  · have hlt : x - round x < 0 := lt_of_not_ge hle
    have habs : |x - round x| = -(x - round x) := abs_of_neg hlt
    rw [circDist, habs, mul_neg, Real.sin_neg, abs_neg]

/-- Jordan's inequality at the circular distance. -/
lemma circDist_sin (x : ℝ) : 2 * circDist x ≤ |Real.sin (Real.pi * x)| := by
  have h0 : 0 ≤ circDist x := circDist_nonneg x
  have h1 : circDist x ≤ 1 / 2 := circDist_le_half x
  have hj := sin_ge (circDist x) h0 h1
  rw [abs_sin_pi_eq_abs_sin_pi_circDist]
  exact hj

/-- Circular-distance form of the geometric-sum bound. -/
theorem geometric_sum_bound_circDist (M : ℕ) (x Δ : ℝ) (hM : 0 < M)
    (hΔ : 0 < Δ) (hΔle : Δ ≤ 1 / 2) (hcirc : circDist x = Δ) :
    ‖((M : ℂ)⁻¹ * ∑ r ∈ Finset.range M,
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * x))‖ ^ 2
      ≤ 1 / (4 * (M : ℝ) ^ 2 * Δ ^ 2) := by
  have hsin : 2 * Δ ≤ |Real.sin (Real.pi * x)| := by
    rw [← hcirc]
    exact circDist_sin x
  exact geometric_sum_bound M x Δ hM hΔ hsin

/-! ## Failure probability tail bound -/

/-- Telescoping estimate `1/(a+r+1)² ≤ 1/(a+r) - 1/(a+r+1)`. -/
lemma one_div_sq_le_telescope (a : ℝ) (ha : 0 < a) (r : ℕ) :
    (1 / (a + (r : ℝ) + 1) ^ 2 : ℝ) ≤ 1 / (a + r) - 1 / (a + r + 1) := by
  have h1 : 0 < a + (r : ℝ) := by positivity
  have h2 : 0 < a + (r : ℝ) + 1 := by positivity
  have h3 : (1 / (a + r) - 1 / (a + r + 1) : ℝ)
      = 1 / ((a + r) * (a + r + 1)) := by
    field_simp
    ring
  rw [h3, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Partial-sum telescoping: `∑_{r=0}^{N} 1/(a+r+1)² ≤ 1/a`. -/
lemma sum_one_div_sq_telescope (a : ℝ) (ha : 0 < a) (N : ℕ) :
    (∑ r ∈ Finset.range (N + 1), (1 / (a + (r : ℝ) + 1) ^ 2 : ℝ)) ≤ 1 / a := by
  have htele : (∑ r ∈ Finset.range (N + 1),
      ((1 / (a + r) - 1 / (a + r + 1) : ℝ))) = 1 / a - 1 / (a + (N : ℝ) + 1) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_succ]
      ring
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ Finset.range (N + 1)) =>
    one_div_sq_le_telescope a ha r)
  rw [htele] at hsum
  have hpos : 0 ≤ 1 / (a + (N : ℝ) + 1) := by positivity
  linarith

/-- Summability of `r ↦ 1/(a+r)²` for `a > 0`. -/
lemma summable_one_div_add_sq (a : ℝ) (ha : 0 < a) :
    Summable (fun r : ℕ => (1 / (a + (r : ℝ)) ^ 2 : ℝ)) := by
  have h : Summable (fun r : ℕ => (1 / |(r : ℝ) + a| ^ (2 : ℝ) : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow a 2).mpr (by norm_num)
  refine Summable.congr h (fun r => ?_)
  have hpos : (0 : ℝ) < (r : ℝ) + a := by positivity
  rw [abs_of_pos hpos]
  have h2 : ((r : ℝ) + a) ^ (2 : ℝ) = ((r : ℝ) + a) ^ 2 := by
    norm_num
  rw [h2, add_comm (r : ℝ)]

/-- Failure-probability tail bound:
`(1/2) ∑_{r≥0} 1/(a+r)² ≤ 1/a` whenever `1 ≤ a`. -/
theorem failure_prob_bound (a : ℝ) (ha : 1 ≤ a) :
    (1 / 2) * (∑' r : ℕ, (1 / (a + (r : ℝ)) ^ 2 : ℝ)) ≤ 1 / a := by
  have ha0 : 0 < a := by positivity
  have hsum := summable_one_div_add_sq a ha0
  have hsplit : (∑' r : ℕ, (1 / (a + (r : ℝ)) ^ 2 : ℝ))
      = 1 / a ^ 2 + (∑' r : ℕ, (1 / (a + (r : ℝ) + 1) ^ 2 : ℝ)) := by
    simpa only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one, ← add_assoc] using
      hsum.tsum_eq_zero_add
  have htail : (∑' r : ℕ, (1 / (a + (r : ℝ) + 1) ^ 2 : ℝ)) ≤ 1 / a := by
    have hconv : Summable (fun r : ℕ => (1 / (a + (r : ℝ) + 1) ^ 2 : ℝ)) := by
      convert summable_one_div_add_sq (a + 1) (by linarith : 0 < a + 1) using 1
      ext r
      congr 2 <;> ring
    refine hconv.tsum_le_of_sum_le ?_
    intro s
    by_cases hs : s.Nonempty
    · have hsub : ∑ r ∈ s, (1 / (a + (r : ℝ) + 1) ^ 2 : ℝ)
          ≤ ∑ r ∈ Finset.range (s.sup id + 1),
            (1 / (a + (r : ℝ) + 1) ^ 2 : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun r hr => ?_)
          (fun i _ _ => by positivity)
        simp only [Finset.mem_range]
        have : r ≤ s.sup id := Finset.le_sup (f := id) hr
        omega
      have h2 := sum_one_div_sq_telescope a ha0 (s.sup id)
      linarith
    · simp only [Finset.not_nonempty_iff_eq_empty] at hs
      rw [hs, Finset.sum_empty]
      positivity
  rw [hsplit]
  have h1 : (1 / 2 : ℝ) * (1 / a ^ 2 + (∑' r : ℕ, (1 / (a + (r : ℝ) + 1) ^ 2 : ℝ)))
      ≤ (1 / 2) * (1 / a ^ 2 + 1 / a) := by
    have := htail
    gcongr
  have h2 := pe_tail_scalar a ha
  linarith

/-! ## Lipschitz bound for the periodic filter -/

/-- Derivative of `g_δ(θ) = f_δ(cos θ)`. -/
lemma hasDerivAt_filterG (δ θ : ℝ) (hδ : δ ≠ 0) :
    HasDerivAt (filterG δ)
      (δ * (δ ^ 2 - Real.cos θ ^ 2) / (Real.cos θ ^ 2 + δ ^ 2) ^ 2 * (-Real.sin θ)) θ := by
  have h1 : HasDerivAt (Real.cos) (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have h2 : HasDerivAt (filterFn δ)
      (δ * (δ ^ 2 - Real.cos θ ^ 2) / (Real.cos θ ^ 2 + δ ^ 2) ^ 2) (Real.cos θ) := by
    have hnum : HasDerivAt (fun x : ℝ => δ * x) δ (Real.cos θ) := by
      simpa using (hasDerivAt_id (Real.cos θ)).const_mul δ
    have hden : HasDerivAt (fun x : ℝ => x ^ 2 + δ ^ 2) (2 * Real.cos θ) (Real.cos θ) := by
      have h := (hasDerivAt_id (Real.cos θ)).pow 2
      simpa [pow_two, two_mul] using h.add_const (δ ^ 2)
    have hden_ne : Real.cos θ ^ 2 + δ ^ 2 ≠ 0 := by
      nlinarith [sq_pos_of_ne_zero hδ, sq_nonneg (Real.cos θ)]
    have hdiv := hnum.div hden hden_ne
    have hclean : δ * (Real.cos θ ^ 2 + δ ^ 2) - δ * Real.cos θ * (2 * Real.cos θ)
        = δ * (δ ^ 2 - Real.cos θ ^ 2) := by ring
    have key : (fun x : ℝ => δ * x / (x ^ 2 + δ ^ 2)) = filterFn δ := by
      funext x; rfl
    rw [hclean] at hdiv
    exact hdiv
  have h := h2.comp θ h1
  simpa [filterG, mul_comm, mul_left_comm, mul_assoc] using h

lemma deriv_filterG (δ θ : ℝ) (hδ : δ ≠ 0) :
    deriv (filterG δ) θ
      = δ * (δ ^ 2 - Real.cos θ ^ 2) / (Real.cos θ ^ 2 + δ ^ 2) ^ 2 * (-Real.sin θ) :=
  (hasDerivAt_filterG δ θ hδ).deriv

/-- `|g_δ'(θ)| ≤ 1/δ` for `0 < δ`. -/
lemma deriv_filterG_abs_le (δ θ : ℝ) (hδ : 0 < δ) : |deriv (filterG δ) θ| ≤ 1 / δ := by
  rw [deriv_filterG δ θ hδ.ne']
  have h1 : |δ * (δ ^ 2 - Real.cos θ ^ 2) / (Real.cos θ ^ 2 + δ ^ 2) ^ 2| ≤ 1 / δ :=
    filter_deriv_bound δ (Real.cos θ) hδ
  have h2 : |(-Real.sin θ : ℝ)| ≤ 1 := by
    simpa [abs_neg] using Real.abs_sin_le_one θ
  rw [abs_mul]
  calc |δ * (δ ^ 2 - Real.cos θ ^ 2) / (Real.cos θ ^ 2 + δ ^ 2) ^ 2| * |(-Real.sin θ : ℝ)|
      ≤ (1 / δ) * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 1 / δ := by ring

/-- `g_δ` is `1/δ`-Lipschitz when `0 < δ`. -/
lemma filterG_abs_sub_le (δ θ φ : ℝ) (hδ : 0 < δ) :
    |filterG δ θ - filterG δ φ| ≤ |θ - φ| / δ := by
  have hdiff : ∀ x : ℝ, DifferentiableAt ℝ (filterG δ) x := fun x =>
    (hasDerivAt_filterG δ x hδ.ne').differentiableAt
  have hbound : ∀ x : ℝ, ‖deriv (filterG δ) x‖ ≤ 1 / δ := fun x => by
    simpa [Real.norm_eq_abs] using deriv_filterG_abs_le δ x hδ
  have hconv : Convex ℝ (Set.univ : Set ℝ) := convex_univ
  have hle := @Convex.norm_image_sub_le_of_norm_deriv_le ℝ ℝ _ _ _
    (filterG δ) Set.univ θ φ (1 / δ) (fun x _ => hdiff x) (fun x _ => hbound x) hconv
    (trivial : (θ : ℝ) ∈ (Set.univ : Set ℝ)) (trivial : (φ : ℝ) ∈ (Set.univ : Set ℝ))
  simpa [Real.norm_eq_abs, abs_sub_comm, div_eq_mul_inv, mul_comm] using hle

/-- With `ζ = εδ/(32π)`, the good-event change `2πζ/δ` equals `ε/16`. -/
lemma good_event_change_eq (δ ε ζ : ℝ) (hδ : 0 < δ)
    (hζdef : ζ = ε * δ / (32 * Real.pi)) :
    2 * Real.pi * ζ / δ = ε / 16 := by
  rw [hζdef]
  have hne : δ ≠ 0 := ne_of_gt hδ
  field_simp [hne, Real.pi_ne_zero]
  ring

/-- Phase change on the good event: `|θ - φ| ≤ 2πζ` implies `|g_δ θ - g_δ φ| ≤ 2πζ/δ`. -/
lemma filterG_phase_change (δ ζ θ φ : ℝ) (hδ : 0 < δ) (hζ : 0 ≤ ζ)
    (hdiff : |θ - φ| ≤ 2 * Real.pi * ζ) :
    |filterG δ θ - filterG δ φ| ≤ 2 * Real.pi * ζ / δ := by
  have hlip := filterG_abs_sub_le δ θ φ hδ
  have h : |θ - φ| / δ ≤ 2 * Real.pi * ζ / δ := by
    rw [div_le_div_iff₀ hδ (by positivity : 0 < δ)]
    nlinarith
  linarith

/-! ## Error budget of Appendix B -/

/-- Numeric error budget of Appendix B with `ζ = εδ/(32π)` and `M ≥ 4096/(δε²)`. -/
theorem phase_est_error_bound (δ ε ζ : ℝ) (M : ℕ)
    (hδ : 0 < δ) (hδle : δ ≤ 1) (hε : 0 < ε) (hεle : ε ≤ 1)
    (hζdef : ζ = ε * δ / (32 * Real.pi))
    (hMdef : (M : ℝ) ≥ 4096 / (δ * ε ^ 2)) :
    (0 < ζ ∧ ζ ≤ 1 / 2) ∧
    (1 ≤ (M : ℝ) * ζ ∧ 1 / ((M : ℝ) * ζ) ≤ Real.pi * ε / 128) ∧
    (2 * Real.pi * ζ / δ = ε / 16) ∧
    (Real.pi * ε / 128 < ε / 16) ∧
    (ε / 16 + Real.pi * ε / 128 ≤ ε / 8) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hζpos : 0 < ζ := by
    rw [hζdef]
    positivity
  have hζle : ζ ≤ 1 / 2 := by
    rw [hζdef]
    have h1 : ε * δ ≤ 1 := by nlinarith [hεle, hδle, hε, hδ]
    have h2 : ε * δ / (32 * Real.pi) ≤ 1 / (32 * Real.pi) := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 32 * Real.pi) (by positivity)]
      nlinarith
    have h3 : (1 / (32 * Real.pi) : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
      nlinarith [Real.pi_gt_three]
    linarith
  have hMge : (4096 : ℝ) ≤ (M : ℝ) * (δ * ε ^ 2) := by
    have hden : 0 < δ * ε ^ 2 := by positivity
    rw [← div_le_iff₀ hden]
    exact hMdef
  have hMζ : (128 / (Real.pi * ε) : ℝ) ≤ (M : ℝ) * ζ := by
    apply (div_le_iff₀ (by positivity : 0 < Real.pi * ε)).2
    rw [hζdef]
    have heq : (M : ℝ) * (ε * δ / (32 * Real.pi)) * (Real.pi * ε)
        = ((M : ℝ) * (δ * ε ^ 2)) / 32 := by
      field_simp
    rw [heq]
    linarith
  have hMζ1 : (1 : ℝ) ≤ (M : ℝ) * ζ := by
    have hπε : Real.pi * ε ≤ 4 := by nlinarith [Real.pi_le_four]
    have h : (1 : ℝ) ≤ 128 / (Real.pi * ε) := by
      apply (le_div_iff₀ (by positivity : 0 < Real.pi * ε)).2
      linarith
    exact h.trans hMζ
  have hinv : 1 / ((M : ℝ) * ζ) ≤ Real.pi * ε / 128 := by
    have hMζpos : 0 < (M : ℝ) * ζ := lt_of_lt_of_le (by norm_num) hMζ1
    have h := one_div_le_one_div_of_le (by positivity : 0 < 128 / (Real.pi * ε)) hMζ
    simpa only [one_div_div] using h
  have hgood : 2 * Real.pi * ζ / δ = ε / 16 :=
    good_event_change_eq δ ε ζ hδ hζdef
  have hbad : Real.pi * ε / 128 < ε / 16 := by
    rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 128) (by norm_num : (0:ℝ) < 16)]
    nlinarith [Real.pi_pos, hε, Real.pi_le_four]
  have htot : ε / 16 + Real.pi * ε / 128 ≤ ε / 8 := by
    have h1 : Real.pi * ε / 128 ≤ ε / 16 := by
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 128) (by norm_num : (0:ℝ) < 16)]
      nlinarith [Real.pi_pos, hε, Real.pi_le_four]
    linarith
  exact ⟨⟨hζpos, hζle⟩, ⟨hMζ1, hinv⟩, hgood, hbad, htot⟩

/-- Split a probability average into a good event with error `G` and a bad
 event with error at most one. The bad probability contributes additively. -/
lemma phase_average_split_bound
    {M : ℕ} (p d : Fin M → ℝ) (bad : Fin M → Prop) [DecidablePred bad]
    (G B : ℝ) (hG : 0 ≤ G)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    (hgood_d : ∀ j, ¬bad j → d j ≤ G)
    (hbad_d : ∀ j, bad j → d j ≤ 1)
    (hbad_p : ∑ j, p j * (if bad j then 1 else 0) ≤ B) :
    ∑ j, p j * d j ≤ G + B := by
  have hpoint : ∀ j, p j * d j ≤ p j * G + p j * (if bad j then 1 else 0) := by
    intro j
    by_cases hb : bad j
    · simp only [if_pos hb, mul_one]
      have hprod := mul_nonneg (hp j) hG
      have hd := mul_le_mul_of_nonneg_left (hbad_d j hb) (hp j)
      linarith
    · simp only [if_neg hb, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_left (hgood_d j hb) (hp j)
  calc
    ∑ j, p j * d j ≤ ∑ j, (p j * G + p j * (if bad j then 1 else 0)) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = G + ∑ j, p j * (if bad j then 1 else 0) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]
    _ ≤ G + B := add_le_add_left hbad_p G

/-- Ideal phase-average error with the full `ε` dependence from Appendix B. -/
theorem phase_est_average_error_eps
    {M : ℕ} (ε : ℝ) (hε : 0 ≤ ε) (p d : Fin M → ℝ)
    (bad : Fin M → Prop) [DecidablePred bad]
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    (hgood_d : ∀ j, ¬bad j → d j ≤ ε / 16)
    (hbad_d : ∀ j, bad j → d j ≤ 1)
    (hbad_p : ∑ j, p j * (if bad j then 1 else 0) ≤ Real.pi * ε / 128) :
    ∑ j, p j * d j ≤ ε / 8 := by
  have h := phase_average_split_bound p d bad (ε / 16) (Real.pi * ε / 128)
    (by positivity) hp hsum hgood_d hbad_d hbad_p
  have hπ := mul_le_mul_of_nonneg_right Real.pi_le_four hε
  linarith

/-- Unit-error specialization of the ideal phase-average bound. -/
theorem phase_est_average_error
    {M : ℕ} (p : Fin M → ℝ) (d : Fin M → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    (bad : Fin M → Prop) [DecidablePred bad]
    (hgood_d : ∀ j, ¬bad j → d j ≤ 1 / 16)
    (hbad_d : ∀ j, bad j → d j ≤ 1)
    (hbad_p : ∑ j, p j * (if bad j then 1 else 0) ≤ Real.pi / 128) :
    ∑ j, p j * d j ≤ 1 / 8 := by
  simpa using phase_est_average_error_eps 1 (by norm_num) p d bad hp hsum
    hgood_d hbad_d (by simpa using hbad_p)

end Paper25
