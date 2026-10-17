import PsgEst.ProbabilityChain
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import PsgEst.HardPair

/-!
# Minimax lower bound via two-point testing (Section 4)

Bernoulli row divergences, chain rule for KL on the path space, Pinsker,
and the resulting `Ω((p g ε²)^{-1})` lower bound.
-/

open Matrix BigOperators Real Finset Classical

namespace PsgEst

/-- Bernoulli relative entropy `KL(Ber u ‖ Ber v)`.
The boundary values are `-log (1-v)` at `u=0` and `-log v` at `u=1`
(with `log 0 = 0` in Lean's real-valued convention). -/
noncomputable def bernKL (u v : ℝ) : ℝ :=
  if u = 0 then -log (1-v)
  else if u = 1 then -log v
  else u * log (u / v) + (1 - u) * log ((1 - u) / (1 - v))

lemma bernKL_eq (u v : ℝ) (hu : 0 < u) (hu' : u < 1) :
    bernKL u v = u * log (u / v) + (1 - u) * log ((1 - u) / (1 - v)) := by
  unfold bernKL
  rw [if_neg (ne_of_gt hu), if_neg (ne_of_lt hu')]

/-- Paper inequality (24): for `0 < u < v < 1` with `v = (1+8ε) u ≤ 1/3`,
`KL(Ber u ‖ Ber v) ≤ 128 ε² u`. -/
theorem bernKL_le (u v ε : ℝ) (hu : 0 < u) (hv : u < v) (hv' : v ≤ 1 / 3)
    (hrel : v = (1 + 8 * ε) * u) (hε : 0 < ε) :
    bernKL u v ≤ 128 * ε ^ 2 * u := by
  have hv0 : 0 < v := lt_trans hu hv
  have hv1 : v < 1 := lt_of_le_of_lt hv' (by norm_num)
  have hu1 : u < 1 := lt_trans hv hv1
  have hu0 : 0 ≤ u := le_of_lt hu
  have h1u : 0 ≤ 1 - u := by linarith
  have h1v : 0 < 1 - v := by linarith
  have h1v' : 2 / 3 ≤ 1 - v := by linarith
  have h8ε : 1 ≤ 1 + 8 * ε := by linarith
  -- log bound
  have log1 : log (u / v) ≤ u / v - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hu hv0)
  have log2 : log ((1 - u) / (1 - v)) ≤ (1 - u) / (1 - v) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos (by linarith) h1v)
  have log1' : u * log (u / v) ≤ u * (u / v - 1) :=
    mul_le_mul_of_nonneg_left log1 hu0
  have log2' : (1 - u) * log ((1 - u) / (1 - v))
      ≤ (1 - u) * ((1 - u) / (1 - v) - 1) :=
    mul_le_mul_of_nonneg_left log2 h1u
  have hsum : u * log (u / v) + (1 - u) * log ((1 - u) / (1 - v))
      ≤ u * (u / v - 1) + (1 - u) * ((1 - u) / (1 - v) - 1) :=
    add_le_add log1' log2'
  -- algebraic identity: RHS = (u-v)² / (v(1-v))
  have hcalc : u * (u / v - 1) + (1 - u) * ((1 - u) / (1 - v) - 1)
      = (u - v) ^ 2 / (v * (1 - v)) := by
    have hv0' : v ≠ 0 := ne_of_gt hv0
    have h1v'' : 1 - v ≠ 0 := ne_of_gt h1v
    field_simp
    ring
  have hkl : bernKL u v ≤ (u - v) ^ 2 / (v * (1 - v)) := by
    rw [bernKL_eq u v hu hu1]
    exact hsum.trans (le_of_eq hcalc)
  -- substitute v = (1+8ε)u
  have huv : u - v = -8 * ε * u := by
    rw [hrel]
    ring
  have hsq : (u - v) ^ 2 = 64 * ε ^ 2 * u ^ 2 := by
    rw [huv]
    ring
  have hden : v * (1 - v) = (1 + 8 * ε) * u * (1 - v) := by rw [hrel]
  rw [hsq, hden] at hkl
  -- 64 ε² u² / ((1+8ε) u (1-v)) = 64 ε² u / ((1+8ε)(1-v))
  have hu_ne : u ≠ 0 := ne_of_gt hu
  have hsplit : 64 * ε ^ 2 * u ^ 2 / ((1 + 8 * ε) * u * (1 - v))
      = 64 * ε ^ 2 * u / ((1 + 8 * ε) * (1 - v)) := by
    have hu_ne : u ≠ 0 := ne_of_gt hu
    have h1v : 1 - v ≠ 0 := by linarith
    have h8 : (1 + 8 * ε) ≠ 0 := by linarith
    field_simp [hu_ne, h1v, h8]
  rw [hsplit] at hkl
  -- bound the denominator
  have hfac : (1 + 8 * ε) * (1 - v) ≥ 2 / 3 := by
    nlinarith [h1v', h8ε, le_of_lt hε, le_of_lt hv0, hv']
  have hcoeff : 64 * ε ^ 2 * u / ((1 + 8 * ε) * (1 - v))
      ≤ 128 * ε ^ 2 * u := by
    have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
    have huu : 0 ≤ ε ^ 2 * u := mul_nonneg hε2 hu0
    have hD : (1 + 8 * ε) * (1 - v) ≥ 1 / 2 := by linarith
    have hDpos : 0 < (1 + 8 * ε) * (1 - v) := lt_of_lt_of_le (by norm_num) hD
    have hrew : 64 * ε ^ 2 * u / ((1 + 8 * ε) * (1 - v))
        = 64 * (ε ^ 2 * u) / ((1 + 8 * ε) * (1 - v)) := by ring
    rw [hrew]
    have hhalf : (0:ℝ) < 1 / 2 := by norm_num
    calc 64 * (ε ^ 2 * u) / ((1 + 8 * ε) * (1 - v))
        ≤ 64 * (ε ^ 2 * u) / (1 / 2) := by
          rw [div_le_div_iff₀ hDpos hhalf]
          nlinarith [huu, hD]
      _ = 128 * (ε ^ 2 * u) := by ring
      _ = 128 * ε ^ 2 * u := by ring
  exact hkl.trans hcoeff

/-! ### Finite KL and TV -/

/-- KL divergence of finite real weight functions (natural log). -/
noncomputable def klDist {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ i, if p i = 0 then 0 else p i * log (p i / q i)

/-- Total variation distance `TV = (1/2) ∑ |p - q|`. -/
noncomputable def tvDist {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, |p i - q i|

/-- Event difference is at most total variation (assuming equal total mass). -/
lemma abs_sum_sub_le_tv {α : Type*} [Fintype α] [DecidableEq α] (p q : α → ℝ)
    (hsum : ∑ i, (p i - q i) = 0) (A : Finset α) :
    |∑ i ∈ A, p i - ∑ i ∈ A, q i| ≤ tvDist p q := by
  have hsplit : (∑ i ∈ A, (p i - q i)) = (1 / 2 : ℝ) *
      ((∑ i ∈ A, (p i - q i)) - ∑ i ∈ (Finset.univ \ A), (p i - q i)) := by
    have hcompl : ∑ i ∈ (Finset.univ \ A), (p i - q i)
        = ∑ i : α, (p i - q i) - ∑ i ∈ A, (p i - q i) := by
      have hsd : ∑ i ∈ (Finset.univ \ A), (p i - q i) + ∑ i ∈ A, (p i - q i)
          = ∑ i : α, (p i - q i) :=
        Finset.sum_sdiff (fun i _ => Finset.mem_univ i)
      linarith
    rw [hcompl, hsum]
    ring
  rw [← Finset.sum_sub_distrib, hsplit]
  have habs : |(1 / 2 : ℝ) * ((∑ i ∈ A, (p i - q i)) - ∑ i ∈ (Finset.univ \ A), (p i - q i))|
      = (1 / 2 : ℝ) * |(∑ i ∈ A, (p i - q i)) - ∑ i ∈ (Finset.univ \ A), (p i - q i)| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
  rw [habs]
  have htri : |(∑ i ∈ A, (p i - q i)) - ∑ i ∈ (Finset.univ \ A), (p i - q i)|
      ≤ |∑ i ∈ A, (p i - q i)| + |∑ i ∈ (Finset.univ \ A), (p i - q i)| :=
    abs_sub _ _
  have h1 : |∑ i ∈ A, (p i - q i)| ≤ ∑ i ∈ A, |p i - q i| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : |∑ i ∈ (Finset.univ \ A), (p i - q i)|
      ≤ ∑ i ∈ (Finset.univ \ A), |p i - q i| :=
    Finset.abs_sum_le_sum_abs _ _
  have h3 : ∑ i ∈ A, |p i - q i| + ∑ i ∈ (Finset.univ \ A), |p i - q i|
      = ∑ i : α, |p i - q i| := by
    have hsd : ∑ i ∈ (Finset.univ \ A), |p i - q i| + ∑ i ∈ A, |p i - q i|
        = ∑ i : α, |p i - q i| :=
      Finset.sum_sdiff (fun i _ => Finset.mem_univ i)
    linarith
  have h4 : |(∑ i ∈ A, (p i - q i)) - ∑ i ∈ (Finset.univ \ A), (p i - q i)|
      ≤ ∑ i : α, |p i - q i| := by
    linarith
  have h5 : (1 / 2 : ℝ) * |(∑ i ∈ A, (p i - q i)) - ∑ i ∈ (Finset.univ \ A), (p i - q i)|
      ≤ (1 / 2 : ℝ) * ∑ i : α, |p i - q i| :=
    mul_le_mul_of_nonneg_left h4 (by norm_num)
  unfold tvDist
  linarith

/-- Binary negative entropy `ψ(t) = t log t + (1-t) log(1-t)`. -/
noncomputable def bernPhi (t : ℝ) : ℝ := t * log t + (1 - t) * log (1 - t)

lemma bernPhi_eq_bregman (u v : ℝ) (hu : 0 < u) (hu' : u < 1) (hv : 0 < v) (hv' : v < 1) :
    bernKL u v = bernPhi u - bernPhi v - (log v - log (1 - v)) * (u - v) := by
  have hu1 : u < 1 := hu'
  rw [bernKL_eq u v hu hu1]
  have h1 : u * log (u / v) = u * log u - u * log v := by
    rw [log_div (ne_of_gt hu) (ne_of_gt hv)]
    ring
  have h2 : (1 - u) * log ((1 - u) / (1 - v)) = (1 - u) * log (1 - u) - (1 - u) * log (1 - v) := by
    rw [log_div (by linarith : (1 - u : ℝ) ≠ 0) (by linarith : (1 - v : ℝ) ≠ 0)]
    ring
  rw [h1, h2]
  unfold bernPhi
  ring

lemma bernPhi_deriv2 (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    1 / t + 1 / (1 - t) - 4 ≥ 0 := by
  have h1 : 0 < t * (1 - t) := mul_pos ht (by linarith)
  have h2 : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
  have h3 : 1 / t + 1 / (1 - t) = 1 / (t * (1 - t)) := by
    have ht0 : t ≠ 0 := ne_of_gt ht
    have h1t : (1 - t : ℝ) ≠ 0 := by linarith
    field_simp [ht0, h1t]
    ring
  rw [h3]
  rw [ge_iff_le, le_sub_iff_add_le]
  rw [le_div_iff₀ h1]
  nlinarith [h2]


/-! ### Binary Pinsker via Bregman / strong convexity of `bernPhi` -/

/-- Tangent-line lower bound for a convex function at an interior point. -/
lemma convexOn_tangent_le {f : ℝ → ℝ} {D : Set ℝ}
    (hf : ConvexOn ℝ D f)
    {v u : ℝ} (hvi : v ∈ interior D) (hu : u ∈ D)
    (hdiff : DifferentiableAt ℝ f v) :
    f v + deriv f v * (u - v) ≤ f u := by
  have hd : HasDerivAt f (deriv f v) v := hdiff.hasDerivAt
  rcases le_total v u with hle | hle
  · rcases eq_or_lt_of_le hle with rfl | hlt
    · rw [sub_self, mul_zero, add_zero]
    · have hIoi : UniqueDiffWithinAt ℝ (Set.Ioi v) v := _root_.uniqueDiffWithinAt_Ioi v
      have hright : HasDerivWithinAt f
          (sInf (slope f v '' {y ∈ D | v < y})) (Set.Ioi v) v :=
        hf.hasDerivWithinAt_sInf_slope_of_mem_interior hvi
      have hEq : deriv f v = sInf (slope f v '' {y ∈ D | v < y}) :=
        hIoi.eq_deriv _ hd.hasDerivWithinAt hright
      have hmem : slope f v u ∈ slope f v '' {y ∈ D | v < y} :=
        ⟨u, ⟨hu, hlt⟩, rfl⟩
      have hle' : sInf (slope f v '' {y ∈ D | v < y}) ≤ slope f v u :=
        _root_.csInf_le (bddBelow_slope_lt_of_mem_interior hf hvi) hmem
      rw [slope_def_field] at hle'
      rw [← hEq] at hle'
      have hpos : 0 < u - v := by linarith
      have hmul : deriv f v * (u - v) ≤ f u - f v :=
        (le_div_iff₀ hpos).1 hle'
      linarith
  · rcases eq_or_lt_of_le hle with rfl | hlt
    · rw [sub_self, mul_zero, add_zero]
    · have hIio : UniqueDiffWithinAt ℝ (Set.Iio v) v := _root_.uniqueDiffWithinAt_Iio v
      have hleft : HasDerivWithinAt f
          (sSup (slope f v '' {y ∈ D | y < v})) (Set.Iio v) v :=
        hf.hasDerivWithinAt_sSup_slope_of_mem_interior hvi
      have hEq : deriv f v = sSup (slope f v '' {y ∈ D | y < v}) :=
        hIio.eq_deriv _ hd.hasDerivWithinAt hleft
      have hmem : slope f v u ∈ slope f v '' {y ∈ D | y < v} :=
        ⟨u, ⟨hu, hlt⟩, rfl⟩
      have hle' : slope f v u ≤ sSup (slope f v '' {y ∈ D | y < v}) :=
        _root_.le_csSup (bddAbove_slope_gt_of_mem_interior hf hvi) hmem
      rw [slope_def_field] at hle'
      rw [← hEq] at hle'
      have hneg : u - v < 0 := by linarith
      have hmul : deriv f v * (u - v) ≤ f u - f v :=
        (div_le_iff_of_neg hneg).1 hle'
      linarith

lemma bernPhi_eq_neg_binEntropy (t : ℝ) : bernPhi t = -Real.binEntropy t := by
  rw [bernPhi, Real.binEntropy]; simp [log_inv, mul_neg]; ring

lemma differentiableAt_bernPhi (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    DifferentiableAt ℝ bernPhi t := by
  have h : DifferentiableAt ℝ (-Real.binEntropy) t :=
    (Real.differentiableAt_binEntropy (p := t) (ne_of_gt ht) (ne_of_lt ht')).neg
  have h2 : bernPhi = -Real.binEntropy := funext bernPhi_eq_neg_binEntropy
  rw [h2]; exact h

lemma hasDerivAt_bernPhi (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    HasDerivAt bernPhi (log t - log (1 - t)) t := by
  have h2 : bernPhi = -Real.binEntropy := funext bernPhi_eq_neg_binEntropy
  have h := (Real.hasDerivAt_binEntropy (p := t) (ne_of_gt ht) (ne_of_lt ht')).neg
  have h3 : -(log (1 - t) - log t) = log t - log (1 - t) := by ring
  rw [h2, ← h3]; exact h

lemma deriv_bernPhi (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    deriv bernPhi t = log t - log (1 - t) :=
  (hasDerivAt_bernPhi t ht ht').deriv

lemma hasDerivAt_two_sq (t : ℝ) : HasDerivAt (fun t => (2:ℝ) * t ^ 2) (4 * t) t := by
  have h := (hasDerivAt_const t (2:ℝ)).mul ((hasDerivAt_id' t).pow 2)
  convert h using 1 <;> ring

lemma hasDerivAt_g (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    HasDerivAt (fun t => bernPhi t - 2 * t ^ 2)
      (log t - log (1 - t) - 4 * t) t := by
  have h1 : HasDerivAt bernPhi (log t - log (1 - t)) t :=
    hasDerivAt_bernPhi t ht ht'
  have h2 : HasDerivAt (fun t => 2 * t ^ 2) (4 * t) t := hasDerivAt_two_sq t
  have h3 : HasDerivAt (fun t => -(2 * t ^ 2)) (-(4 * t)) t := h2.fun_neg
  have := h1.fun_add h3
  convert this using 1 <;> first | (funext x; ring) | ring

lemma differentiableAt_g (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    DifferentiableAt ℝ (fun t => bernPhi t - 2 * t ^ 2) t :=
  (hasDerivAt_g t ht ht').differentiableAt

lemma deriv_g_eq (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    deriv (fun t => bernPhi t - 2 * t ^ 2) t = log t - log (1 - t) - 4 * t :=
  (hasDerivAt_g t ht ht').deriv

lemma deriv_log_sub (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    deriv (fun t : ℝ => log t - log (1 - t) - 4 * t) t
      = 1 / t + 1 / (1 - t) - 4 := by
  have d1 : deriv (fun t : ℝ => log t) t = t⁻¹ := Real.deriv_log _
  have hd : HasDerivAt (fun t : ℝ => 1 - t) (-1 : ℝ) t := by
    have h := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id' t)
    convert h using 1 <;> ring
  have d2 : deriv (fun t : ℝ => log (1 - t)) t = -(1 - t)⁻¹ := by
    have hlog := (Real.hasDerivAt_log (by linarith : (1 - t : ℝ) ≠ 0)).comp t hd
    convert hlog.deriv using 1
    ring
  have d3 : deriv (fun t => (4:ℝ) * t) t = 4 := by
    have h := (hasDerivAt_const t (4:ℝ)).mul (hasDerivAt_id' t)
    convert h.deriv using 1
    ring
  have hA : (fun t : ℝ => log t - log (1 - t) - 4 * t)
      = fun t => (log t - log (1 - t)) - (4 * t) := rfl
  rw [hA, deriv_fun_sub]
  · rw [deriv_fun_sub, d1, d2, d3]
    · rw [inv_eq_one_div, inv_eq_one_div]; ring
    · exact differentiableAt_log (ne_of_gt ht)
    · exact (differentiableAt_log (by linarith)).comp t hd.differentiableAt
  · apply DifferentiableAt.sub
    · exact differentiableAt_log (ne_of_gt ht)
    · exact (differentiableAt_log (by linarith)).comp t hd.differentiableAt
  · exact (differentiableAt_const _).mul differentiableAt_fun_id

lemma f''_ge (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    (0:ℝ) ≤ (1 / t + 1 / (1 - t) - 4) := by
  have h1 : 0 < t * (1 - t) := mul_pos ht (by linarith)
  have h2 : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
  have h3 : 1 / t + 1 / (1 - t) = 1 / (t * (1 - t)) := by
    have ht0 : t ≠ 0 := ne_of_gt ht
    have h1t : (1 - t : ℝ) ≠ 0 := by linarith
    field_simp [ht0, h1t]; ring
  rw [h3]
  have : (1:ℝ) / (t * (1 - t)) ≥ 4 := by
    rw [ge_iff_le, le_div_iff₀ h1]; nlinarith
  linarith

/-- `g(t) = bernPhi t - 2 t^2` is convex on `(0,1)` (4-strong convexity of `bernPhi`). -/
lemma convexOn_bernPhi_sub :
    ConvexOn ℝ (Set.Ioo 0 1) (fun t => bernPhi t - 2 * t ^ 2) := by
  refine convexOn_of_deriv2_nonneg' (convex_Ioo 0 1) ?_ ?_ ?_
  · intro t ht
    exact (differentiableAt_g t ht.1 ht.2).differentiableWithinAt
  · intro t ht
    obtain ⟨ht0, ht1⟩ := Set.mem_Ioo.1 ht
    have heq : deriv (fun t => bernPhi t - 2 * t ^ 2)
        =ᶠ[nhds t] fun t => log t - log (1 - t) - 4 * t := by
      filter_upwards [Ioo_mem_nhds ht0 ht1] with x hx
      exact deriv_g_eq x hx.1 hx.2
    have hd : DifferentiableAt ℝ (fun t => log t - log (1 - t) - 4 * t) t := by
      apply DifferentiableAt.sub
      · apply DifferentiableAt.sub
        · exact differentiableAt_log (ne_of_gt ht0)
        · exact (differentiableAt_log (by linarith : (1 - t : ℝ) ≠ 0)).comp t
            ((differentiableAt_const _).sub differentiableAt_fun_id)
      · have h : HasDerivAt (fun t => (4:ℝ) * t) 4 t := by
          convert (hasDerivAt_const t (4:ℝ)).mul (hasDerivAt_id' t) <;> ring
        exact h.differentiableAt
    exact (heq.differentiableAt_iff.2 hd).differentiableWithinAt
  · intro t ht
    obtain ⟨ht0, ht1⟩ := Set.mem_Ioo.1 ht
    have heq : deriv (fun t => bernPhi t - 2 * t ^ 2)
        =ᶠ[nhds t] fun t => log t - log (1 - t) - 4 * t := by
      filter_upwards [Ioo_mem_nhds ht0 ht1] with x hx
      exact deriv_g_eq x hx.1 hx.2
    have h2 : deriv (deriv (fun t => bernPhi t - 2 * t ^ 2)) t
        = deriv (fun t => log t - log (1 - t) - 4 * t) t :=
      heq.deriv_eq
    have h3 : deriv (fun t : ℝ => log t - log (1 - t) - 4 * t) t
        = 1 / t + 1 / (1 - t) - 4 :=
      deriv_log_sub t ht0 ht1
    have : deriv^[2] (fun t => bernPhi t - 2 * t ^ 2) t
        = 1 / t + 1 / (1 - t) - 4 := by
      show deriv (deriv (fun t => bernPhi t - 2 * t ^ 2)) t = _
      rw [h2, h3]
    rw [this]
    exact f''_ge t ht0 ht1

lemma bernKL_bregman (u v : ℝ) (hu : 0 < u) (hu' : u < 1) (hv : 0 < v) (hv' : v < 1) :
    bernKL u v = bernPhi u - bernPhi v - (log v - log (1 - v)) * (u - v) := by
  rw [bernKL_eq u v hu hu']
  have h1 : u * log (u / v) = u * log u - u * log v := by
    rw [log_div (ne_of_gt hu) (ne_of_gt hv)]
    ring
  have h2 : (1 - u) * log ((1 - u) / (1 - v))
      = (1 - u) * log (1 - u) - (1 - u) * log (1 - v) := by
    rw [log_div (by linarith : (1 - u : ℝ) ≠ 0) (by linarith : (1 - v : ℝ) ≠ 0)]
    ring
  rw [h1, h2, bernPhi, bernPhi]
  ring

/-- Binary Pinsker: `KL(Ber u ‖ Ber v) ≥ 2 (u-v)²` for `u,v ∈ (0,1)`. -/
theorem binary_pinsker (u v : ℝ) (hu : 0 < u) (hu' : u < 1) (hv : 0 < v) (hv' : v < 1) :
    2 * (u - v) ^ 2 ≤ bernKL u v := by
  have huI : u ∈ Set.Ioo (0:ℝ) 1 := ⟨hu, hu'⟩
  have hvI : v ∈ Set.Ioo (0:ℝ) 1 := ⟨hv, hv'⟩
  have hconv := convexOn_bernPhi_sub
  have hd := differentiableAt_g v hv hv'
  have hvi : v ∈ interior (Set.Ioo (0:ℝ) 1) := by rwa [interior_Ioo]
  have htan := convexOn_tangent_le hconv hvi huI hd
  have hdg := deriv_g_eq v hv hv'
  rw [hdg] at htan
  have hkl := bernKL_bregman u v hu hu' hv hv'
  nlinarith [sq_nonneg (u - v)]


/-! ### Pinsker: `KL ≤ 1/8 ⇒ TV ≤ 1/4` -/

/-- Log-sum inequality via Jensen for `x ↦ x log x`. -/
lemma log_sum_ineq {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 < b i) :
    (∑ i, a i) * log ((∑ i, a i) / (∑ i, b i)) ≤ ∑ i, a i * log (a i / b i) := by
  classical
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    have hBpos : 0 < ∑ i, b i := by
      have h1 : b i₀ ≤ ∑ i ∈ Finset.univ, b i := by
        apply Finset.single_le_sum (fun j _ => (hb j).le)
        exact Finset.mem_univ i₀
      have h2 : 0 < b i₀ := hb i₀
      linarith
    set A := ∑ i, a i
    set B := ∑ i, b i
    have hAnonneg : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
    rcases eq_or_lt_of_le hAnonneg with hA0 | hApos
    · have hA : A = 0 := by linarith
      have hall : ∀ i, a i = 0 := by
        intro i
        have h2 : a i ≤ A := Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
        nlinarith [ha i]
      rw [hA, zero_mul]
      have hz : (∑ i, a i * log (a i / b i)) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hall i, zero_mul]
      rw [hz]
    · have hconv : ConvexOn ℝ (Set.Ici (0:ℝ)) (fun x => x * log x) := Real.convexOn_mul_log
      have hsumw : ∑ i, (b i / B) = 1 := by
        have h : (∑ i, b i) / B = 1 := by
          have : B = ∑ i, b i := rfl
          rw [this]
          exact div_self (ne_of_gt hBpos)
        have h2 : ∑ i, (b i / B) = (∑ i, b i) / B :=
          (Finset.sum_div (Finset.univ : Finset ι) (fun i => b i) B).symm
        rw [h2]; exact h
      have hw : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ b i / B :=
        fun i _ => div_nonneg (hb i).le hBpos.le
      have hx : ∀ i ∈ (Finset.univ : Finset ι), a i / b i ∈ Set.Ici (0:ℝ) :=
        fun i _ => div_nonneg (ha i) (hb i).le
      have hjensen : (fun x => x * log x) (∑ i, (b i / B) * (a i / b i))
          ≤ ∑ i, (b i / B) * ((fun x => x * log x) (a i / b i)) :=
        hconv.map_sum_le hw hsumw hx
      have heq1 : ∀ i, (b i / B) * (a i / b i) = a i / B := by
        intro i; field_simp [ne_of_gt (hb i)]
      have hcenter : (∑ i, (b i / B) * (a i / b i)) = A / B := by
        rw [Finset.sum_congr rfl (fun i _ => heq1 i)]
        have h2 : ∑ i, (a i / B) = (∑ i, a i) / B :=
          (Finset.sum_div (Finset.univ : Finset ι) (fun i => a i) B).symm
        have : A = ∑ i, a i := rfl
        linarith
      have heq2 : ∀ i, (b i / B) * ((a i / b i) * log (a i / b i))
          = (a i / B) * log (a i / b i) := by
        intro i; field_simp [ne_of_gt (hb i)]
      have hrhs : (∑ i, (b i / B) * ((a i / b i) * log (a i / b i)))
          = (1 / B) * ∑ i, a i * log (a i / b i) := by
        rw [Finset.sum_congr rfl (fun i _ => heq2 i)]
        have h2 : ∑ i, (a i / B) * log (a i / b i)
            = (∑ i, a i * log (a i / b i)) / B := by
          have heq3 : ∀ i, (a i / B) * log (a i / b i) = (a i * log (a i / b i)) / B := by
            intro i; field_simp [ne_of_gt (hb i)]
          rw [Finset.sum_congr rfl (fun i _ => heq3 i)]
          exact (Finset.sum_div _ _ _).symm
        rw [h2]
        field_simp [ne_of_gt hBpos]
      rw [hcenter, hrhs] at hjensen
      have hmul := mul_le_mul_of_nonneg_left hjensen (le_of_lt hBpos)
      have hleft : B * ((A / B) * log (A / B)) = A * log (A / B) := by
        field_simp [ne_of_gt hBpos]
      have hright : B * ((1 / B) * ∑ i, a i * log (a i / b i))
          = ∑ i, a i * log (a i / b i) := by field_simp [ne_of_gt hBpos]
      rw [hleft, hright] at hmul
      exact hmul
  · have hsum0 : (∑ i : ι, a i) = 0 := by
      rw [Finset.sum_eq_zero]; intro i _; exact absurd ⟨i⟩ hι
    have hsum1 : (∑ i : ι, b i) = 0 := by
      rw [Finset.sum_eq_zero]; intro i _; exact absurd ⟨i⟩ hι
    have hsum2 : (∑ i : ι, a i * log (a i / b i)) = 0 := by
      rw [Finset.sum_eq_zero]; intro i _; exact absurd ⟨i⟩ hι
    rw [hsum0, hsum1, hsum2]
    simp

/-- `∑_{i∈A} f i + ∑_{i∈Aᶜ} f i = ∑ i, f i`. -/
lemma sum_add_sum_compl {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) (A : Finset α) :
    (∑ i ∈ A, f i) + (∑ i ∈ Finset.univ \ A, f i) = ∑ i, f i := by
  have h : (∑ i ∈ Finset.univ \ A, f i) + (∑ i ∈ A, f i)
      = ∑ i ∈ Finset.univ, f i :=
    Finset.sum_sdiff (fun (i : α) (_ : i ∈ A) => Finset.mem_univ i)
  have h2 : (∑ i, f i) = ∑ i ∈ Finset.univ, f i := rfl
  linarith

lemma klDist_nonneg {α : Type*} [Fintype α] (μ ν : α → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 < ν i)
    (hsumμ : ∑ i, μ i = 1) (hsumν : ∑ i, ν i = 1) :
    0 ≤ klDist μ ν := by
  have hkl : klDist μ ν = ∑ i, μ i * log (μ i / ν i) := by
    unfold klDist
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h0 : μ i = 0
    · rw [if_pos h0, h0, zero_mul]
    · rw [if_neg h0]
  have h := log_sum_ineq μ ν hμ hν
  rw [hsumμ, hsumν] at h
  simp only [div_self (by norm_num : (1:ℝ) ≠ 0), log_one, mul_zero] at h
  rw [hkl]
  exact h

lemma log_sum_ineq_finset {α : Type*} [Fintype α] (a b : α → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 < b i) (A : Finset α) :
    (∑ i ∈ A, a i) * log ((∑ i ∈ A, a i) / (∑ i ∈ A, b i))
      ≤ ∑ i ∈ A, a i * log (a i / b i) := by
  classical
  have h := log_sum_ineq (fun i : A => a i) (fun i : A => b i)
    (fun i => ha i) (fun i => hb i)
  have h1 : (∑ i ∈ A, a i) = ∑ i : A, a i :=
    Finset.sum_subtype (p := fun x => x ∈ A) A (fun _ => Iff.rfl) _
  have h2 : (∑ i ∈ A, b i) = ∑ i : A, b i :=
    Finset.sum_subtype (p := fun x => x ∈ A) A (fun _ => Iff.rfl) _
  have h3 : (∑ i ∈ A, a i * log (a i / b i)) = ∑ i : A, a i * log (a i / b i) :=
    Finset.sum_subtype (p := fun x => x ∈ A) A (fun _ => Iff.rfl) _
  rw [h1, h2, h3]
  exact h

lemma mem_of_ne_empty {α : Type*} {A : Finset α} (hA : A ≠ ∅) : ∃ i, i ∈ A :=
  Finset.nonempty_of_ne_empty hA

lemma klDist_ge_bernKL {α : Type*} [Fintype α] [DecidableEq α]
    (μ ν : α → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 < ν i)
    (hsumμ : ∑ i, μ i = 1) (hsumν : ∑ i, ν i = 1)
    (A : Finset α) :
    bernKL (∑ i ∈ A, μ i) (∑ i ∈ A, ν i) ≤ klDist μ ν := by
  classical
  have hPdef : (∑ i ∈ A, μ i) + (∑ i ∈ Finset.univ \ A, μ i) = 1 := by
    have := sum_add_sum_compl μ A; linarith
  have hQdef : (∑ i ∈ A, ν i) + (∑ i ∈ Finset.univ \ A, ν i) = 1 := by
    have := sum_add_sum_compl ν A; linarith
  have hPge : 0 ≤ ∑ i ∈ A, μ i := Finset.sum_nonneg fun i _ => hμ i
  have hQpos : 0 < ∑ i ∈ A, ν i ∨ A = ∅ := by
    by_cases hA : A = ∅
    · exact Or.inr hA
    · left
      obtain ⟨i, hi⟩ := mem_of_ne_empty hA
      have : 0 < ν i := hν i
      have hle : ν i ≤ ∑ j ∈ A, ν j := Finset.single_le_sum (fun j _ => (hν j).le) hi
      exact lt_of_lt_of_le this hle
  have hQcpos : 0 < ∑ i ∈ Finset.univ \ A, ν i ∨ A = Finset.univ := by
    by_cases hA : A = Finset.univ
    · exact Or.inr hA
    · left
      have hne : (Finset.univ \ A) ≠ ∅ := by
        intro h
        apply hA
        apply Finset.eq_univ_of_forall
        intro i
        by_contra hnot
        have : i ∈ Finset.univ \ A := by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]; exact hnot
        rw [h] at this
        exact absurd this (by simp)
      obtain ⟨i, hi⟩ := mem_of_ne_empty hne
      have : 0 < ν i := hν i
      have hle : ν i ≤ ∑ j ∈ Finset.univ \ A, ν j :=
        Finset.single_le_sum (fun j _ => (hν j).le) hi
      exact lt_of_lt_of_le this hle
  have hkl : klDist μ ν = ∑ i, μ i * log (μ i / ν i) := by
    unfold klDist
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : μ i = 0
    · rw [if_pos h, h, zero_mul]
    · rw [if_neg h]
  have hsplit : (∑ i, μ i * log (μ i / ν i))
      = (∑ i ∈ A, μ i * log (μ i / ν i)) + (∑ i ∈ Finset.univ \ A, μ i * log (μ i / ν i)) :=
    (sum_add_sum_compl (fun i => μ i * log (μ i / ν i)) A).symm
  have hlsA := log_sum_ineq_finset μ ν hμ hν A
  have hlsAc := log_sum_ineq_finset μ ν hμ hν (Finset.univ \ A)
  have hcombine : (∑ i ∈ A, μ i) * log ((∑ i ∈ A, μ i) / (∑ i ∈ A, ν i))
      + (∑ i ∈ Finset.univ \ A, μ i) * log ((∑ i ∈ Finset.univ \ A, μ i) / (∑ i ∈ Finset.univ \ A, ν i))
      ≤ klDist μ ν := by
    rw [hkl, hsplit]
    exact add_le_add hlsA hlsAc
  by_cases hP0 : ∑ i ∈ A, μ i = 0
  · -- The complementary partition has mass one under μ.
    have hPc1 : (∑ i ∈ Finset.univ \ A, μ i) = 1 := by linarith
    have hQc : (∑ i ∈ Finset.univ \ A, ν i) = 1 - ∑ i ∈ A, ν i := by linarith
    rw [hP0, bernKL, if_pos rfl]
    simpa only [hP0, hPc1, hQc, zero_mul, zero_add, one_mul, one_div, log_inv]
      using hcombine
  · by_cases hP1 : ∑ i ∈ A, μ i = 1
    · -- P = 1
      have hPc0 : (∑ i ∈ Finset.univ \ A, μ i) = 0 := by linarith
      have hQpos' : 0 < ∑ i ∈ A, ν i := by
        rcases hQpos with h | h
        · exact h
        · rw [h] at hP1; simp at hP1
      rw [hP1]
      show bernKL 1 _ ≤ klDist μ ν
      unfold bernKL
      rw [if_neg (by norm_num : (1:ℝ) ≠ 0), if_pos rfl]
      have hsumA : (∑ i ∈ A, μ i * log (μ i / ν i)) = klDist μ ν := by
        have hz : (∑ i ∈ Finset.univ \ A, μ i * log (μ i / ν i)) = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          have hle : μ i ≤ ∑ j ∈ Finset.univ \ A, μ j :=
            Finset.single_le_sum (fun j _ => hμ j) hi
          rw [hPc0] at hle
          rw [show μ i = 0 from le_antisymm hle (hμ i), zero_mul]
        rw [hkl, hsplit, hz, add_zero]
      have hlog : log (1 / ∑ i ∈ A, ν i) ≤ klDist μ ν := by
        have hls := log_sum_ineq_finset μ ν hμ hν A
        rw [hP1] at hls
        rw [hsumA] at hls
        simpa using hls
      have hlog' : -log (∑ i ∈ A, ν i) = log (1 / ∑ i ∈ A, ν i) := by
        rw [one_div, log_inv]
      rw [hlog']
      exact hlog
    · -- 0 < P < 1
      have hPpos : 0 < ∑ i ∈ A, μ i := lt_of_le_of_ne hPge (Ne.symm hP0)
      have hPlt1 : (∑ i ∈ A, μ i) < 1 := by
        have hle : (∑ i ∈ A, μ i) ≤ 1 := by
          have := sum_add_sum_compl μ A
          have hPcge : 0 ≤ ∑ i ∈ Finset.univ \ A, μ i := Finset.sum_nonneg fun i _ => hμ i
          linarith
        exact lt_of_le_of_ne hle hP1
      have hPcpos : 0 < ∑ i ∈ Finset.univ \ A, μ i := by linarith
      have hQpos' : 0 < ∑ i ∈ A, ν i := by
        rcases hQpos with h | h
        · exact h
        · rw [h] at hP0; simp at hP0
      have hQcpos' : 0 < ∑ i ∈ Finset.univ \ A, ν i := by
        rcases hQcpos with h | h
        · exact h
        · rw [h] at hPlt1
          have : (∑ i ∈ A, μ i) = 1 := by
            rw [h]; simp [hsumμ]
          linarith
      have hPc : (∑ i ∈ Finset.univ \ A, μ i) = 1 - ∑ i ∈ A, μ i := by linarith
      have hQc : (∑ i ∈ Finset.univ \ A, ν i) = 1 - ∑ i ∈ A, ν i := by linarith
      have hbern : bernKL (∑ i ∈ A, μ i) (∑ i ∈ A, ν i)
          = (∑ i ∈ A, μ i) * log ((∑ i ∈ A, μ i) / (∑ i ∈ A, ν i))
            + (1 - ∑ i ∈ A, μ i) * log ((1 - ∑ i ∈ A, μ i) / (1 - ∑ i ∈ A, ν i)) :=
        bernKL_eq _ _ hPpos hPlt1
      rw [hbern]
      rw [← hPc, ← hQc]
      exact hcombine



/-- Pinsker form used in the paper: `KL ≤ 1/8 ⇒ TV ≤ 1/4`. -/
theorem pinsker_1_8 {α : Type*} [Fintype α] [DecidableEq α] (μ ν : α → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 < ν i)
    (hsumμ : ∑ i, μ i = 1) (hsumν : ∑ i, ν i = 1)
    (hKL : klDist μ ν ≤ 1 / 8) : tvDist μ ν ≤ 1 / 4 := by
  classical
  let A : Finset α := Finset.univ.filter (fun i => ν i ≤ μ i)
  have hAmem : ∀ i, i ∈ A ↔ ν i ≤ μ i := by
    intro i
    show i ∈ Finset.univ.filter _ ↔ _
    simp
  have hTV : tvDist μ ν = (∑ i ∈ A, μ i) - (∑ i ∈ A, ν i) := by
    unfold tvDist
    have habs : ∑ i, |μ i - ν i| = 2 * ((∑ i ∈ A, μ i) - (∑ i ∈ A, ν i)) := by
      have h1 : ∑ i, |μ i - ν i|
          = (∑ i ∈ A, |μ i - ν i|) + (∑ i ∈ Finset.univ \ A, |μ i - ν i|) :=
        (sum_add_sum_compl (fun i => |μ i - ν i|) A).symm
      have hA : ∀ i ∈ A, |μ i - ν i| = μ i - ν i := by
        intro i hi
        have := (hAmem i).1 hi
        exact abs_of_nonneg (by linarith)
      have hAc : ∀ i ∈ Finset.univ \ A, |μ i - ν i| = ν i - μ i := by
        intro i hi
        have hiA : i ∉ A := Finset.mem_sdiff.1 hi |>.2
        have hlt : μ i - ν i < 0 := by
          have := lt_of_not_ge (fun h => hiA ((hAmem i).2 h))
          linarith
        rw [abs_of_neg hlt]
        ring
      rw [h1, Finset.sum_congr rfl (fun i hi => hA i hi),
        Finset.sum_congr rfl (fun i hi => hAc i hi),
        Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      have h2 : (∑ i ∈ Finset.univ \ A, μ i) = 1 - (∑ i ∈ A, μ i) := by
        have := sum_add_sum_compl μ A; linarith
      have h3 : (∑ i ∈ Finset.univ \ A, ν i) = 1 - (∑ i ∈ A, ν i) := by
        have := sum_add_sum_compl ν A; linarith
      rw [h2, h3]
      ring
    rw [habs]
    ring
  have hPQ : (∑ i ∈ A, ν i) ≤ ∑ i ∈ A, μ i :=
    Finset.sum_le_sum fun i hi => (hAmem i).1 hi
  have hPge : 0 ≤ ∑ i ∈ A, μ i := Finset.sum_nonneg fun i _ => hμ i
  have hPle : (∑ i ∈ A, μ i) ≤ 1 := by
    have h := sum_add_sum_compl μ A
    have hPcge : 0 ≤ ∑ i ∈ Finset.univ \ A, μ i := Finset.sum_nonneg fun i _ => hμ i
    rw [hsumμ] at h
    linarith
  by_cases hP0 : ∑ i ∈ A, μ i = 0
  · have hQ0 : (∑ i ∈ A, ν i) = 0 := le_antisymm (by linarith) (Finset.sum_nonneg fun i _ => (hν i).le)
    rw [hTV, hP0, hQ0]
    linarith
  · by_cases hP1 : ∑ i ∈ A, μ i = 1
    · -- P = 1
      have hQpos : 0 < ∑ i ∈ A, ν i := by
        by_contra hnot
        push_neg at hnot
        have hQ0 : (∑ i ∈ A, ν i) = 0 := le_antisymm hnot (Finset.sum_nonneg fun i _ => (hν i).le)
        have hAne : A ≠ ∅ := by
          intro h; rw [h] at hP1; simp at hP1
        obtain ⟨i, hi⟩ := mem_of_ne_empty hAne
        have : 0 < ν i := hν i
        have hle : ν i ≤ ∑ j ∈ A, ν j := Finset.single_le_sum (fun j _ => (hν j).le) hi
        linarith
      have hdpi := klDist_ge_bernKL μ ν hμ hν hsumμ hsumν A
      rw [hP1] at hdpi
      have hbern : bernKL 1 (∑ i ∈ A, ν i) = -log (∑ i ∈ A, ν i) := by
        unfold bernKL
        rw [if_neg (by norm_num : (1:ℝ) ≠ 0), if_pos rfl]
      rw [hbern] at hdpi
      have hlog : -log (∑ i ∈ A, ν i) ≤ 1 / 8 := le_trans hdpi hKL
      have hQge34 : (3 / 4 : ℝ) ≤ ∑ i ∈ A, ν i := by
        by_contra hnot
        push_neg at hnot
        have h1 : log (1 / ∑ i ∈ A, ν i) = -log (∑ i ∈ A, ν i) := by
          rw [one_div, log_inv]
        have hcmp : (4:ℝ)/3 < 1 / ∑ i ∈ A, ν i := by
          rw [lt_div_iff₀ hQpos]
          nlinarith
        have h2 : log ((4:ℝ) / 3) < log (1 / ∑ i ∈ A, ν i) := by
          rw [Real.log_lt_log_iff (by norm_num) (div_pos (by norm_num) hQpos)]
          exact hcmp
        have h3 : (1/4:ℝ) ≤ log ((4:ℝ) / 3) := by
          have := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 4/3 by norm_num)
          have hcalc : (1:ℝ) - (((4:ℝ)/3)⁻¹) = 1/4 := by norm_num
          linarith
        have h4 : (1/4:ℝ) < log (1 / ∑ i ∈ A, ν i) := lt_of_le_of_lt h3 h2
        rw [h1] at h4
        linarith
      rw [hTV, hP1]
      linarith
    · -- 0 < P < 1
      have hPpos : 0 < ∑ i ∈ A, μ i := lt_of_le_of_ne hPge (Ne.symm hP0)
      have hPlt1 : (∑ i ∈ A, μ i) < 1 := lt_of_le_of_ne hPle hP1
      have hQpos : 0 < ∑ i ∈ A, ν i := by
        by_contra hnot
        push_neg at hnot
        have hQ0 : (∑ i ∈ A, ν i) = 0 := le_antisymm hnot (Finset.sum_nonneg fun i _ => (hν i).le)
        have hAne : A = ∅ := by
          by_contra hne
          obtain ⟨i, hi⟩ := mem_of_ne_empty hne
          have : 0 < ν i := hν i
          have hle : ν i ≤ ∑ j ∈ A, ν j := Finset.single_le_sum (fun j _ => (hν j).le) hi
          linarith
        rw [hAne] at hP0
        simp at hP0
      have hQlt1 : (∑ i ∈ A, ν i) < 1 := lt_of_le_of_lt hPQ hPlt1
      have hdpi := klDist_ge_bernKL μ ν hμ hν hsumμ hsumν A
      have hpins := binary_pinsker _ _ hPpos hPlt1 hQpos hQlt1
      have h2 : 2 * ((∑ i ∈ A, μ i) - (∑ i ∈ A, ν i)) ^ 2 ≤ 1 / 8 :=
        le_trans hpins (le_trans hdpi hKL)
      have hPQge : 0 ≤ (∑ i ∈ A, μ i) - (∑ i ∈ A, ν i) := by linarith
      have h4' : (∑ i ∈ A, μ i) - (∑ i ∈ A, ν i) ≤ 1 / 4 := by
        by_contra hnot
        push_neg at hnot
        have : ((1:ℝ)/4) < ((∑ i ∈ A, μ i) - (∑ i ∈ A, ν i)) := hnot
        have : ((1:ℝ)/4)^2 < ((∑ i ∈ A, μ i) - (∑ i ∈ A, ν i))^2 := by nlinarith
        nlinarith
      rw [hTV]
      exact h4'

/-- Two-point testing: `KL ≤ 1/8` implies every event differs by at most `1/4`. -/
theorem event_diff_le_of_kl_le {α : Type*} [Fintype α] [DecidableEq α] (μ ν : α → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 < ν i)
    (hsumμ : ∑ i, μ i = 1) (hsumν : ∑ i, ν i = 1)
    (hKL : klDist μ ν ≤ 1 / 8) (A : Finset α) :
    |∑ i ∈ A, μ i - ∑ i ∈ A, ν i| ≤ 1 / 4 :=
  (abs_sum_sub_le_tv μ ν (by
    rw [Finset.sum_sub_distrib, hsumμ, hsumν]
    ring) A).trans
    (pinsker_1_8 μ ν hμ hν hsumμ hsumν hKL)

/-! ### Minimax lower bound (abstract two-point / Le Cam) -/

open Classical in
/-- An estimator is relatively `ε`-accurate at confidence `2/3` on `C(d,p,g)`
from every deterministic initial state. -/
def relativelyAccurate (n d : ℕ) [NeZero d] (est : (Fin (n + 1) → Fin d) → ℝ) (p g ε : ℝ) : Prop :=
  ∀ (S : Stoch d) (st : Stationary S) (_hπ : p ≤ Stationary.star st) (_hg : g ≤ gammaPS S st),
  ∀ (x0 : Fin d),
    let mu0 : Fin d → ℝ := fun i => if i = x0 then 1 else 0
    2 / 3 ≤ pathMeasure S.P mu0
      {X | |est X - gammaPS S st| ≤ ε * gammaPS S st}

/-- Sample size of the best relatively accurate estimator (`sInf ∅ = 0`). -/
noncomputable def nStar (d : ℕ) [NeZero d] (p g ε : ℝ) : ℕ :=
  sInf {n : ℕ | ∃ est : (Fin (n + 1) → Fin d) → ℝ, relativelyAccurate n d est p g ε}

/-! ### Hard-pair package and path-KL bound -/

/-- Strict positivity of `hardP` entries. -/
lemma hardP_pos {d : ℕ} (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) (hs : 0 < s) (hs' : s < 1) :
    ∀ i j, 0 < hardP d p s i j := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := cast_d_sub_one_pos hd
  intro i j
  unfold hardP
  have hdne : d ≠ 0 := by omega
  simp only [hdne, if_false]
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · -- 1 - (1-p)*s > 0
    have hlt : (1 - p) * s < 1 := by
      have h1 : (1 - p) < 1 := sub_lt_self _ hp
      nlinarith [one_sub_p_pos hd hp hp', le_of_lt hs]
    simp [hi, hj]
    linarith
  · simp [hi, hj]
    exact div_pos (mul_pos (one_sub_p_pos hd hp hp') hs) hd1
  · simp [hi, hj]
    exact mul_pos hp hs
  · simp [hi, hj]
    exact div_pos (one_sub_ps_pos hd hp hp' hs hs') hd1

/-- Path probability is strictly positive under positive data and a positive start. -/
lemma pathProb_pos {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (hP : ∀ i j, 0 < P i j)
    (X : Fin (n + 1) → Fin d) (hmu : 0 < mu0 (X 0)) :
    0 < pathProb P mu0 X := by
  unfold pathProb
  exact mul_pos hmu (Finset.prod_pos fun t _ => hP _ _)

/-- `hardMu` attains its minimum `p` and is always `≥ p`. -/
lemma hardMu_min (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) :
    (∀ i : Fin d, p ≤ hardMu d p i) ∧ hardMu d p ⟨0, by omega⟩ = p := by
  have h0 : hardMu d p ⟨0, by omega⟩ = p := by
    unfold hardMu; simp
  refine ⟨?_, h0⟩
  intro i
  unfold hardMu
  by_cases hi : i.val = 0
  · simp [hi]
  · simp only [hi, if_false]
    have hpm : p * ((d - 1 : ℕ) : ℝ) ≤ 1 - p := by
      have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
      have h1 : p * (d : ℝ) ≤ 1 := (le_div_iff₀ hdpos).mp hp'
      rw [cast_d_sub_one hd]
      nlinarith
    have hd1pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := cast_d_sub_one_pos hd
    rw [le_div_iff₀ hd1pos]
    linarith

/-- `Stationary.star` of the hard pair equals `p`. -/
lemma hard_star (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) (hs : 0 < s) (hs' : s < 1) :
    Stationary.star (hardSt hd p s hp hp' hs hs') = p := by
  haveI : NeZero d := ⟨by omega⟩
  have hmin := hardMu_min d hd p hp hp'
  obtain ⟨hle, h0⟩ := hmin
  -- star = min of mu
  have heq : (hardSt hd p s hp hp' hs hs').mu = hardMu d p := rfl
  show (Finset.univ : Finset (Fin d)).inf' _ _ = p
  rw [heq]
  have hle' : ∀ b ∈ (Finset.univ : Finset (Fin d)), p ≤ hardMu d p b := fun i _ => hle i
  have h1 : (Finset.univ : Finset (Fin d)).inf' Finset.univ_nonempty (hardMu d p) ≤ p := by
    have h := Finset.inf'_le (b := (⟨0, by omega⟩ : Fin d))
      (Finset.mem_univ _) (f := hardMu d p)
    have key : (Finset.univ : Finset (Fin d)).inf' Finset.univ_nonempty (hardMu d p)
        = (Finset.univ : Finset (Fin d)).inf'
            ⟨(⟨0, by omega⟩ : Fin d), Finset.mem_univ _⟩ (hardMu d p) := by
      rfl
    rw [key]
    rw [h0] at h
    exact h
  have h2 : p ≤ (Finset.univ : Finset (Fin d)).inf' Finset.univ_nonempty (hardMu d p) :=
    (Finset.le_inf'_iff (H := Finset.univ_nonempty) (f := hardMu d p) (a := p)).2 hle'
  exact le_antisymm h1 h2

/-- Parameter bounds for the hard-pair rates `s0,s1`. -/
lemma hardP_rates (g ε : ℝ) (hg : 0 < g) (hg' : g ≤ 1 / 8) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    0 < 1 - sqrt (1 - g) ∧ 1 - sqrt (1 - g) < 1
      ∧ 0 < (1 + 8 * ε) * (1 - sqrt (1 - g))
      ∧ (1 + 8 * ε) * (1 - sqrt (1 - g)) < 1 := by
  have h1mg : 0 ≤ 1 - g := by linarith
  set s0 : ℝ := 1 - sqrt (1 - g)
  have hs0_pos : 0 < s0 := by
    have hlt : Real.sqrt (1 - g) < 1 := by
      have h1 : 1 - g < 1 := by linarith
      have := Real.sqrt_lt_sqrt h1mg h1
      rwa [Real.sqrt_one] at this
    have : 0 ≤ Real.sqrt (1 - g) := Real.sqrt_nonneg _
    show 0 < 1 - Real.sqrt (1 - g)
    linarith
  have hs0_lt : s0 < 1 := by
    have hpos : 0 < Real.sqrt (1 - g) :=
      Real.sqrt_pos.mpr (by linarith : (0:ℝ) < 1 - g)
    show 1 - Real.sqrt (1 - g) < 1
    linarith
  have hs0_le : s0 ≤ 1 / 15 := by
    have h2g : 0 < 2 - g := by linarith
    have hs0_eq : s0 * (2 - s0) = g := by
      have hsq : Real.sqrt (1 - g) ^ 2 = 1 - g := Real.sq_sqrt h1mg
      have hform : (1 - Real.sqrt (1 - g)) * (2 - (1 - Real.sqrt (1 - g)))
          = 1 - Real.sqrt (1 - g) ^ 2 := by ring
      have h2 : 0 < 2 - s0 := by
        have : 0 ≤ Real.sqrt (1 - g) := Real.sqrt_nonneg _
        nlinarith
      nlinarith
    have hden : 2 - g ≤ 2 - s0 := by nlinarith
    have hs0_bd : s0 ≤ g / (2 - g) := by
      have h2 : 0 < 2 - s0 := by
        have : 0 ≤ Real.sqrt (1 - g) := Real.sqrt_nonneg _
        nlinarith
      have hs0eq : s0 = g / (2 - s0) := by
        rw [eq_div_iff (ne_of_gt h2)]; nlinarith
      rw [hs0eq]
      exact div_le_div_of_nonneg_left hg.le (by linarith) (by linarith)
    have hgb : g / (2 - g) ≤ 1 / 15 := by
      rw [div_le_iff₀ h2g]
      nlinarith [hg']
    linarith
  have hs1_pos : 0 < (1 + 8 * ε) * s0 := mul_pos (by linarith) hs0_pos
  have hs1_lt : (1 + 8 * ε) * s0 < 1 := by nlinarith
  constructor
  · exact hs0_pos
  constructor
  · exact hs0_lt
  constructor
  · show 0 < (1 + 8 * ε) * (1 - Real.sqrt (1 - g))
    exact hs1_pos
  · show (1 + 8 * ε) * (1 - Real.sqrt (1 - g)) < 1
    exact hs1_lt

/-- If `n ≤ 1/(2048 p g ε²)` then the hard-pair path KL is at most `1/8`. -/
theorem pathKL_le_one_eighth (d n : ℕ) (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hn : (n : ℝ) ≤ 1 / (2048 * p * g * ε ^ 2)) :
    256 * (n : ℝ) * p * g * ε ^ 2 ≤ 1 / 8 := by
  have hpos : 0 < p * g * ε ^ 2 := mul_pos (mul_pos hp hg) (sq_pos_of_ne_zero (ne_of_gt hε))
  have hne : (p * g * ε ^ 2) ≠ 0 := ne_of_gt hpos
  have hrew : (256 * (n : ℝ) * p * g * ε ^ 2) = 256 * (n : ℝ) * (p * g * ε ^ 2) := by ring
  rw [hrew]
  calc 256 * (n : ℝ) * (p * g * ε ^ 2)
      ≤ 256 * (1 / (2048 * p * g * ε ^ 2)) * (p * g * ε ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hpos)
        apply mul_le_mul_of_nonneg_left hn (by norm_num)
    _ = 256 / 2048 := by
      field_simp [hne]
    _ = (1 / 8 : ℝ) := by norm_num

/-- Abstract two-point / Le Cam contradiction.  If two models have disjoint success
intervals for `est` and their path laws satisfy `klDist ≤ 1/8`, then `est` cannot be
accurate (w.p. ≥ 2/3) on both: thresholding gives a test with error sum ≤ 2/3, while
Pinsker forces error sum ≥ 3/4. -/
theorem two_point_no_accurate {α : Type*} [Fintype α] [DecidableEq α]
    (μ ν : α → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 < ν i)
    (hsumμ : ∑ i, μ i = 1) (hsumν : ∑ i, ν i = 1)
    (hKL : klDist μ ν ≤ 1 / 8)
    (est : α → ℝ) (g0 g1 ε : ℝ)
    (hdisj : (1 + ε) * g0 < (1 - ε) * g1)
    (hacc0 : 2 / 3 ≤ ∑ i, μ i * (if |est i - g0| ≤ ε * g0 then 1 else 0))
    (hacc1 : 2 / 3 ≤ ∑ i, ν i * (if |est i - g1| ≤ ε * g1 then 1 else 0)) :
    False := by
  have hPinsker : tvDist μ ν ≤ 1 / 4 := pinsker_1_8 μ ν hμ hν hsumμ hsumν hKL
  have hts : ∃ t : ℝ, (1 + ε) * g0 < t ∧ t < (1 - ε) * g1 := by
    refine ⟨((1 + ε) * g0 + (1 - ε) * g1) / 2, ?_, ?_⟩ <;> linarith
  obtain ⟨t, ht0, ht1⟩ := hts
  let A : Finset α := Finset.univ.filter (fun i => t ≤ est i)
  have hTV : |∑ i ∈ A, μ i - ∑ i ∈ A, ν i| ≤ tvDist μ ν :=
    abs_sum_sub_le_tv μ ν (by
      rw [Finset.sum_sub_distrib, hsumμ, hsumν]
      ring) A
  have herr : (1 : ℝ) - tvDist μ ν
      ≤ (∑ i ∈ A, μ i) + (∑ i ∈ Finset.univ \ A, ν i) := by
    have h1 : ∑ i ∈ Finset.univ \ A, ν i = 1 - ∑ i ∈ A, ν i := by
      have := sum_add_sum_compl ν A; linarith
    rw [h1]
    have := hTV
    have := abs_le.1 this
    linarith
  have hacc0' : (∑ i, μ i * (if |est i - g0| ≤ ε * g0 then 1 else 0)) ≤ 1 - ∑ i ∈ A, μ i := by
    have hpt : ∀ i, (if |est i - g0| ≤ ε * g0 then (1:ℝ) else 0)
        ≤ (if t ≤ est i then (0:ℝ) else 1) := by
      intro i
      by_cases hs : |est i - g0| ≤ ε * g0
      · rw [if_pos hs]
        have hle : est i ≤ (1 + ε) * g0 := by
          have h1 : est i - g0 ≤ |est i - g0| := le_abs_self _
          linarith
        have hnot : ¬(t ≤ est i) := by intro h; linarith
        rw [if_neg hnot]
      · rw [if_neg hs]
        by_cases ht : t ≤ est i
        · rw [if_pos ht]
        · rw [if_neg ht]
          norm_num
    have hsum : (∑ i, μ i * (if |est i - g0| ≤ ε * g0 then 1 else 0))
        ≤ ∑ i, μ i * (if t ≤ est i then (0:ℝ) else 1) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpt i) (hμ i)
    have h2 : (∑ i, μ i * (if t ≤ est i then (0:ℝ) else 1)) = 1 - ∑ i ∈ A, μ i := by
      have hA : ∀ i, (μ i * (if t ≤ est i then (0:ℝ) else 1))
          = (if i ∈ A then (0:ℝ) else μ i) := by
        intro i
        have hmem : i ∈ A ↔ t ≤ est i := by
          show i ∈ Finset.univ.filter (fun i => t ≤ est i) ↔ _
          simp
        by_cases ht : t ≤ est i
        · rw [if_pos ht, if_pos (hmem.2 ht), mul_zero]
        · rw [if_neg ht, if_neg (fun h => ht (hmem.1 h)), mul_one]
      rw [Finset.sum_congr rfl (fun i _ => hA i)]
      have h3 : (∑ i, (if i ∈ A then (0:ℝ) else μ i))
          = ∑ i ∈ Finset.univ.filter (fun i => i ∉ A), μ i := by
        have hif : ∀ i, (if i ∈ A then (0:ℝ) else μ i) = (if i ∉ A then μ i else 0) := by
          intro i
          by_cases hi : i ∈ A
          · simp [hi]
          · simp [hi]
        rw [Finset.sum_congr rfl (fun i _ => hif i)]
        exact (Finset.sum_filter (s := (Finset.univ : Finset α))
          (p := fun i => i ∉ A) (f := fun i => μ i)).symm
      rw [h3]
      have h4 : (Finset.univ.filter (fun i => i ∉ A)) = Finset.univ \ A := by
        ext i; simp
      rw [h4]
      have := sum_add_sum_compl μ A
      linarith
    linarith
  have hacc1' : (∑ i, ν i * (if |est i - g1| ≤ ε * g1 then 1 else 0)) ≤ ∑ i ∈ A, ν i := by
    have hpt : ∀ i, (if |est i - g1| ≤ ε * g1 then (1:ℝ) else 0)
        ≤ (if t ≤ est i then (1:ℝ) else 0) := by
      intro i
      by_cases hs : |est i - g1| ≤ ε * g1
      · rw [if_pos hs]
        have hge : (1 - ε) * g1 ≤ est i := by
          have h1 : g1 - est i ≤ |g1 - est i| := le_abs_self _
          have h2 : |g1 - est i| = |est i - g1| := abs_sub_comm _ _
          linarith
        have hiA : t ≤ est i := by linarith
        rw [if_pos hiA]
      · rw [if_neg hs]
        by_cases ht : t ≤ est i
        · rw [if_pos ht]
          norm_num
        · rw [if_neg ht]
    have hsum : (∑ i, ν i * (if |est i - g1| ≤ ε * g1 then 1 else 0))
        ≤ ∑ i, ν i * (if t ≤ est i then (1:ℝ) else 0) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpt i) (hν i).le
    have h2 : (∑ i, ν i * (if t ≤ est i then (1:ℝ) else 0)) = ∑ i ∈ A, ν i := by
      have hA : ∀ i, (ν i * (if t ≤ est i then (1:ℝ) else 0))
          = (if i ∈ A then ν i else 0) := by
        intro i
        have hmem : i ∈ A ↔ t ≤ est i := by
          show i ∈ Finset.univ.filter (fun i => t ≤ est i) ↔ _
          simp
        by_cases ht : t ≤ est i
        · rw [if_pos ht, if_pos (hmem.2 ht), mul_one]
        · rw [if_neg ht, if_neg (fun h => ht (hmem.1 h)), mul_zero]
      rw [Finset.sum_congr rfl (fun i _ => hA i)]
      have h3 : (∑ i, (if i ∈ A then ν i else 0))
          = ∑ i ∈ Finset.univ.filter (fun i => i ∈ A), ν i :=
        (Finset.sum_filter (s := (Finset.univ : Finset α))
          (p := fun i => i ∈ A) (f := fun i => ν i)).symm
      rw [h3]
      have h4 : (Finset.univ.filter (fun i => i ∈ A)) = A := by
        ext i; simp
      rw [h4]
    linarith
  have herrsum : (∑ i ∈ A, μ i) + (∑ i ∈ Finset.univ \ A, ν i) ≤ 2 / 3 := by
    have hA : ∑ i ∈ A, μ i ≤ 1 / 3 := by
      have := hacc0'
      have := hacc0
      linarith
    have hAc : ∑ i ∈ Finset.univ \ A, ν i ≤ 1 / 3 := by
      have := hacc1'
      have := hacc1
      have h1 : ∑ i ∈ Finset.univ \ A, ν i = 1 - ∑ i ∈ A, ν i := by
        have := sum_add_sum_compl ν A; linarith
      linarith
    linarith
  have hfinal : (1 : ℝ) - tvDist μ ν ≤ 2 / 3 := le_trans herr herrsum
  have hcontra : (1 : ℝ) - 1 / 4 ≤ 2 / 3 := by
    have := hPinsker
    linarith
  norm_num at hcontra

lemma reservoirRowKL (d : ℕ) [NeZero d] (hd : 2 ≤ d) (u v : ℝ)
    (hu : 0 < u) (hu' : u < 1) (hv : 0 < v) (hv' : v < 1) :
    (∑ j : Fin d, (if j.val = 0 then u else (1-u) / ((d-1:ℕ):ℝ)) *
      log ((if j.val = 0 then u else (1-u) / ((d-1:ℕ):ℝ)) /
        (if j.val = 0 then v else (1-v) / ((d-1:ℕ):ℝ)))) = bernKL u v := by
  have hD := cast_d_sub_one_ne hd
  have hV : (1-v:ℝ) ≠ 0 := by linarith
  have hratio : ((1-u) / ((d-1:ℕ):ℝ)) / ((1-v) / ((d-1:ℕ):ℝ)) = (1-u)/(1-v) := by
    field_simp
  have hentry : ∀ j : Fin d,
      (if j.val = 0 then u else (1-u) / ((d-1:ℕ):ℝ)) *
      log ((if j.val = 0 then u else (1-u) / ((d-1:ℕ):ℝ)) /
        (if j.val = 0 then v else (1-v) / ((d-1:ℕ):ℝ))) =
      if j.val = 0 then u * log (u/v)
        else (1-u) / ((d-1:ℕ):ℝ) * log ((1-u)/(1-v)) := by
    intro j
    by_cases hj : j.val = 0 <;> simp [hj, hratio]
  simp_rw [hentry]
  rw [sum_split, Finset.sum_const, card_val_ne_zero, nsmul_eq_mul,
    bernKL_eq u v hu hu']
  field_simp

lemma bernKL_compl (u v : ℝ) (hu : 0 < u) (hu' : u < 1) (hv : 0 < v) (hv' : v < 1) :
    bernKL (1-u) (1-v) = bernKL u v := by
  rw [bernKL_eq _ _ (by linarith) (by linarith), bernKL_eq u v hu hu']
  simp only [sub_sub_cancel]
  ring

lemma hardP_rowKL (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p s t : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1/(d:ℝ)) (hs : 0 < s) (hs' : s < 1)
    (ht : 0 < t) (ht' : t < 1) (i : Fin d) :
    (∑ j, hardP d p s i j * log (hardP d p s i j / hardP d p t i j)) =
      if i.val = 0 then bernKL ((1-p)*s) ((1-p)*t) else bernKL (p*s) (p*t) := by
  have hp1 := one_sub_p_pos hd hp hp'
  have hsu : (1-p)*s < 1 := by nlinarith
  have htu : (1-p)*t < 1 := by nlinarith
  by_cases hi : i.val = 0
  · have heq : ∀ j, hardP d p s i j =
        if j.val = 0 then 1-(1-p)*s else (1-(1-(1-p)*s))/((d-1:ℕ):ℝ) := by
      intro j
      simp [hardP, NeZero.ne d, hi]
    have heq' : ∀ j, hardP d p t i j =
        if j.val = 0 then 1-(1-p)*t else (1-(1-(1-p)*t))/((d-1:ℕ):ℝ) := by
      intro j
      simp [hardP, NeZero.ne d, hi]
    simp_rw [heq, heq']
    rw [reservoirRowKL d hd _ _ (by linarith) (by nlinarith) (by linarith) (by nlinarith),
      bernKL_compl _ _ (mul_pos hp1 hs) hsu (mul_pos hp1 ht) htu, if_pos hi]
  · have heq : ∀ j, hardP d p s i j =
        if j.val = 0 then p*s else (1-p*s)/((d-1:ℕ):ℝ) := by
      intro j
      simp [hardP, NeZero.ne d, hi]
    have heq' : ∀ j, hardP d p t i j =
        if j.val = 0 then p*t else (1-p*t)/((d-1:ℕ):ℝ) := by
      intro j
      simp [hardP, NeZero.ne d, hi]
    simp_rw [heq, heq']
    rw [reservoirRowKL d hd _ _ (mul_pos hp hs) (ps_lt_one hd hp hp' hs hs')
      (mul_pos hp ht) (ps_lt_one hd hp hp' ht ht'), if_neg hi]

noncomputable def hardRareMass (d n : ℕ) (p s : ℝ) (x0 : Fin d) : ℝ :=
  ∑ Y : Fin (n+1) → Fin d, pathProb (hardP d p s) (fun i => if i=x0 then 1 else 0) Y *
    (if (Y (Fin.last n)).val = 0 then 1 else 0)

lemma hardRareMass_recur (d n : ℕ) [NeZero d] (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1/(d:ℝ)) (hs : 0 < s) (hs' : s < 1)
    (x0 : Fin d) :
    hardRareMass d (n+1) p s x0 = p*s + (1-s)*hardRareMass d n p s x0 := by
  let mu : Fin d → ℝ := fun i => if i=x0 then 1 else 0
  have htotal : (∑ Y : Fin (n+1) → Fin d, pathProb (hardP d p s) mu Y) = 1 := by
    rw [pathProb_sum _ _ (hardP_stoch hd p s hp hp' hs hs')]
    simp [mu]
  have hinner : ∀ Y : Fin (n+1) → Fin d,
      (∑ x : Fin d, pathProb (hardP d p s) mu (pathSnoc Y x) *
        (if (pathSnoc Y x (Fin.last (n+1))).val = 0 then 1 else 0)) =
      pathProb (hardP d p s) mu Y * hardP d p s (Y (Fin.last n)) ⟨0, Nat.pos_of_neZero d⟩ := by
    intro Y
    simp_rw [pathProb_snoc, pathSnoc_last]
    apply (Fintype.sum_eq_single (⟨0, Nat.pos_of_neZero d⟩ : Fin d) ?_).trans
    · simp
    · intro x hx
      have hval : x.val ≠ 0 := fun h => hx (Fin.ext h)
      simp [hval]
  have hentry : ∀ i : Fin d, hardP d p s i ⟨0, Nat.pos_of_neZero d⟩ =
      p*s + (1-s)*(if i.val = 0 then 1 else 0) := by
    intro i
    by_cases hi : i.val = 0 <;> simp [hardP, NeZero.ne d, hi] <;> ring
  change (∑ Y : Fin (n+2) → Fin d, pathProb (hardP d p s) mu Y *
    (if (Y (Fin.last (n+1))).val = 0 then 1 else 0)) = _
  rw [sum_path_snoc]
  simp_rw [hinner, hentry]
  calc
    (∑ Y : Fin (n+1) → Fin d, pathProb (hardP d p s) mu Y *
      (p*s+(1-s)*(if (Y (Fin.last n)).val = 0 then 1 else 0))) =
        p*s * (∑ Y : Fin (n+1) → Fin d, pathProb (hardP d p s) mu Y) +
        (1-s) * hardRareMass d n p s x0 := by
      unfold hardRareMass
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro Y _
      ring
    _ = _ := by rw [htotal, mul_one]

lemma hardRareMass_le (d n : ℕ) [NeZero d] (hd : 2 ≤ d) (p s : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1/(d:ℝ)) (hs : 0 < s) (hs' : s < 1)
    (x0 : Fin d) (hx0 : x0.val ≠ 0) : hardRareMass d n p s x0 ≤ p := by
  induction n with
  | zero =>
    unfold hardRareMass pathProb
    simp only [Fin.last_zero, Fintype.prod_empty, mul_one]
    have heq : ∀Y : Fin 1 → Fin d,
        (if Y 0=x0 then (1:ℝ) else 0)*(if (Y 0).val=0 then 1 else 0) = 0 := by
      intro Y
      by_cases hY : Y 0=x0 <;> simp [hY, hx0]
    simp_rw [heq]
    simpa using hp.le
  | succ n ih =>
    rw [hardRareMass_recur d n hd p s hp hp' hs hs' x0]
    have h := mul_le_mul_of_nonneg_left ih (show 0 ≤ 1-s by linarith)
    nlinarith

lemma hardP_rowKL_le (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p s t ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1/(d:ℝ)) (hs : 0 < s) (hs' : s < 1)
    (ht : 0 < t) (ht' : t < 1) (ht13 : t ≤ 1/3)
    (hrel : t = (1+8*ε)*s) (hε : 0 < ε) (i : Fin d) :
    (∑ j, hardP d p s i j * log (hardP d p s i j / hardP d p t i j)) ≤
      128*ε^2*s*(p + (if i.val=0 then 1 else 0)) := by
  have hp1 := one_sub_p_pos hd hp hp'
  have hpmax := p_lt_one hd hp hp'
  have hst : s < t := by nlinarith
  have hC : 0 ≤ 128*ε^2*s := by positivity
  rw [hardP_rowKL d hd p s t hp hp' hs hs' ht ht']
  by_cases hi : i.val=0
  · rw [if_pos hi, if_pos hi]
    calc
      bernKL ((1-p)*s) ((1-p)*t) ≤ 128*ε^2*((1-p)*s) := by
        apply bernKL_le _ _ ε (mul_pos hp1 hs) (mul_lt_mul_of_pos_left hst hp1)
          (by nlinarith) (by rw [hrel]; ring) hε
      _ ≤ _ := by nlinarith
  · rw [if_neg hi, if_neg hi, add_zero]
    calc
      bernKL (p*s) (p*t) ≤ 128*ε^2*(p*s) := by
        apply bernKL_le _ _ ε (mul_pos hp hs) (mul_lt_mul_of_pos_left hst hp)
          (by nlinarith) (by rw [hrel]; ring) hε
      _ = _ := by ring

lemma hardP_expectedKL_le (d n : ℕ) [NeZero d] (hd : 2 ≤ d) (p s t ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1/(d:ℝ)) (hs : 0 < s) (hs' : s < 1)
    (ht : 0 < t) (ht' : t < 1) (ht13 : t ≤ 1/3)
    (hrel : t = (1+8*ε)*s) (hε : 0 < ε) (x0 : Fin d) (hx0 : x0.val ≠ 0) :
    (∑ Y : Fin (n+1) → Fin d,
      pathProb (hardP d p s) (fun i => if i=x0 then 1 else 0) Y *
        ∑ j, hardP d p s (Y (Fin.last n)) j *
          log (hardP d p s (Y (Fin.last n)) j / hardP d p t (Y (Fin.last n)) j)) ≤
      256*p*s*ε^2 := by
  let mu : Fin d → ℝ := fun i => if i=x0 then 1 else 0
  have htotal : (∑ Y : Fin (n+1) → Fin d, pathProb (hardP d p s) mu Y) = 1 := by
    rw [pathProb_sum _ _ (hardP_stoch hd p s hp hp' hs hs')]
    simp [mu]
  have hq := hardRareMass_le d n hd p s hp hp' hs hs' x0 hx0
  have hnonneg : ∀ Y : Fin (n+1) → Fin d, 0 ≤ pathProb (hardP d p s) mu Y := by
    intro Y
    apply pathProb_nonneg _ _ (hardP_nonneg hd p s hp hp' hs hs')
    intro i
    dsimp [mu]
    split_ifs <;> norm_num
  have hC : 0 ≤ 128*ε^2*s := by positivity
  calc
    (∑ Y : Fin (n+1) → Fin d, pathProb (hardP d p s) mu Y *
        ∑ j, hardP d p s (Y (Fin.last n)) j *
          log (hardP d p s (Y (Fin.last n)) j / hardP d p t (Y (Fin.last n)) j)) ≤
      ∑ Y : Fin (n+1) → Fin d, pathProb (hardP d p s) mu Y *
        (128*ε^2*s*(p+(if (Y (Fin.last n)).val=0 then 1 else 0))) := by
      apply Finset.sum_le_sum
      intro Y _
      exact mul_le_mul_of_nonneg_left
        (hardP_rowKL_le d hd p s t ε hp hp' hs hs' ht ht' ht13 hrel hε _) (hnonneg Y)
    _ = 128*ε^2*s*(p+hardRareMass d n p s x0) := by
      calc
        _ = 128*ε^2*s*(p*(∑ Y : Fin (n+1) → Fin d, pathProb (hardP d p s) mu Y) +
            hardRareMass d n p s x0) := by
          unfold hardRareMass
          conv_rhs => rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro Y _
          ring
        _ = _ := by rw [htotal, mul_one]
    _ ≤ 128*ε^2*s*(p+p) := mul_le_mul_of_nonneg_left (add_le_add_left hq p) hC
    _ = 256*p*s*ε^2 := by ring

theorem hardPathKL_le (d n : ℕ) [NeZero d] (hd : 2 ≤ d) (p s t ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1/(d:ℝ)) (hs : 0 < s) (hs' : s < 1)
    (ht : 0 < t) (ht' : t < 1) (ht13 : t ≤ 1/3)
    (hrel : t = (1+8*ε)*s) (hε : 0 < ε) (x0 : Fin d) (hx0 : x0.val ≠ 0) :
    pathKL (n:=n) (hardP d p s) (hardP d p t)
      (fun i => if i=x0 then 1 else 0) (fun i => if i=x0 then 1 else 0) ≤
      256*(n:ℝ)*p*s*ε^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pathKL_succ _ _ _ (hardP_pos hd p s hp hp' hs hs')
      (hardP_pos hd p t hp hp' ht ht') (hardP_stoch hd p s hp hp' hs hs')]
    calc
      _ ≤ 256*(n:ℝ)*p*s*ε^2 + 256*p*s*ε^2 := add_le_add ih
        (hardP_expectedKL_le d n hd p s t ε hp hp' hs hs' ht ht' ht13 hrel hε x0 hx0)
      _ = _ := by push_cast; ring

/-- **Path KL of the hard pair** (paper (25)): from a reservoir start `X_0 = x₀` with
`x₀.val ≠ 0`, the path laws of `P_{s0}` and `P_{s1}` satisfy
`klDist ≤ 256 n p g ε²`.

Chain-rule identity (row-wise KL = Bernoulli KL of the exchange rates) plus (24):
each step contributes at most `256 p s0 ε²`, and `s0 ≤ g`.  The identity
`klDist (path laws) = ∑_t E[KL(P_{s0}(X_t,·) ‖ P_{s1}(X_t,·))]` is the chain rule
for relative entropy on the path space (same start ⇒ zero initial KL). -/
theorem pathKL_hardPair_le (d n : ℕ) [NeZero d] (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / (d : ℝ)) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2)
    (x0 : Fin d) (hx0 : x0.val ≠ 0)
    (mu0 : Fin d → ℝ) (hmu0 : mu0 = fun i => if i = x0 then 1 else 0) :
    let s0 := 1 - sqrt (1 - g)
    let s1 := (1 + 8 * ε) * s0
    klDist (fun X : Fin (n + 1) → Fin d => pathProb (hardP d p s0) mu0 X)
        (fun X : Fin (n + 1) → Fin d => pathProb (hardP d p s1) mu0 X)
      ≤ 256 * (n : ℝ) * p * g * ε ^ 2 := by
  intro s0 s1
  have hrate := hardP_rates g ε hg hg' hε hε'
  have hs0 : 0 < s0 := hrate.1
  have hs0' : s0 < 1 := hrate.2.1
  have hs1 : 0 < s1 := hrate.2.2.1
  have hs1' : s1 < 1 := hrate.2.2.2
  have hgap : s0*(2-s0) = g := by
    dsimp [s0]
    nlinarith [Real.sq_sqrt (show 0 ≤ 1-g by linarith)]
  have hsg : s0 ≤ g := by nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hs0'.le)]
  have hs015 : s0 ≤ 1/15 := by
    have hm : 0 ≤ s0*((1/8:ℝ)-s0) :=
      mul_nonneg hs0.le (by linarith)
    nlinarith
  have hs113 : s1 ≤ 1/3 := by
    dsimp [s1]
    nlinarith
  rw [hmu0]
  change pathKL (n:=n) (hardP d p s0) (hardP d p s1)
    (fun i => if i=x0 then 1 else 0) (fun i => if i=x0 then 1 else 0) ≤ _
  calc
    _ ≤ 256*(n:ℝ)*p*s0*ε^2 :=
      hardPathKL_le d n hd p s0 s1 ε hp hp' hs0 hs0' hs1 hs1' hs113 rfl hε x0 hx0
    _ ≤ 256*(n:ℝ)*p*g*ε^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg ε)
      exact mul_le_mul_of_nonneg_left hsg (by positivity)

/-- Hard-pair interface: two models in `C(d,p,g)` with gaps `g0 = g`, `g1 ∈ [g,5g]`,
disjoint success intervals `(1+ε)g0 < (1-ε)g1`, and path KL ≤ `256 n p g ε²` from the
reservoir start. -/
theorem hardPair_interface_with_structure (d n : ℕ) [NeZero d] (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ (S0 S1 : Stoch d) (st0 : Stationary S0) (st1 : Stationary S1)
      (g0 g1 : ℝ) (x0 : Fin d)
      (mu0 : Fin d → ℝ),
      p ≤ Stationary.star st0 ∧ p ≤ Stationary.star st1
      ∧ g ≤ gammaPS S0 st0 ∧ g ≤ gammaPS S1 st1
      ∧ g0 = gammaPS S0 st0 ∧ g1 = gammaPS S1 st1
      ∧ (1 + ε) * g0 < (1 - ε) * g1
      ∧ mu0 = (fun i => if i = x0 then 1 else 0)
      ∧ klDist (fun X : Fin (n + 1) → Fin d => pathProb S0.P mu0 X)
          (fun X : Fin (n + 1) → Fin d => pathProb S1.P mu0 X)
          ≤ 256 * n * p * g * ε ^ 2
      ∧ (∀ i j : Fin d, 0 < S1.P i j)
      ∧ (∀ i j : Fin d, 0 < S0.P i j)
      ∧ (∀ i j, st0.mu i * S0.P i j = st0.mu j * S0.P j i)
      ∧ (∀ i j, st1.mu i * S1.P i j = st1.mu j * S1.P j i)
      ∧ st0.mu = hardMu d p ∧ st1.mu = hardMu d p := by
  classical
  set s0 : ℝ := 1 - sqrt (1 - g)
  set s1 : ℝ := (1 + 8 * ε) * s0
  have hrate := hardP_rates g ε hg hg' hε hε'
  have hs0_pos : 0 < s0 := by
    show 0 < 1 - sqrt (1 - g)
    exact hrate.1
  have hs0_lt : s0 < 1 := by
    show 1 - sqrt (1 - g) < 1
    exact hrate.2.1
  have hs1_pos : 0 < s1 := by
    show 0 < (1 + 8 * ε) * (1 - sqrt (1 - g))
    exact hrate.2.2.1
  have hs1_lt : s1 < 1 := by
    show (1 + 8 * ε) * (1 - sqrt (1 - g)) < 1
    exact hrate.2.2.2
  let S0 : Stoch d := hardP_isStoch hd p s0 hp hp' hs0_pos hs0_lt
  let S1 : Stoch d := hardP_isStoch hd p s1 hp hp' hs1_pos hs1_lt
  let st0 : Stationary S0 := hardSt hd p s0 hp hp' hs0_pos hs0_lt
  let st1 : Stationary S1 := hardSt hd p s1 hp hp' hs1_pos hs1_lt
  have hx0val : (1 : ℕ) ≠ 0 := by decide
  let x0 : Fin d := ⟨1, by omega⟩
  let mu0 : Fin d → ℝ := fun i => if i = x0 then 1 else 0
  -- gaps
  have hgap0 : gammaPS S0 st0 = s0 * (2 - s0) := by
    show gammaPS _ _ = _
    exact hardP_gamma hd p s0 hp hp' hs0_pos hs0_lt
  have hgap1 : gammaPS S1 st1 = s1 * (2 - s1) := by
    show gammaPS _ _ = _
    exact hardP_gamma hd p s1 hp hp' hs1_pos hs1_lt
  have hdisj0 := hardPair_disjoint g ε hg hg' hε hε'
  have hg0eq : s0 * (2 - s0) = g := hdisj0.1
  have hg1ge : g ≤ s1 * (2 - s1) := hdisj0.2.1
  have hdisj : (1 + ε) * (s0 * (2 - s0)) < (1 - ε) * (s1 * (2 - s1)) := hdisj0.2.2.2
  set g0 : ℝ := s0 * (2 - s0)
  set g1 : ℝ := s1 * (2 - s1)
  -- star
  have hstar0 : p ≤ Stationary.star st0 := by
    rw [hard_star d hd p s0 hp hp' hs0_pos hs0_lt]
  have hstar1 : p ≤ Stationary.star st1 := by
    rw [hard_star d hd p s1 hp hp' hs1_pos hs1_lt]
  -- path KL (chain rule; see `pathKL_hardPair_le`)
  have hKL : klDist (fun X : Fin (n + 1) → Fin d => pathProb S0.P mu0 X)
      (fun X : Fin (n + 1) → Fin d => pathProb S1.P mu0 X)
      ≤ 256 * (n : ℝ) * p * g * ε ^ 2 := by
    have h := pathKL_hardPair_le d n hd p g ε hp hp' hg hg' hε hε' x0 (by
      show (1:ℕ) ≠ 0; exact hx0val) mu0 rfl
    simpa [S0, S1, mu0, s0, s1] using h
  have hS1pos : ∀ i j : Fin d, 0 < S1.P i j := by
    intro i j
    exact hardP_pos hd p s1 hp hp' hs1_pos hs1_lt i j
  refine ⟨S0, S1, st0, st1, g0, g1, x0, mu0, ?_⟩
  refine ⟨hstar0, hstar1, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · rw [hgap0]; linarith
  · rw [hgap1]; linarith
  · rw [hgap0]
  · rw [hgap1]
  · simpa [g0, g1] using hdisj
  · have hcast : (256 * n * p * g * ε ^ 2 : ℝ) = 256 * (n : ℝ) * p * g * ε ^ 2 := by
      norm_cast
    rw [hcast]
    exact hKL
  · refine ⟨hS1pos, ?_, ?_, ?_, rfl, rfl⟩
    · exact hardP_pos hd p s0 hp hp' hs0_pos hs0_lt
    · exact (hardP_reversible hd p s0 hp hp' hs0_pos hs0_lt).1
    · exact (hardP_reversible hd p s1 hp hp' hs1_pos hs1_lt).1

theorem hardPair_interface (d n : ℕ) [NeZero d] (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ (S0 S1 : Stoch d) (st0 : Stationary S0) (st1 : Stationary S1)
      (g0 g1 : ℝ) (x0 : Fin d)
      (mu0 : Fin d → ℝ),
      p ≤ Stationary.star st0 ∧ p ≤ Stationary.star st1
      ∧ g ≤ gammaPS S0 st0 ∧ g ≤ gammaPS S1 st1
      ∧ g0 = gammaPS S0 st0 ∧ g1 = gammaPS S1 st1
      ∧ (1 + ε) * g0 < (1 - ε) * g1
      ∧ mu0 = (fun i => if i = x0 then 1 else 0)
      ∧ klDist (fun X : Fin (n + 1) → Fin d => pathProb S0.P mu0 X)
          (fun X : Fin (n + 1) → Fin d => pathProb S1.P mu0 X)
          ≤ 256 * n * p * g * ε ^ 2
      ∧ (∀ i j : Fin d, 0 < S1.P i j) := by
  obtain ⟨S0, S1, st0, st1, g0, g1, x0, mu0,
    hπ0, hπ1, hg0, hg1, heq0, heq1, hdisj, hmu, hKL, hpos, _⟩ :=
    hardPair_interface_with_structure d n hd p g ε hp hp' hg hg' hε hε'
  exact ⟨S0, S1, st0, st1, g0, g1, x0, mu0,
    hπ0, hπ1, hg0, hg1, heq0, heq1, hdisj, hmu, hKL, hpos⟩

/-- A finite sum may be restricted to the common deterministic-start support. -/
lemma sum_startSupport (x0 : Fin d) (f : (Fin (n + 1) → Fin d) → ℝ)
    (hf : ∀ X, X 0 ≠ x0 → f X = 0) :
    (∑ X : {X : Fin (n + 1) → Fin d // X 0 = x0}, f X.val) = ∑ X, f X := by
  classical
  have hsub := Finset.sum_subtype (F := inferInstance) (p := fun X : Fin (n + 1) → Fin d => X 0 = x0)
    (Finset.univ.filter (fun X => X 0 = x0)) (fun X => by simp) f
  rw [← hsub]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro X _ hX
  exact hf X (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hX)

lemma pathProb_eq_zero_of_start_ne (P : Matrix (Fin d) (Fin d) ℝ)
    (x0 : Fin d) (X : Fin (n + 1) → Fin d) (hX : X 0 ≠ x0) :
    pathProb P (fun i => if i = x0 then 1 else 0) X = 0 := by
  simp [pathProb, hX]

lemma pathMeasure_eq_indicator (P : Matrix (Fin d) (Fin d) ℝ)
    (mu : Fin d → ℝ) (E : (Fin (n + 1) → Fin d) → Prop) [DecidablePred E] :
    pathMeasure P mu (Finset.univ.filter E) =
      ∑ X, pathProb P mu X * (if E X then 1 else 0) := by
  classical
  simp only [pathMeasure, Finset.sum_filter, mul_ite, mul_one, mul_zero]

/-- The lower bound already holds on strictly positive reversible chains whose
stationary law is the single known vector `hardMu d p`.  Any estimator using
that known law is a function of the path once this common vector is fixed. -/
theorem minimax_lower_reversible_known_stationary (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2)
    (n : ℕ) (est : (Fin (n + 1) → Fin d) → ℝ)
    (hacc : ∀ (S : Stoch d) (st : Stationary S),
      (∀ i j, 0 < S.P i j) →
      (∀ i j, st.mu i * S.P i j = st.mu j * S.P j i) →
      st.mu = hardMu d p → p ≤ Stationary.star st → g ≤ gammaPS S st →
      ∀ x0 : Fin d,
        2/3 ≤ pathMeasure S.P (fun i => if i=x0 then 1 else 0)
          {X | |est X - gammaPS S st| ≤ ε * gammaPS S st}) :
    (1 / 2048 : ℝ) / (p * g * ε ^ 2) ≤ n := by
  by_contra h
  push_neg at h
  have hn : (n : ℝ) ≤ 1 / (2048 * p * g * ε ^ 2) := by
    have hpos : 0 < p * g * ε ^ 2 :=
      mul_pos (mul_pos hp hg) (sq_pos_of_ne_zero (ne_of_gt hε))
    have : (1 / 2048 : ℝ) / (p * g * ε ^ 2) = 1 / (2048 * p * g * ε ^ 2) := by
      field_simp [ne_of_gt hpos]
    have h' : (n : ℝ) < 1 / (2048 * p * g * ε ^ 2) := by
      rw [← this]; exact h
    exact le_of_lt h'
  have hklbound := pathKL_le_one_eighth d n hd p g ε hp hp' hg hg' hε hε' hn
  obtain ⟨S0, S1, st0, st1, g0, g1, x0, mu0,
      hst0, hst1, hg0, hg1, hg0', hg1', hdisj, hmu0, hKL, hS1pos,
      hS0pos, hrev0, hrev1, hlaw0, hlaw1⟩ :=
    hardPair_interface_with_structure d n hd p g ε hp hp' hg hg' hε hε'
  have hmu0' : mu0 = (fun i => if i = x0 then 1 else 0) := hmu0
  have hacc0 : 2 / 3 ≤ pathMeasure S0.P mu0
      {X | |est X - gammaPS S0 st0| ≤ ε * gammaPS S0 st0} := by
    have h := hacc S0 st0 hS0pos hrev0 hlaw0 hst0 hg0 x0
    -- h : 2/3 ≤ pathMeasure S0.P (fun i => if i = x0 then 1 else 0) {X | ...}
    rw [hmu0']
    exact h
  have hacc1 : 2 / 3 ≤ pathMeasure S1.P mu0
      {X | |est X - gammaPS S1 st1| ≤ ε * gammaPS S1 st1} := by
    have h := hacc S1 st1 hS1pos hrev1 hlaw1 hst1 hg1 x0
    rw [hmu0']
    exact h
  -- Two-point testing on the path laws, restricted to {X // X 0 = x0}.
  have h2pt : False := by
    classical
    let α := {X : Fin (n + 1) → Fin d // X 0 = x0}
    let μp : α → ℝ := fun X => pathProb S0.P mu0 X.val
    let νp : α → ℝ := fun X => pathProb S1.P mu0 X.val
    have hmu0eq : mu0 = (fun i => if i = x0 then 1 else 0) := hmu0
    have hmu_nonneg : ∀ j : Fin d, 0 ≤ mu0 j := by
      intro j
      rw [hmu0eq]
      by_cases hj : j = x0 <;> simp [hj]
    have hμn : ∀ i : α, 0 ≤ μp i := by
      intro i
      exact pathProb_nonneg S0.P mu0 S0.nonneg hmu_nonneg i.val
    have hνn : ∀ i : α, 0 < νp i := by
      intro i
      have hX : i.val 0 = x0 := i.property
      have hmu : 0 < mu0 (i.val 0) := by
        rw [hX, hmu0eq]
        simp
      exact pathProb_pos S1.P mu0 hS1pos i.val hmu
    -- sums to 1: off-support paths have mass 0
    have hμs : ∑ i : α, μp i = 1 := by
      have hfull : (∑ X : Fin (n + 1) → Fin d, pathProb S0.P mu0 X) = ∑ i, mu0 i :=
        pathProb_sum (n := n) S0.P mu0 S0.row_stoch
      rw [show (∑ i, mu0 i) = (1:ℝ) by
        rw [hmu0eq]
        show (∑ i, (fun i => if i = x0 then 1 else 0) i) = 1
        simp] at hfull
      calc
        (∑ i : α, μp i) = ∑ X : Fin (n + 1) → Fin d, pathProb S0.P mu0 X := by
          apply sum_startSupport x0 (fun X => pathProb S0.P mu0 X)
          intro X hX
          rw [hmu0eq]
          exact pathProb_eq_zero_of_start_ne S0.P x0 X hX
        _ = 1 := hfull
    have hνs : ∑ i : α, νp i = 1 := by
      have hfull : (∑ X : Fin (n + 1) → Fin d, pathProb S1.P mu0 X) = ∑ i, mu0 i :=
        pathProb_sum (n := n) S1.P mu0 S1.row_stoch
      rw [show (∑ i, mu0 i) = (1:ℝ) by
        rw [hmu0eq]
        show (∑ i, (fun i => if i = x0 then 1 else 0) i) = 1
        simp] at hfull
      calc
        (∑ i : α, νp i) = ∑ X : Fin (n + 1) → Fin d, pathProb S1.P mu0 X := by
          apply sum_startSupport x0 (fun X => pathProb S1.P mu0 X)
          intro X hX
          rw [hmu0eq]
          exact pathProb_eq_zero_of_start_ne S1.P x0 X hX
        _ = 1 := hfull
    have hKLsub : klDist μp νp ≤ 1 / 8 := by
      -- subtype klDist = full path klDist; ≤ 256 n p g ε² ≤ 1/8
      have hle := le_trans hKL hklbound
      have heq : klDist μp νp =
          klDist (fun X : Fin (n + 1) → Fin d => pathProb S0.P mu0 X)
            (fun X : Fin (n + 1) → Fin d => pathProb S1.P mu0 X) := by
        unfold klDist
        apply sum_startSupport x0 (fun X => if pathProb S0.P mu0 X = 0 then 0 else
          pathProb S0.P mu0 X * log (pathProb S0.P mu0 X / pathProb S1.P mu0 X))
        intro X hX
        have hz : pathProb S0.P mu0 X = 0 := by
          rw [hmu0eq]
          exact pathProb_eq_zero_of_start_ne S0.P x0 X hX
        rw [hz, if_pos rfl]
      rw [heq]
      exact hle
    have hac0 : (2 / 3 : ℝ) ≤ ∑ i : α, μp i *
        (if |est i.val - g0| ≤ ε * g0 then 1 else 0) := by
      -- = pathMeasure of the success event
      have h := hacc0
      rw [← hg0', pathMeasure_eq_indicator] at h
      rw [sum_startSupport x0 (fun X => pathProb S0.P mu0 X *
        (if |est X - g0| ≤ ε * g0 then 1 else 0)) (by
          intro X hX
          have hz : pathProb S0.P mu0 X = 0 := by
            rw [hmu0eq]
            exact pathProb_eq_zero_of_start_ne S0.P x0 X hX
          simp only [hz, zero_mul])]
      exact h
    have hac1 : (2 / 3 : ℝ) ≤ ∑ i : α, νp i *
        (if |est i.val - g1| ≤ ε * g1 then 1 else 0) := by
      have h := hacc1
      rw [← hg1', pathMeasure_eq_indicator] at h
      rw [sum_startSupport x0 (fun X => pathProb S1.P mu0 X *
        (if |est X - g1| ≤ ε * g1 then 1 else 0)) (by
          intro X hX
          have hz : pathProb S1.P mu0 X = 0 := by
            rw [hmu0eq]
            exact pathProb_eq_zero_of_start_ne S1.P x0 X hX
          simp only [hz, zero_mul])]
      exact h
    exact two_point_no_accurate μp νp hμn hνn hμs hνs hKLsub
      (fun i => est i.val) g0 g1 ε hdisj hac0 hac1
  exact h2pt

theorem minimax_lower (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2)
    (n : ℕ) (est : (Fin (n + 1) → Fin d) → ℝ)
    (hacc : relativelyAccurate n d est p g ε) :
    (1 / 2048 : ℝ) / (p * g * ε ^ 2) ≤ n := by
  apply minimax_lower_reversible_known_stationary d hd p g ε hp hp' hg hg' hε hε' n est
  intro S st _hpos _hrev _hlaw hπ hgap x0
  exact hacc S st hπ hgap x0

/-- Corollary in terms of `nStar`: whenever a relatively accurate estimator exists
at some sample size, `nStar` is at least `(1/2048)/(p g ε²)`. -/
theorem nStar_le_of_ne (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hexists : ∃ n est, relativelyAccurate n d est p g ε) :
    (1 / 2048 : ℝ) / (p * g * ε ^ 2) ≤ nStar d p g ε := by
  obtain ⟨n, est, hacc⟩ := hexists
  set S : Set ℕ := {n : ℕ | ∃ est, relativelyAccurate n d est p g ε}
  have hmin : ∀ m ∈ S, (1 / 2048 : ℝ) / (p * g * ε ^ 2) ≤ (m : ℝ) := by
    intro m hm
    obtain ⟨est, hacc⟩ := hm
    exact minimax_lower d hd p g ε hp hp' hg hg' hε hε' m est hacc
  have hne : S.Nonempty := ⟨n, est, hacc⟩
  have hns : nStar d p g ε = sInf S := rfl
  have hmem : nStar d p g ε ∈ S := by
    rw [hns]
    exact Nat.sInf_mem hne
  exact hmin _ hmem

end PsgEst
