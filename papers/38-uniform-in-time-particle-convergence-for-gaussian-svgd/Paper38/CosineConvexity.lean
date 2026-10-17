import Paper38.CosineExample
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.GCongr

noncomputable section

open Real Set

namespace Paper38.Cosine

/-- The entries of the actual Hessian calculated in (9.6). -/
def hessianA (ε μ s : ℝ) : ℝ := meanCurvature ε μ s

def hessianB (ε μ s : ℝ) : ℝ := ε * attenuation s * Real.sin μ / 2

def hessianC (ε μ s : ℝ) : ℝ :=
  1 / (2 * s ^ 2) + ε * attenuation s * Real.cos μ / 4

lemma hessianA_pos {ε s : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1) (hs : 0 ≤ s) (μ : ℝ) :
    0 < hessianA ε μ s := by
  have := meanCurvature_lower hε hs μ
  unfold hessianA
  linarith

lemma attenuation_sq (s : ℝ) : attenuation s ^ 2 = Real.exp (-s) := by
  unfold attenuation
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- The first Schur-complement estimate in (9.7). -/
lemma schur_lower_first {ε s : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1) (hs : 0 < s) (μ : ℝ) :
    1 / (2 * s ^ 2) - ε * attenuation s / 4 -
        ε ^ 2 * Real.exp (-s) / (4 * (1 - ε)) ≤
      hessianC ε μ s - hessianB ε μ s ^ 2 / hessianA ε μ s := by
  have hA := hessianA_pos hε hε' hs.le μ
  have hA' : 1 - ε ≤ hessianA ε μ s := meanCurvature_lower hε hs.le μ
  have hden : 0 < 1 - ε := by linarith
  have he : 0 ≤ ε * attenuation s := mul_nonneg hε (attenuation_pos s).le
  have hcos := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos μ) he
  have hC : 1 / (2 * s ^ 2) - ε * attenuation s / 4 ≤ hessianC ε μ s := by
    unfold hessianC
    linarith
  have hB : hessianB ε μ s ^ 2 ≤ ε ^ 2 * Real.exp (-s) / 4 := by
    have hsin := mul_le_mul_of_nonneg_left (Real.sin_sq_le_one μ)
      (sq_nonneg (ε * attenuation s))
    unfold hessianB
    rw [← attenuation_sq]
    nlinarith
  have hdiv : hessianB ε μ s ^ 2 / hessianA ε μ s ≤
      (ε ^ 2 * Real.exp (-s) / 4) / (1 - ε) := by
    exact div_le_div₀ (by positivity) hB hden hA'
  have hrewrite : (ε ^ 2 * Real.exp (-s) / 4) / (1 - ε) =
      ε ^ 2 * Real.exp (-s) / (4 * (1 - ε)) := by rw [div_div]
  rw [hrewrite] at hdiv
  linarith

/-- The second Schur-complement estimate in (9.7), including its constants. -/
lemma schur_lower_second {ε s : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1) (hs : 0 < s) :
    (1 / (2 * s ^ 2)) *
        (1 - 8 * Real.exp (-2) * ε - 2 * Real.exp (-2) * ε ^ 2 / (1 - ε)) ≤
      1 / (2 * s ^ 2) - ε * attenuation s / 4 -
        ε ^ 2 * Real.exp (-s) / (4 * (1 - ε)) := by
  have hb := source_exponential_bounds hs.le
  have hden : 0 < 1 - ε := by linarith
  have h₁ := mul_le_mul_of_nonneg_left hb.1 hε
  have h₂ := mul_le_mul_of_nonneg_left hb.2 (sq_nonneg ε)
  have h₃ := mul_le_mul_of_nonneg_left h₁ hden.le
  unfold attenuation
  simp only [neg_div] at h₁ h₃
  apply (mul_le_mul_right (show 0 < 8 * s ^ 2 * (1 - ε) by positivity)).mp
  field_simp [hs.ne', hden.ne']
  nlinarith

lemma source_schur_factor_positive {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 10) :
    0 < 1 - 8 * Real.exp (-2) * ε - 2 * Real.exp (-2) * ε ^ 2 / (1 - ε) := by
  have hden : 0 < 1 - ε := by linarith
  have he : 0 ≤ Real.exp (-2) := (Real.exp_pos _).le
  have he' : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have h₁ := mul_le_mul_of_nonneg_right he' hε
  have h₂ := mul_le_mul_of_nonneg_right he' (sq_nonneg ε)
  have hsq : ε ^ 2 ≤ 1 / 100 := by nlinarith
  apply (mul_lt_mul_right hden).mp
  field_simp [hden.ne']
  nlinarith

lemma schur_positive {ε s : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 10) (hs : 0 < s) (μ : ℝ) :
    0 < hessianC ε μ s - hessianB ε μ s ^ 2 / hessianA ε μ s := by
  have hε1 : ε < 1 := by linarith
  have h₁ := schur_lower_first hε hε1 hs μ
  have h₂ := schur_lower_second hε hε1 hs
  have h₃ : 0 < (1 / (2 * s ^ 2)) *
      (1 - 8 * Real.exp (-2) * ε - 2 * Real.exp (-2) * ε ^ 2 / (1 - ε)) :=
    mul_pos (by positivity) (source_schur_factor_positive hε hε')
  linarith

/-- Strict positivity of the Hessian quadratic form throughout the entire
positive-variance domain. -/
lemma energy_hessian_positive_definite {ε s : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 10)
    (hs : 0 < s) (μ u v : ℝ) (huv : (u, v) ≠ (0, 0)) :
    0 < hessianA ε μ s * u ^ 2 + 2 * hessianB ε μ s * u * v + hessianC ε μ s * v ^ 2 := by
  have hA := hessianA_pos hε (by linarith) hs.le μ
  have hS := schur_positive hε hε' hs μ
  have hid : hessianA ε μ s * u ^ 2 + 2 * hessianB ε μ s * u * v + hessianC ε μ s * v ^ 2 =
      hessianA ε μ s * (u + hessianB ε μ s / hessianA ε μ s * v) ^ 2 +
        (hessianC ε μ s - hessianB ε μ s ^ 2 / hessianA ε μ s) * v ^ 2 := by
    field_simp
    ring
  rw [hid]
  by_cases hv : v = 0
  · have hu : u ≠ 0 := by intro hu; exact huv (by simp [hu, hv])
    simp only [hv, mul_zero, add_zero]
    have hz : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [hz, mul_zero, add_zero]
    exact mul_pos hA (sq_pos_of_ne_zero hu)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hA.le (sq_nonneg _))
      (mul_pos hS (sq_pos_of_ne_zero hv))

/-- Restriction of the energy to an affine line, with variance as the second coordinate. -/
def lineEnergy (ε μ s u v t : ℝ) : ℝ := energy ε (μ + t * u) (s + t * v)

def lineEnergyDeriv (ε μ s u v t : ℝ) : ℝ :=
  meanForce ε (μ + t * u) (s + t * v) * u +
    varianceGradient ε (μ + t * u) (s + t * v) * v

lemma hasDerivAt_lineEnergy (ε μ s u v t : ℝ) (hs : s + t * v ≠ 0) :
    HasDerivAt (lineEnergy ε μ s u v) (lineEnergyDeriv ε μ s u v t) t := by
  have hm : HasDerivAt (fun z : ℝ => μ + z * u) u t := by
    convert ((hasDerivAt_id t).mul_const u).const_add μ using 1 <;> simp
  have hv : HasDerivAt (fun z : ℝ => s + z * v) v t := by
    convert ((hasDerivAt_id t).mul_const v).const_add s using 1 <;> simp
  convert (((hm.pow 2).add hv).sub (hv.log hs)).div_const 2 |>.add
    (((hv.neg.div_const 2).exp.const_mul ε).mul hm.cos) using 1 <;>
    simp [lineEnergy, lineEnergyDeriv, meanForce, varianceGradient, attenuation] <;>
    field_simp [hs] <;> ring

lemma hasDerivAt_lineEnergyDeriv (ε μ s u v t : ℝ) (hs : s + t * v ≠ 0) :
    HasDerivAt (lineEnergyDeriv ε μ s u v)
      (hessianA ε (μ + t * u) (s + t * v) * u ^ 2 +
        2 * hessianB ε (μ + t * u) (s + t * v) * u * v +
        hessianC ε (μ + t * u) (s + t * v) * v ^ 2) t := by
  have hm : HasDerivAt (fun z : ℝ => μ + z * u) u t := by
    convert ((hasDerivAt_id t).mul_const u).const_add μ using 1 <;> simp
  have hv : HasDerivAt (fun z : ℝ => s + z * v) v t := by
    convert ((hasDerivAt_id t).mul_const v).const_add s using 1 <;> simp
  have ha := (hv.neg.div_const 2).exp
  convert ((hm.sub ((ha.const_mul ε).mul hm.sin)).mul_const u).add
    ((((hasDerivAt_const t 1).sub (hv.inv hs)).sub
      ((ha.const_mul ε).mul hm.cos)).div_const 2 |>.mul_const v) using 1
  · funext z
    simp [lineEnergyDeriv, meanForce, varianceGradient, attenuation, one_div] <;> ring
  · simp [hessianA, meanCurvature, hessianB, hessianC, attenuation, one_div]
    field_simp [hs]
    ring

lemma positive_variance_segment {s r t : ℝ} (hs : 0 < s) (hr : 0 < r)
    (ht : t ∈ Icc 0 1) : 0 < s + t * (r - s) := by
  by_cases ht1 : t = 1
  · simpa [ht1] using hr
  · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
    have ht' : 0 < 1 - t := by linarith
    have h₁ := mul_pos ht' hs
    have h₂ := mul_nonneg ht.1 hr.le
    nlinarith

lemma lineEnergy_strictConvexOn {ε s r : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 10)
    (hs : 0 < s) (hr : 0 < r) (μ ν : ℝ) (hneq : (μ, s) ≠ (ν, r)) :
    StrictConvexOn ℝ (Icc 0 1) (lineEnergy ε μ s (ν - μ) (r - s)) := by
  have hdir : (ν - μ, r - s) ≠ (0, 0) := by
    intro heq
    have hm := congrArg Prod.fst heq
    have hv := congrArg Prod.snd heq
    apply hneq
    apply Prod.ext <;> dsimp at * <;> linarith
  have hpos (t : ℝ) (ht : t ∈ Icc 0 1) : 0 < s + t * (r - s) :=
    positive_variance_segment hs hr ht
  have hmono : StrictMonoOn (lineEnergyDeriv ε μ s (ν - μ) (r - s)) (Ioo 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
    · intro t ht
      exact (hasDerivAt_lineEnergyDeriv ε μ s (ν - μ) (r - s) t
        (hpos t ⟨ht.1.le, ht.2.le⟩).ne').continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      rw [(hasDerivAt_lineEnergyDeriv ε μ s (ν - μ) (r - s) t
        (hpos t ⟨ht.1.le, ht.2.le⟩).ne').deriv]
      exact energy_hessian_positive_definite hε hε' (hpos t ⟨ht.1.le, ht.2.le⟩)
        (μ + t * (ν - μ)) (ν - μ) (r - s) hdir
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc 0 1)
  · intro t ht
    exact (hasDerivAt_lineEnergy ε μ s (ν - μ) (r - s) t (hpos t ht).ne').continuousAt.continuousWithinAt
  · rw [interior_Icc]
    intro t ht z hz htz
    rw [(hasDerivAt_lineEnergy ε μ s (ν - μ) (r - s) t
        (hpos t ⟨ht.1.le, ht.2.le⟩).ne').deriv,
      (hasDerivAt_lineEnergy ε μ s (ν - μ) (r - s) z
        (hpos z ⟨hz.1.le, hz.2.le⟩).ne').deriv]
    exact hmono ht hz htz

/-- The strict convexity claimed after (9.7), on its exact source domain. -/
lemma energy_strictConvexOn {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 10) :
    StrictConvexOn ℝ {q : ℝ × ℝ | 0 < q.2} (fun q => energy ε q.1 q.2) := by
  have hc : Convex ℝ {q : ℝ × ℝ | 0 < q.2} := by
    intro x hx y hy a b ha hb hab
    change 0 < a * x.2 + b * y.2
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hy
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hx)
        (mul_nonneg hb hy.le)
  refine ⟨hc, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hline := lineEnergy_strictConvexOn hε hε' hx hy x.1 y.1 (by simpa using hxy)
  have hj := hline.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) (by norm_num : (0 : ℝ) ≠ 1) ha hb hab
  have ha1 : a = 1 - b := by linarith
  have hμ : x.1 + b * (y.1 - x.1) = a * x.1 + b * y.1 := by rw [ha1]; ring
  have hs : x.2 + b * (y.2 - x.2) = a * x.2 + b * y.2 := by rw [ha1]; ring
  have hμ1 : x.1 + (y.1 - x.1) = y.1 := by ring
  have hs1 : x.2 + (y.2 - x.2) = y.2 := by ring
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, lineEnergy, zero_mul, add_zero,
    one_mul, hμ1, hs1, hμ, hs, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] using hj

/-- A direct certificate that the source potential is genuinely nonquadratic. -/
lemma potential_second_derivative_nonconstant {ε : ℝ} (hε : 0 < ε) :
    deriv (deriv (potential ε)) 0 ≠ deriv (deriv (potential ε)) Real.pi := by
  simp only [second_deriv_potential, curvature, Real.cos_zero, Real.cos_pi, mul_one, mul_neg_one]
  linarith

end Paper38.Cosine
