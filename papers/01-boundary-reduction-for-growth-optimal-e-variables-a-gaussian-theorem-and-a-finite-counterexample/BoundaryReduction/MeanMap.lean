import BoundaryReduction.Separator
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Real Set BigOperators
open scoped Classical
namespace BoundaryReduction.NinePoint

lemma hasDerivAt_un_ray (θ : ℝ × ℝ) (y : Fin 9) (t : ℝ) :
    HasDerivAt (fun s : ℝ => un (s • θ) y)
      (un (t • θ) y * dot θ (coord y)) t := by
  simp only [un_smul]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (((hasDerivAt_id t).mul_const (dot θ (coord y))).exp.mul_const (p0 y))

noncomputable def rayNumerator (θ : ℝ × ℝ) (t : ℝ) : ℝ :=
  ∑ y, un (t • θ) y * dot θ (coord y)
noncomputable def raySecond (θ : ℝ × ℝ) (t : ℝ) : ℝ :=
  ∑ y, un (t • θ) y * (dot θ (coord y)) ^ 2
noncomputable def rayMean (θ : ℝ × ℝ) (t : ℝ) : ℝ :=
  rayNumerator θ t / Z (t • θ)

lemma hasDerivAt_Z_ray (θ : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Z (s • θ)) (rayNumerator θ t) t := by
  simpa only [Z, rayNumerator, Finset.sum_apply] using
    HasDerivAt.sum (u := Finset.univ) (fun y _ => hasDerivAt_un_ray θ y t)

lemma hasDerivAt_numerator (θ : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (rayNumerator θ) (raySecond θ t) t := by
  convert HasDerivAt.sum (fun y (_ : y ∈ Finset.univ) =>
    (hasDerivAt_un_ray θ y t).mul_const (dot θ (coord y))) using 1
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma ray_variance_nonneg (θ : ℝ × ℝ) (t : ℝ) :
    0 ≤ raySecond θ t * Z (t • θ) - (rayNumerator θ t)^2 := by
  have h : 0 ≤ ∑ y, un (t • θ) y *
      (dot θ (coord y) - rayMean θ t)^2 := by
    apply Finset.sum_nonneg
    intro y _
    exact mul_nonneg (un_pos _ _).le (sq_nonneg _)
  have heq : (∑ y, un (t • θ) y *
      (dot θ (coord y) - rayMean θ t)^2) =
      raySecond θ t - 2 * rayMean θ t * rayNumerator θ t +
        (rayMean θ t)^2 * Z (t • θ) := by
    calc
      _ = ∑ y, (un (t • θ) y * (dot θ (coord y))^2 -
          2 * rayMean θ t * (un (t • θ) y * dot θ (coord y)) +
          (rayMean θ t)^2 * un (t • θ) y) := by
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          raySecond, rayNumerator, Z]
  rw [heq] at h
  have hz := Z_pos (t • θ)
  have heq2 : raySecond θ t - 2 * rayMean θ t * rayNumerator θ t +
      (rayMean θ t)^2 * Z (t • θ) =
      (raySecond θ t * Z (t • θ) - (rayNumerator θ t)^2) / Z (t • θ) := by
    unfold rayMean
    field_simp
    <;> ring
  rw [heq2] at h
  simpa only [zero_mul] using (le_div_iff₀ hz).mp h

lemma rayMean_monotone (θ : ℝ × ℝ) : Monotone (rayMean θ) := by
  apply monotone_of_hasDerivAt_nonneg
    (f' := fun t => (raySecond θ t * Z (t • θ) - (rayNumerator θ t)^2) / (Z (t • θ))^2)
  · intro t
    simpa only [rayMean, pow_two] using
      (hasDerivAt_numerator θ t).div (hasDerivAt_Z_ray θ t) (ne_of_gt (Z_pos _))
  · intro t
    exact div_nonneg (ray_variance_nonneg θ t) (sq_nonneg _)

lemma inner_toES (a b : ℝ × ℝ) :
    inner ℝ (toES a) (toES b) = dot a b := by
  simp [PiLp.inner_apply, toES, dot, Fin.sum_univ_succ, Fin.succ]
  <;> ring

lemma abs_dot_le (θ : ℝ × ℝ) (y : Fin 9) :
    |dot θ (coord y)| ≤ ‖toES θ‖ := by
  rw [← inner_toES]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (norm_toES_coord_le_one y))

lemma rayMean_inner (θ : ℝ × ℝ) (t : ℝ) :
    rayMean θ t = inner ℝ (toES θ) (esMean (pt (t • θ))) := by
  simp only [rayMean, rayNumerator, esMean, inner_sum, inner_smul_right, inner_toES,
    pt, div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma toES_smul (a : ℝ) (θ : ℝ × ℝ) : toES (a • θ) = a • toES θ := by
  ext i
  fin_cases i <;> simp [toES, smul_eq_mul]

lemma base_esMean : esMean p0 = 0 := by
  ext i
  fin_cases i <;> norm_num [esMean, p0, coord, toES, Fin.sum_univ_succ, Fin.succ] <;> ring

lemma base_norm_average : ∑ y, p0 y * ‖toES (coord y)‖ = (9/10 : ℝ)*(1-ε) := by
  simp only [norm_toES]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [p0, Fin.succ, coord, euclNorm, ρ_sq, sqrt_two_rho_sq]
  have h16 := Real.sqrt_sq (show (0:ℝ) ≤ 4 by norm_num)
  have h25 := Real.sqrt_sq (show (0:ℝ) ≤ 5 by norm_num)
  norm_num at h16 h25
  rw [h16, h25, w_eq]
  ring

lemma base_dot_zero (θ : ℝ × ℝ) : ∑ y, p0 y * dot θ (coord y) = 0 := by
  have h := congrArg (inner ℝ (toES θ)) base_esMean
  simpa [esMean, inner_sum, inner_smul_right, inner_toES] using h

lemma base_dot_second (θ : ℝ × ℝ) :
    ∑ y, p0 y * (dot θ (coord y))^2 =
      (41/100 : ℝ)*(1-ε)*‖toES θ‖^2 := by
  rw [norm_toES, euclNorm]
  rw [Real.sq_sqrt (by positivity)]
  norm_num [p0, dot, coord, Fin.sum_univ_succ, Fin.succ]
  have hρ := ρ_sq
  rw [w_eq]
  ring_nf
  <;> simp only [ρ_sq]
  <;> ring

lemma exp_sub_one_small {a : ℝ} (ha : |a| ≤ 1/10) :
    |exp a - 1| ≤ (11/10 : ℝ)*|a| := by
  have h := abs_exp_sub_one_sub_id_le (x := a) (by linarith)
  have ht := abs_add_le (exp a - 1 - a) a
  have heq : exp a - 1 - a + a = exp a - 1 := by ring
  rw [heq] at ht
  have hs : a^2 ≤ |a|/10 := by nlinarith [sq_abs a, abs_nonneg a]
  linarith

lemma dot_exp_small {a : ℝ} (ha : |a| ≤ 1/10) :
    (9/10 : ℝ)*a^2 ≤ (exp a - 1)*a := by
  have h := abs_exp_sub_one_sub_id_le (x := a) (by linarith)
  have hbounds := abs_le.mp h
  have hab := abs_le.mp ha
  rcases le_total 0 a with hsign | hsign
  · have hh := mul_le_mul_of_nonneg_right hbounds.1 hsign
    have h3 := mul_nonneg (sq_nonneg a) (show 0 ≤ (1/10 : ℝ)-a by linarith)
    nlinarith
  · have hh := mul_le_mul_of_nonpos_right hbounds.2 hsign
    have h3 := mul_nonneg (sq_nonneg a) (show 0 ≤ (1/10 : ℝ)+a by linarith)
    nlinarith

lemma Z_local_upper {θ : ℝ × ℝ} (hθ : ‖toES θ‖^2 ≤ 1/100) : Z θ < (9:ℝ)/8 := by
  have hsq : θ.1^2 + θ.2^2 ≤ 1/100 := by
    simpa [norm_toES, euclNorm, Real.sq_sqrt (by positivity : 0 ≤ θ.1^2+θ.2^2)] using hθ
  change Z (θ.1, θ.2) < _
  rw [Z_eq_cosh]
  have h := mul_lt_mul_of_pos_left (Z8_upper hsq) w_pos
  rw [w_eq] at h ⊢
  nlinarith [ε_pos]

lemma mean_centered_sum (θ : ℝ × ℝ) :
    esMean (pt θ) = (1 / Z θ) •
      ∑ y, ((exp (dot θ (coord y))-1)*p0 y) • toES (coord y) := by
  have heq : (∑ y, ((exp (dot θ (coord y))-1)*p0 y) • toES (coord y)) =
      (∑ y, (exp (dot θ (coord y))*p0 y) • toES (coord y)) - esMean p0 := by
    simp only [sub_mul, one_mul, sub_smul, Finset.sum_sub_distrib, esMean]
  rw [heq, base_esMean, sub_zero]
  simp only [esMean, pt, un, Finset.smul_sum, smul_smul]
  congr 1
  ext y
  ring

lemma mean_norm_local {θ : ℝ × ℝ} (hθ : ‖toES θ‖^2 ≤ 1/100) :
    ‖esMean (pt θ)‖ ≤ ‖toES θ‖ := by
  have hn : ‖toES θ‖ ≤ 1/10 := by nlinarith [norm_nonneg (toES θ)]
  have hsum : ‖∑ y, ((exp (dot θ (coord y))-1)*p0 y) • toES (coord y)‖ ≤
      (11/10 : ℝ)*‖toES θ‖*((9/10 : ℝ)*(1-ε)) := by
    calc
      _ ≤ ∑ y, ‖((exp (dot θ (coord y))-1)*p0 y) • toES (coord y)‖ := norm_sum_le _ _
      _ ≤ ∑ y, ((11/10 : ℝ)*‖toES θ‖) * (p0 y * ‖toES (coord y)‖) := by
        apply Finset.sum_le_sum
        intro y _
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (p0_nonneg y)]
        have he := exp_sub_one_small ((abs_dot_le θ y).trans hn)
        have hle : |exp (dot θ (coord y))-1| ≤ (11/10 : ℝ)*‖toES θ‖ :=
          he.trans (mul_le_mul_of_nonneg_left (abs_dot_le θ y) (by norm_num))
        nlinarith [mul_nonneg (p0_nonneg y) (norm_nonneg (toES (coord y))),
          mul_le_mul_of_nonneg_right hle (mul_nonneg (p0_nonneg y) (norm_nonneg (toES (coord y))))]
      _ = _ := by rw [← Finset.mul_sum, base_norm_average]
  rw [mean_centered_sum, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ((one_div_pos.mpr (Z_pos θ)).le)]
  have hinv : 1 / Z θ ≤ 1 := (div_le_one (Z_pos θ)).mpr (Z_ge_one θ)
  have he := ε_pos
  have hz := norm_nonneg (∑ y, ((exp (dot θ (coord y))-1)*p0 y) • toES (coord y))
  have hh := mul_le_mul_of_nonneg_right hinv hz
  nlinarith [norm_nonneg (toES θ), mul_nonneg ε_pos.le (norm_nonneg (toES θ))]

lemma rayMean_local_lower {θ : ℝ × ℝ} (hθ : ‖toES θ‖^2 ≤ 1/100) :
    (3/10 : ℝ)*‖toES θ‖^2 ≤ rayMean θ 1 := by
  have hn : ‖toES θ‖ ≤ 1/10 := by nlinarith [norm_nonneg (toES θ)]
  have hsum : (9/10 : ℝ)*(∑ y, p0 y*(dot θ (coord y))^2) ≤ rayNumerator θ 1 := by
    have hpt : ∀ y, (9/10 : ℝ)*(p0 y*(dot θ (coord y))^2) ≤
        un θ y * dot θ (coord y) - p0 y * dot θ (coord y) := by
      intro y
      have h := mul_le_mul_of_nonneg_right
        (dot_exp_small ((abs_dot_le θ y).trans hn)) (p0_nonneg y)
      dsimp [un]
      nlinarith
    have h := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hpt y)
    rw [Finset.sum_sub_distrib, base_dot_zero, sub_zero, ← Finset.mul_sum] at h
    simpa [rayNumerator] using h
  rw [base_dot_second] at hsum
  unfold rayMean
  simp only [one_smul]
  apply (le_div_iff₀ (Z_pos θ)).mpr
  have hz := Z_local_upper hθ
  have hmul := mul_le_mul_of_nonneg_left hz.le (by positivity : 0 ≤ (3/10 : ℝ)*‖toES θ‖^2)
  have hc : (27/80 : ℝ) ≤ (9/10 : ℝ)*(41/100)*(1-ε) := by rw [ε_eq]; norm_num
  have hc' := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖toES θ‖)
  nlinarith

lemma rayMean_scale (a : ℝ) (θ : ℝ × ℝ) (t : ℝ) :
    rayMean (a • θ) t = a * rayMean θ (t*a) := by
  unfold rayMean rayNumerator
  simp only [dot_smul, smul_smul]
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma mean_norm_large {θ : ℝ × ℝ} (hθ : (1/10 : ℝ) ≤ ‖toES θ‖) :
    (3/100 : ℝ) ≤ ‖esMean (pt θ)‖ := by
  let a := (1/10 : ℝ)/‖toES θ‖
  have hn : 0 < ‖toES θ‖ := lt_of_lt_of_le (by norm_num) hθ
  have ha : 0 < a := div_pos (by norm_num) hn
  have ha1 : a ≤ 1 := (div_le_one hn).mpr hθ
  have heq : a*‖toES θ‖ = 1/10 := by dsimp [a]; field_simp
  have hnorm : ‖toES (a • θ)‖ = 1/10 := by
    rw [toES_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ha, heq]
  have hl := rayMean_local_lower (θ := a • θ) (by rw [hnorm]; norm_num)
  rw [hnorm, rayMean_scale, one_mul] at hl
  have hm := mul_le_mul_of_nonneg_left (rayMean_monotone θ ha1) ha.le
  have hu : rayMean θ 1 ≤ ‖toES θ‖*‖esMean (pt θ)‖ := by
    rw [rayMean_inner, one_smul]
    exact real_inner_le_norm _ _
  have hu' := mul_le_mul_of_nonneg_left hu ha.le
  nlinarith

lemma boundary_parameter_bounds {θ : ℝ × ℝ} (hμ : ‖esMean (pt θ)‖ = r₀) :
    r₀ ≤ ‖toES θ‖ ∧ ‖toES θ‖ < 1/10 := by
  have hsmall : ‖toES θ‖ < 1/10 := by
    by_contra h
    have hlarge := mean_norm_large (le_of_not_gt h)
    rw [hμ, r₀_eq] at hlarge
    norm_num at hlarge
  refine ⟨?_, hsmall⟩
  rw [← hμ]
  apply mean_norm_local
  nlinarith [norm_nonneg (toES θ)]

/-- Uniform separator on the actual mean circle, with no natural-coordinate premise. -/
theorem separator_boundary {θ : ℝ × ℝ} (hμ : ‖esMean (pt θ)‖ = r₀) :
    (35/100 : ℝ)*(1-ε)/9*r₀^2 ≤ FinProb.expect (tiltProb θ) separator := by
  have hb := boundary_parameter_bounds hμ
  have hsq : θ.1^2+θ.2^2 = ‖toES θ‖^2 := by
    rw [norm_toES, euclNorm, Real.sq_sqrt (by positivity)]
  have hs : θ.1^2+θ.2^2 ≤ 1/100 := by
    rw [hsq]
    nlinarith [norm_nonneg (toES θ)]
  have hl := separator_local hs
  have hcoef : 0 ≤ (35/100 : ℝ)*(1-ε)/9 := by
    have he : 0 ≤ 1-ε := by linarith [ε_lt_one]
    positivity
  have hh := mul_le_mul_of_nonneg_left
    (show r₀^2 ≤ θ.1^2+θ.2^2 by rw [hsq]; nlinarith [r₀_pos]) hcoef
  exact hh.trans hl

end BoundaryReduction.NinePoint
