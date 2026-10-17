import PUT.ExternalMoments

/-!
# Paper Lemma 2 from the standard external joint moment law

All centered moment, Holder, TV moment and event probability arguments are
proved here.  Only the published standard Dirichlet joint moment identity
is a named explicit input; the probability measure is the actual continuous
normalized-gamma measure throughout.
-/

noncomputable section
namespace PUT
open MeasureTheory Set Filter
open scoped ENNReal

def coordinatePowerIndex {d : ℕ} (i : Fin d) (r : ℕ) : Fin d → ℕ :=
  fun j => if j = i then r else 0

theorem coordinatePowerIndex_prod {d : ℕ} (i : Fin d) (r : ℕ) (p : Fin d → ℝ) :
    (∏ j, p j ^ coordinatePowerIndex i r j) = p i ^ r := by
  simp [coordinatePowerIndex]

theorem coordinatePowerIndex_moment {d : ℕ} (i : Fin d) (r : ℕ) (a : ℝ) :
    dirMoment a (coordinatePowerIndex i r) =
      risingFactorial a r / risingFactorial (a * d) r := by
  simp [dirMoment, coordinatePowerIndex, degK, apply_ite]

/-- Coordinate raw moments are derived by specializing the joint law,
not supplied as a new external premise. -/
theorem dirichlet_coordinate_moment (hMom : External.DirichletJointMomentLaw)
    {d : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) (i : Fin d) (r : ℕ) :
    Integrable (fun p : Fin d → ℝ => p i ^ r) (dirichletMeasure d a) ∧
      (∫ p, p i ^ r ∂dirichletMeasure d a) =
        risingFactorial a r / risingFactorial (a * d) r := by
  simpa only [coordinatePowerIndex_prod, coordinatePowerIndex_moment] using
    hMom d a (coordinatePowerIndex i r) hd ha

theorem dirichlet_coordinate_beta_moment (hMom : External.DirichletJointMomentLaw)
    {d : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) (i : Fin d) (r : ℕ) :
    (∫ p, p i ^ r ∂dirichletMeasure d a) = betaRawMoment a ((d - 1 : ℝ) * a) r := by
  have hs : a + (d - 1 : ℝ) * a = a * d := by ring
  rw [(dirichlet_coordinate_moment hMom hd ha i r).2]
  simp only [betaRawMoment, hs]

theorem betaMean_dirichlet (d : ℕ) (a : ℝ) (hd : 0 < d) (ha : 0 < a) :
    betaMean a ((d - 1 : ℝ) * a) = 1 / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : a + (d - 1 : ℝ) * a = a * d := by ring
  unfold betaMean
  rw [hs]
  field_simp

/-- Boundedness supplies all integrability facts needed by interpolation. -/
theorem dirichlet_centered_memLp {d : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a)
    (i : Fin d) (q : ℝ≥0∞) :
    MemLp (fun p : Fin d → ℝ => p i - 1 / d) q (dirichletMeasure d a) := by
  letI := isProbabilityMeasure_dirichletMeasure d ha
  apply MemLp.of_bound
    ((measurable_pi_apply i).sub measurable_const).aestronglyMeasurable 1
  filter_upwards [dirichletMeasure_ae_positiveSimplex (by omega : 0 < d) ha] with p hp
  have hpi0 : 0 ≤ p i := (hp.1 i).le
  have hpi1 : p i ≤ 1 := by
    calc p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => (hp.1 j).le) (Finset.mem_univ i)
      _ = 1 := hp.2
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hdpos : (0 : ℝ) < d := by linarith
  have hc0 : (0 : ℝ) ≤ 1 / d := by positivity
  have hc1 : (1 : ℝ) / d ≤ 1 := (div_le_one (by positivity)).mpr hdR
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem dirichlet_centered_abs_pow_integrable {d : ℕ} (hd : 2 ≤ d)
    {a : ℝ} (ha : 0 < a) (i : Fin d) (r : ℕ) :
    Integrable (fun p : Fin d → ℝ => |p i - 1 / d| ^ r) (dirichletMeasure d a) := by
  letI := isProbabilityMeasure_dirichletMeasure d ha
  simpa only [Real.norm_eq_abs] using
    (dirichlet_centered_memLp hd ha i r).integrable_norm_pow'

/-- Exact actual second central moment, derived from joint moments. -/
theorem dirichlet_centered_second (hMom : External.DirichletJointMomentLaw)
    {d : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) (i : Fin d) :
    (∫ p : Fin d → ℝ, (p i - 1 / d) ^ 2 ∂dirichletMeasure d a) = dirVar a d := by
  letI := isProbabilityMeasure_dirichletMeasure d ha
  let c : ℝ := 1 / d
  let b : ℝ := (d - 1 : ℝ) * a
  have h1 : Integrable (fun p : Fin d → ℝ => p i) (dirichletMeasure d a) := by
    simpa using (dirichlet_coordinate_moment hMom hd ha i 1).1
  have h2 := (dirichlet_coordinate_moment hMom hd ha i 2).1
  have hfun : (fun p : Fin d → ℝ => (p i - c) ^ 2) =
      (fun p => p i ^ 2 - (2 * c) * p i + c ^ 2) := by funext p; ring
  change (∫ p : Fin d → ℝ, (p i - c) ^ 2 ∂dirichletMeasure d a) = dirVar a d
  rw [hfun]
  change (∫ p : Fin d → ℝ,
    (((fun p : Fin d → ℝ => p i ^ 2) - (fun p : Fin d → ℝ => (2 * c) * p i)) +
      (fun _ : Fin d → ℝ => c ^ 2)) p
      ∂dirichletMeasure d a) = dirVar a d
  rw [integral_add' (h2.sub (h1.const_mul (2 * c))) (integrable_const (c ^ 2)),
    integral_sub' h2 (h1.const_mul (2 * c)), integral_const_mul]
  have hm := betaMean_dirichlet d a (by omega) ha
  have hr1 := dirichlet_coordinate_beta_moment hMom hd ha i 1
  have hr2 := dirichlet_coordinate_beta_moment hMom hd ha i 2
  simp only [pow_one] at hr1
  rw [hr1, hr2]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]
  have hcentral : betaRawMoment a b 2 - (2 * c) * betaRawMoment a b 1 + c ^ 2 =
      betaCentral2 a b := by
    unfold betaCentral2
    have hmc : betaMean a b = c := hm
    rw [← hmc, betaRawMoment_one]
    unfold betaMean
    ring
  change betaRawMoment a b 2 - (2 * c) * betaRawMoment a b 1 + c ^ 2 = dirVar a d
  have habpos : 0 < a + b := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    dsimp [b]
    nlinarith
  rw [hcentral, betaCentral2_eq a b habpos]
  exact (dirVar_eq_betaVar a d ha).symm

/-- Exact actual fourth central moment, with no external centered-moment
or kurtosis assumption. -/
theorem dirichlet_centered_fourth (hMom : External.DirichletJointMomentLaw)
    {d : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) (i : Fin d) :
    (∫ p : Fin d → ℝ, (p i - 1 / d) ^ 4 ∂dirichletMeasure d a) =
      betaCentral4 a ((d - 1 : ℝ) * a) := by
  letI := isProbabilityMeasure_dirichletMeasure d ha
  let c : ℝ := 1 / d
  let b : ℝ := (d - 1 : ℝ) * a
  have h1 : Integrable (fun p : Fin d → ℝ => p i) (dirichletMeasure d a) := by
    simpa using (dirichlet_coordinate_moment hMom hd ha i 1).1
  have h2 := (dirichlet_coordinate_moment hMom hd ha i 2).1
  have h3 := (dirichlet_coordinate_moment hMom hd ha i 3).1
  have h4 := (dirichlet_coordinate_moment hMom hd ha i 4).1
  have h43 := h4.sub (h3.const_mul (4 * c))
  have h432 := h43.add (h2.const_mul (6 * c ^ 2))
  have h4321 := h432.sub (h1.const_mul (4 * c ^ 3))
  have hfun : (fun p : Fin d → ℝ => (p i - c) ^ 4) =
      (fun p => p i ^ 4 - (4 * c) * p i ^ 3 +
        (6 * c ^ 2) * p i ^ 2 - (4 * c ^ 3) * p i + c ^ 4) := by funext p; ring
  change (∫ p : Fin d → ℝ, (p i - c) ^ 4 ∂dirichletMeasure d a) = betaCentral4 a b
  rw [hfun]
  change (∫ p : Fin d → ℝ,
    ((((((fun p : Fin d → ℝ => p i ^ 4) -
      (fun p : Fin d → ℝ => (4 * c) * p i ^ 3)) +
      (fun p : Fin d → ℝ => (6 * c ^ 2) * p i ^ 2)) -
      (fun p : Fin d → ℝ => (4 * c ^ 3) * p i)) +
        (fun _ : Fin d → ℝ => c ^ 4)) : (Fin d → ℝ) → ℝ) p
          ∂dirichletMeasure d a) = betaCentral4 a b
  rw [integral_add' h4321 (integrable_const (c ^ 4)),
    integral_sub' h432 (h1.const_mul (4 * c ^ 3)),
    integral_add' h43 (h2.const_mul (6 * c ^ 2)),
    integral_sub' h4 (h3.const_mul (4 * c))]
  simp only [integral_const_mul]
  have hr1 := dirichlet_coordinate_beta_moment hMom hd ha i 1
  simp only [pow_one] at hr1
  rw [hr1, dirichlet_coordinate_beta_moment hMom hd ha i 2,
    dirichlet_coordinate_beta_moment hMom hd ha i 3,
    dirichlet_coordinate_beta_moment hMom hd ha i 4]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]
  unfold betaCentral4
  have hm : betaMean a b = c := betaMean_dirichlet d a (by omega) ha
  rw [hm]

/-- The paper's lower bound on an actual coordinate absolute first moment. -/
theorem dirichlet_coordinate_abs_lower (hMom : External.DirichletJointMomentLaw)
    {d : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 1 ≤ a) (i : Fin d) :
    1 / (6 * d * Real.sqrt a) ≤
      ∫ p : Fin d → ℝ, |p i - 1 / d| ∂dirichletMeasure d a := by
  have ha0 : 0 < a := by linarith
  let μ := dirichletMeasure d a
  let X : (Fin d → ℝ) → ℝ := fun p => p i - 1 / d
  let b : ℝ := (d - 1 : ℝ) * a
  let σ : ℝ := Real.sqrt (dirVar a d)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hb : 0 < b := by dsimp [b]; exact mul_pos (by linarith) ha0
  have hab : a ≤ 2 * b := by dsimp [b]; nlinarith
  have hvarpos : 0 < dirVar a d :=
    lt_of_lt_of_le (by positivity) (dirVar_lower a d ha hd)
  have hσ : 0 < σ := Real.sqrt_pos.mpr hvarpos
  have hσ2 : σ ^ 2 = dirVar a d := Real.sq_sqrt hvarpos.le
  have hX1 : Integrable (fun p => |X p|) μ := by
    simpa [X, μ] using dirichlet_centered_abs_pow_integrable hd ha0 i 1
  have hX2 : Integrable (fun p => X p ^ 2) μ :=
    (dirichlet_centered_memLp hd ha0 i 2).integrable_sq
  have hX3 : Integrable (fun p => |X p| ^ 3) μ :=
    dirichlet_centered_abs_pow_integrable hd ha0 i 3
  have hX4 : Integrable (fun p => X p ^ 4) μ := by
    have hi := dirichlet_centered_abs_pow_integrable hd ha0 i 4
    apply hi.congr
    exact ae_of_all _ (fun p => by dsimp [X]; rw [← abs_pow, abs_of_nonneg (by positivity)])
  have hhold := integral_holder_moments μ X hX1 hX2 hX3 hX4
  have he2 : (∫ p, X p ^ 2 ∂μ) = σ ^ 2 := by
    rw [hσ2]
    exact dirichlet_centered_second hMom hd ha0 i
  have he4 : (∫ p, X p ^ 4 ∂μ) ≤ 9 * σ ^ 4 := by
    have hf := fourth_moment_ratio a b ha0 hb ha hab
    have hv : betaVar a b = dirVar a d := (dirVar_eq_betaVar a d ha0).symm
    have hpow : σ ^ 4 = (dirVar a d) ^ 2 := by
      calc σ ^ 4 = (σ ^ 2) ^ 2 := by ring
        _ = (dirVar a d) ^ 2 := by rw [hσ2]
    rw [show (∫ p, X p ^ 4 ∂μ) = betaCentral4 a b from
      dirichlet_centered_fourth hMom hd ha0 i, hpow, ← hv]
    exact hf
  have hlow := holder_abs_lower hσ (integral_nonneg (fun p => abs_nonneg (X p)))
    he2 he4 hhold
  have hscale := abs_moment_scale a d ha hd
  change 1 / (6 * d * Real.sqrt a) ≤ ∫ p, |X p| ∂μ
  dsimp [σ] at hlow
  linarith

/-- Equation (27), first bound, for the actual continuous Dirichlet law. -/
theorem dirichlet_tv_mean_lower (hMom : External.DirichletJointMomentLaw)
    {d : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 1 ≤ a) :
    1 / (12 * Real.sqrt a) ≤
      ∫ p, tvDist p (uniform d) ∂dirichletMeasure d a := by
  have ha0 : 0 < a := by linarith
  have hAbs (i : Fin d) : Integrable (fun p : Fin d → ℝ => |p i - 1 / d|)
      (dirichletMeasure d a) := by
    simpa using dirichlet_centered_abs_pow_integrable hd ha0 i 1
  unfold tvDist uniform
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun i _ => hAbs i)]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
    (fun i _ => dirichlet_coordinate_abs_lower hMom hd ha i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hs := ez_lower_scale a d ha0 (by omega)
  nlinarith only [hsum, hs]

/-- The finite-dimensional Cauchy bound used for the second TV moment. -/
theorem tvDist_uniform_sq_le (d : ℕ) (p : Fin d → ℝ) :
    tvDist p (uniform d) ^ 2 ≤
      (d : ℝ) / 4 * ∑ i, (p i - 1 / d) ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
    (fun i => |p i - 1 / d|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, sq_abs] at hcs
  unfold tvDist uniform
  nlinarith only [hcs]

/-- Equation (27), second bound, derived by integrating finite Cauchy. -/
theorem dirichlet_tv_second_upper (hMom : External.DirichletJointMomentLaw)
    {d : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 1 ≤ a) :
    (∫ p, tvDist p (uniform d) ^ 2 ∂dirichletMeasure d a) ≤ 1 / (4 * a) := by
  have ha0 : 0 < a := by linarith
  have hX2 (i : Fin d) : Integrable (fun p : Fin d → ℝ => (p i - 1 / d) ^ 2)
      (dirichletMeasure d a) := (dirichlet_centered_memLp hd ha0 i 2).integrable_sq
  have hsumint := integrable_finset_sum Finset.univ (fun i _ => hX2 i)
  have hZ2 := (dirichlet_tv_memLp (by omega : 0 < d) ha0 2).integrable_sq
  have hle := integral_mono hZ2 (hsumint.const_mul ((d : ℝ) / 4))
    (fun p => tvDist_uniform_sq_le d p)
  rw [integral_const_mul,
    integral_finset_sum Finset.univ (fun i _ => hX2 i)] at hle
  simp only [dirichlet_centered_second hMom hd ha0, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  exact hle.trans (by convert ez2_upper_scale a d ha hd using 1; ring)

/-- Full paper Lemma 2, conditional solely on the explicitly published
standard joint Dirichlet moment law.  The tail is measured under the actual
continuous normalized-gamma prior. -/
theorem lemma2_from_joint_moments (hMom : External.DirichletJointMomentLaw) : paperLemma2 := by
  intro d a hd ha
  have ha0 : 0 < a := by linarith
  letI := isProbabilityMeasure_dirichletMeasure d ha0
  exact paley_zygmund_paper_constants (dirichletMeasure d a)
    (fun p => tvDist p (uniform d)) (measurable_tvDist_uniform d)
    (MemLp.integrable (by norm_num) (dirichlet_tv_memLp (by omega) ha0 1))
    (dirichlet_tv_memLp (by omega) ha0 2).integrable_sq a ha
    (dirichlet_tv_mean_lower hMom hd ha) (dirichlet_tv_second_upper hMom hd ha)

end PUT
