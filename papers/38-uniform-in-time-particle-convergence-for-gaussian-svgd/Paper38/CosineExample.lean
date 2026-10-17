import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The concrete cosine perturbation in P38, Example 9.1

The definitions below use the variance `s` (rather than its square root), as in
Section 9 of the source. All integrals are over Mathlib's actual Gaussian measure.
-/

noncomputable section

open Real Set

namespace Paper38.Cosine

/-- The nonquadratic potential (9.1). -/
def potential (ε x : ℝ) : ℝ := x ^ 2 / 2 + ε * (1 + Real.cos x)

def force (ε x : ℝ) : ℝ := x - ε * Real.sin x

def curvature (ε x : ℝ) : ℝ := 1 - ε * Real.cos x

/-- Gaussian attenuation for variance `s`. -/
def attenuation (s : ℝ) : ℝ := Real.exp (-s / 2)

def meanForce (ε μ s : ℝ) : ℝ := μ - ε * attenuation s * Real.sin μ

def meanCurvature (ε μ s : ℝ) : ℝ := 1 - ε * attenuation s * Real.cos μ

/-- The constant-free Gaussian reverse-KL energy (9.4). -/
def energy (ε μ s : ℝ) : ℝ :=
  (μ ^ 2 + s - Real.log s) / 2 + ε * attenuation s * Real.cos μ

def varianceGradient (ε μ s : ℝ) : ℝ :=
  (1 - 1 / s - ε * attenuation s * Real.cos μ) / 2

def meanVelocity (ε μ s : ℝ) : ℝ :=
  (1 - meanCurvature ε μ s * s) * μ - (1 + μ ^ 2) * meanForce ε μ s

def varianceVelocity (ε μ s : ℝ) : ℝ :=
  2 * s * (1 - meanCurvature ε μ s * s - μ * meanForce ε μ s)

/-- The scalar equation characterizing the optimal variance (9.8). -/
def varianceEquation (ε s : ℝ) : ℝ := s * (1 - ε * attenuation s)

lemma hasDerivAt_potential (ε x : ℝ) :
    HasDerivAt (potential ε) (force ε x) x := by
  convert ((hasDerivAt_id x).pow 2 |>.div_const 2).add
    (((hasDerivAt_const x 1).add (Real.hasDerivAt_cos x)).const_mul ε) using 1 <;>
    simp [potential, force] <;> ring

lemma hasDerivAt_force (ε x : ℝ) :
    HasDerivAt (force ε) (curvature ε x) x := by
  convert (hasDerivAt_id x).sub ((Real.hasDerivAt_sin x).const_mul ε) using 1 <;>
    simp [force, curvature]

lemma deriv_potential (ε x : ℝ) : deriv (potential ε) x = force ε x :=
  (hasDerivAt_potential ε x).deriv

lemma deriv_force (ε x : ℝ) : deriv (force ε) x = curvature ε x :=
  (hasDerivAt_force ε x).deriv

lemma second_deriv_potential (ε x : ℝ) :
    deriv (deriv (potential ε)) x = curvature ε x := by
  have h : deriv (potential ε) = force ε := funext (deriv_potential ε)
  rw [h, deriv_force]

lemma contDiff_potential (ε : ℝ) : ContDiff ℝ ⊤ (potential ε) := by
  unfold potential
  fun_prop

lemma curvature_bounds {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    1 - ε ≤ curvature ε x ∧ curvature ε x ≤ 1 + ε := by
  have h₁ := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hε
  have h₂ := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos x) hε
  constructor <;> unfold curvature <;> nlinarith

lemma source_hessian_bounds {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10) (x : ℝ) :
    0 < 1 - ε ∧ 1 - ε ≤ deriv (deriv (potential ε)) x ∧
      deriv (deriv (potential ε)) x ≤ 1 + ε := by
  rw [second_deriv_potential]
  exact ⟨by linarith, curvature_bounds hε.le x⟩

lemma attenuation_pos (s : ℝ) : 0 < attenuation s := Real.exp_pos _

lemma attenuation_le_one {s : ℝ} (hs : 0 ≤ s) : attenuation s ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (by linarith)

lemma hasDerivAt_attenuation (s : ℝ) :
    HasDerivAt attenuation (-attenuation s / 2) s := by
  convert (((hasDerivAt_id s).neg.div_const 2).exp) using 1 <;>
    simp [attenuation] <;> ring

lemma hasDerivAt_energy_mean (ε μ s : ℝ) :
    HasDerivAt (fun u => energy ε u s) (meanForce ε μ s) μ := by
  convert ((((hasDerivAt_id μ).pow 2).add_const s).sub_const (Real.log s)).div_const 2 |>.add
    ((Real.hasDerivAt_cos μ).const_mul (ε * attenuation s)) using 1 <;>
    simp [energy, meanForce] <;> ring

lemma hasDerivAt_energy_variance (ε μ : ℝ) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (energy ε μ) (varianceGradient ε μ s) s := by
  convert (((hasDerivAt_id s).const_add (μ ^ 2)).sub (Real.hasDerivAt_log hs)).div_const 2 |>.add
    (((hasDerivAt_attenuation s).const_mul ε).mul_const (Real.cos μ)) using 1 <;>
    simp [energy, varianceGradient] <;> ring

lemma hasDerivAt_meanForce (ε μ s : ℝ) :
    HasDerivAt (fun u => meanForce ε u s) (meanCurvature ε μ s) μ := by
  convert (hasDerivAt_id μ).sub ((Real.hasDerivAt_sin μ).const_mul (ε * attenuation s)) using 1 <;>
    simp [meanForce, meanCurvature]

lemma hasDerivAt_varianceGradient_variance (ε μ : ℝ) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun v => varianceGradient ε μ v)
      (1 / (2 * s ^ 2) + ε * attenuation s * Real.cos μ / 4) s := by
  convert (((hasDerivAt_const s 1).sub ((hasDerivAt_id s).inv hs)).sub
    (((hasDerivAt_attenuation s).const_mul ε).mul_const (Real.cos μ))).div_const 2 using 1 <;>
    simp [varianceGradient] <;> field_simp <;> ring

lemma hasDerivAt_varianceGradient_mean (ε μ s : ℝ) :
    HasDerivAt (fun u => varianceGradient ε u s)
      (ε * attenuation s * Real.sin μ / 2) μ := by
  convert ((hasDerivAt_const μ (1 - 1 / s)).sub
    ((Real.hasDerivAt_cos μ).const_mul (ε * attenuation s))).div_const 2 using 1 <;>
    simp [varianceGradient] <;> ring

lemma hasDerivAt_meanForce_variance (ε μ s : ℝ) :
    HasDerivAt (meanForce ε μ)
      (ε * attenuation s * Real.sin μ / 2) s := by
  convert (hasDerivAt_const s μ).sub
    (((hasDerivAt_attenuation s).const_mul ε).mul_const (Real.sin μ)) using 1 <;>
    simp [meanForce] <;> ring

/-- The first row of the mobility identity (9.5). -/
lemma mean_mobility (ε μ : ℝ) {s : ℝ} (hs : s ≠ 0) :
    meanVelocity ε μ s =
      -((1 + μ ^ 2) * meanForce ε μ s + 2 * s * μ * varianceGradient ε μ s) := by
  unfold meanVelocity meanForce meanCurvature varianceGradient
  field_simp
  ring

/-- The second row of the mobility identity (9.5). -/
lemma variance_mobility (ε μ : ℝ) {s : ℝ} (hs : s ≠ 0) :
    varianceVelocity ε μ s =
      -(2 * s * μ * meanForce ε μ s + 4 * s ^ 2 * varianceGradient ε μ s) := by
  unfold varianceVelocity meanForce meanCurvature varianceGradient
  field_simp
  ring

lemma mobility_determinant (μ s : ℝ) :
    (1 + μ ^ 2) * (4 * s ^ 2) - (2 * s * μ) ^ 2 = 4 * s ^ 2 := by ring

lemma mobility_determinant_pos (μ : ℝ) {s : ℝ} (hs : 0 < s) :
    0 < (1 + μ ^ 2) * (4 * s ^ 2) - (2 * s * μ) ^ 2 := by
  rw [mobility_determinant]
  positivity

/-- Positive definiteness of the actual mobility as a quadratic form. -/
lemma mobility_positive_definite (μ : ℝ) {s : ℝ} (hs : 0 < s)
    (u v : ℝ) (huv : (u, v) ≠ (0, 0)) :
    0 < (1 + μ ^ 2) * u ^ 2 + 2 * (2 * s * μ) * u * v + 4 * s ^ 2 * v ^ 2 := by
  have hsum : (1 + μ ^ 2) * u ^ 2 + 2 * (2 * s * μ) * u * v + 4 * s ^ 2 * v ^ 2 =
      u ^ 2 + (μ * u + 2 * s * v) ^ 2 := by ring
  rw [hsum]
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by intro hv; exact huv (by simp [hu, hv])
    simp only [hu, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]
    exact sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) hs.ne') hv)
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hu) (sq_nonneg _)

lemma hasDerivAt_varianceEquation (ε s : ℝ) :
    HasDerivAt (varianceEquation ε)
      (1 - ε * attenuation s + ε * s * attenuation s / 2) s := by
  convert (hasDerivAt_id s).mul
    ((hasDerivAt_const s 1).sub ((hasDerivAt_attenuation s).const_mul ε)) using 1 <;>
    simp [varianceEquation] <;> ring

lemma varianceEquation_deriv_lower {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 ≤ s) :
    1 - ε ≤ 1 - ε * attenuation s + ε * s * attenuation s / 2 := by
  have hmul := mul_le_mul_of_nonneg_left (attenuation_le_one hs) hε
  have hn : 0 ≤ ε * s * attenuation s / 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hε hs) (attenuation_pos s).le) (by norm_num)
  linarith

lemma varianceEquation_strictMonoOn {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1) :
    StrictMonoOn (varianceEquation ε) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · unfold varianceEquation attenuation
    fun_prop
  · intro s hs
    rw [(hasDerivAt_varianceEquation ε s).deriv]
    have hs' : 0 ≤ s := interior_subset hs
    have := varianceEquation_deriv_lower hε hs'
    linarith

/-- Existence and uniqueness in (9.8), with an explicit compact bracketing interval. -/
lemma existsUnique_optimal_variance {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1) :
    ∃! s : ℝ, 0 < s ∧ varianceEquation ε s = 1 := by
  have hden : 0 < 1 - ε := by linarith
  let b : ℝ := 1 / (1 - ε)
  have hb : 0 < b := one_div_pos.mpr hden
  have hcont : ContinuousOn (varianceEquation ε) (Icc 0 b) := by
    unfold varianceEquation attenuation
    fun_prop
  have hzero : varianceEquation ε 0 = 0 := by simp [varianceEquation]
  have hend : 1 ≤ varianceEquation ε b := by
    have he := mul_le_mul_of_nonneg_left (attenuation_le_one hb.le) hε
    have hbprod : b * (1 - ε) = 1 := by dsimp [b]; field_simp
    unfold varianceEquation
    nlinarith
  obtain ⟨s, hs, heq⟩ := intermediate_value_Icc hb.le hcont (show 1 ∈ Icc
    (varianceEquation ε 0) (varianceEquation ε b) from ⟨by rw [hzero]; norm_num, hend⟩)
  have hspos : 0 < s := by
    have hsne : s ≠ 0 := by intro hh; simp [hh, hzero] at heq
    exact lt_of_le_of_ne hs.1 (Ne.symm hsne)
  refine ⟨s, ⟨hspos, heq⟩, ?_⟩
  intro t ht
  exact (varianceEquation_strictMonoOn hε hε').injOn ht.1.le hspos.le (ht.2.trans heq.symm)

lemma stationary_at_optimal_variance (ε : ℝ) {s : ℝ} (hs : 0 < s)
    (hroot : varianceEquation ε s = 1) :
    meanForce ε 0 s = 0 ∧ varianceGradient ε 0 s = 0 := by
  constructor
  · simp [meanForce]
  · simp only [varianceGradient, Real.cos_zero, mul_one]
    unfold varianceEquation at hroot
    field_simp
    nlinarith

lemma meanCurvature_lower {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 ≤ s) (μ : ℝ) :
    1 - ε ≤ meanCurvature ε μ s := by
  have ha := attenuation_le_one hs
  have he : 0 ≤ ε * attenuation s := mul_nonneg hε (attenuation_pos s).le
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one μ) he
  have hprod := mul_le_mul_of_nonneg_left ha hε
  unfold meanCurvature
  nlinarith

lemma meanForce_strictMono {ε s : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1) (hs : 0 ≤ s) :
    StrictMono (fun μ => meanForce ε μ s) := by
  apply strictMono_of_hasDerivAt_pos (fun μ => hasDerivAt_meanForce ε μ s)
  intro μ
  have := meanCurvature_lower hε hs μ
  linarith

/-- For every positive variance the unique minimizing mean is zero. -/
lemma energy_mean_strict_minimum {ε s : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1) (hs : 0 ≤ s)
    {μ : ℝ} (hμ : μ ≠ 0) : energy ε 0 s < energy ε μ s := by
  have hm := meanForce_strictMono hε hε' hs
  have hm0 : meanForce ε 0 s = 0 := by simp [meanForce]
  rcases lt_or_gt_of_ne hμ with hμ | hμ
  · have hf : StrictAntiOn (fun u => energy ε u s) (Iic 0) := by
      apply strictAntiOn_of_deriv_neg (convex_Iic 0)
      · exact fun x _ => (hasDerivAt_energy_mean ε x s).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Iic] at hx
        rw [(hasDerivAt_energy_mean ε x s).deriv]
        simpa [hm0] using hm hx
    exact hf (show μ ∈ Iic 0 from hμ.le) (show (0 : ℝ) ∈ Iic 0 by simp) hμ
  · have hf : StrictMonoOn (fun u => energy ε u s) (Ici 0) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      · exact fun x _ => (hasDerivAt_energy_mean ε x s).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Ici] at hx
        rw [(hasDerivAt_energy_mean ε x s).deriv]
        simpa [hm0] using hm hx
    exact hf (show (0 : ℝ) ∈ Ici 0 by simp) (show μ ∈ Ici 0 from hμ.le) hμ

lemma energy_mean_minimum {ε s : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1) (hs : 0 ≤ s)
    (μ : ℝ) : energy ε 0 s ≤ energy ε μ s := by
  by_cases hμ : μ = 0
  · simp [hμ]
  · exact (energy_mean_strict_minimum hε hε' hs hμ).le

lemma varianceGradient_at_zero (ε : ℝ) {s : ℝ} (hs : s ≠ 0) :
    varianceGradient ε 0 s = (varianceEquation ε s - 1) / (2 * s) := by
  simp only [varianceGradient, varianceEquation, Real.cos_zero, mul_one]
  field_simp
  ring

/-- The unique positive root of (9.8) is the unique minimizing variance at zero mean. -/
lemma energy_variance_strict_minimum {ε r s : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1)
    (hr : 0 < r) (hrroot : varianceEquation ε r = 1) (hs : 0 < s) (hsr : s ≠ r) :
    energy ε 0 r < energy ε 0 s := by
  have hm := varianceEquation_strictMonoOn hε hε'
  rcases lt_or_gt_of_ne hsr with hsr | hsr
  · have hf : StrictAntiOn (energy ε 0) (Icc s r) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc s r)
      · intro x hx
        exact (hasDerivAt_energy_variance ε 0 (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxpos : 0 < x := lt_trans hs hx.1
        rw [(hasDerivAt_energy_variance ε 0 hxpos.ne').deriv,
          varianceGradient_at_zero ε hxpos.ne']
        have hlt := hm hxpos.le hr.le hx.2
        rw [hrroot] at hlt
        exact div_neg_of_neg_of_pos (by linarith) (by positivity)
    exact hf ⟨le_rfl, hsr.le⟩ ⟨hsr.le, le_rfl⟩ hsr
  · have hf : StrictMonoOn (energy ε 0) (Icc r s) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc r s)
      · intro x hx
        exact (hasDerivAt_energy_variance ε 0 (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxpos : 0 < x := lt_trans hr hx.1
        rw [(hasDerivAt_energy_variance ε 0 hxpos.ne').deriv,
          varianceGradient_at_zero ε hxpos.ne']
        have hlt := hm hr.le hxpos.le hx.1
        rw [hrroot] at hlt
        exact div_pos (by linarith) (by positivity)
    exact hf ⟨le_rfl, hsr.le⟩ ⟨hsr.le, le_rfl⟩ hsr

lemma energy_variance_minimum {ε r : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1)
    (hr : 0 < r) (hrroot : varianceEquation ε r = 1) {s : ℝ} (hs : 0 < s) :
    energy ε 0 r ≤ energy ε 0 s := by
  by_cases hsr : s = r
  · simp [hsr]
  · exact (energy_variance_strict_minimum hε hε' hr hrroot hs hsr).le

/-- A full, unconditional-in-the-state characterization of the variational optimum.
The hypotheses `0 ≤ ε < 1` are weaker than the source's `0 < ε ≤ 0.1`. -/
lemma unique_global_minimum {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1) :
    ∃ r : ℝ, 0 < r ∧ varianceEquation ε r = 1 ∧
      (∀ μ s : ℝ, 0 < s → energy ε 0 r ≤ energy ε μ s) ∧
      (∀ μ s : ℝ, 0 < s → energy ε μ s = energy ε 0 r → μ = 0 ∧ s = r) := by
  obtain ⟨r, hr, _⟩ := existsUnique_optimal_variance hε hε'
  refine ⟨r, hr.1, hr.2, ?_, ?_⟩
  · intro μ s hs
    exact (energy_variance_minimum hε hε' hr.1 hr.2 hs).trans
      (energy_mean_minimum hε hε' hs.le μ)
  · intro μ s hs heq
    have h₁ := energy_variance_minimum hε hε' hr.1 hr.2 hs
    have h₂ := energy_mean_minimum hε hε' hs.le μ
    have hμ : μ = 0 := by
      by_contra hμ
      have := energy_mean_strict_minimum hε hε' hs.le hμ
      linarith
    have hsr : s = r := by
      by_contra hsr
      have := energy_variance_strict_minimum hε hε' hr.1 hr.2 hs hsr
      linarith
    exact ⟨hμ, hsr⟩

/-- The elementary maximization underlying the two bounds used in (9.7). -/
lemma sq_mul_exp_neg_le {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x) ≤ 4 * Real.exp (-2) := by
  have hd (y : ℝ) : HasDerivAt (fun z : ℝ => z ^ 2 * Real.exp (-z))
      (y * Real.exp (-y) * (2 - y)) y := by
    convert ((hasDerivAt_id y).pow 2).mul ((hasDerivAt_id y).neg.exp) using 1 <;>
      simp <;> ring
  by_cases hx2 : x ≤ 2
  · have hm : MonotoneOn (fun z : ℝ => z ^ 2 * Real.exp (-z)) (Icc 0 2) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 2)
      · exact fun y _ => (hd y).continuousAt.continuousWithinAt
      · exact fun y _ => (hd y).differentiableAt.differentiableWithinAt
      · intro y hy
        have hy' := interior_subset hy
        rw [(hd y).deriv]
        exact mul_nonneg (mul_nonneg hy'.1 (Real.exp_pos _).le) (by linarith [hy'.2])
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hm ⟨hx, hx2⟩ ⟨by norm_num, le_rfl⟩ hx2
  · have ha : AntitoneOn (fun z : ℝ => z ^ 2 * Real.exp (-z)) (Ici 2) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 2)
      · exact fun y _ => (hd y).continuousAt.continuousWithinAt
      · exact fun y _ => (hd y).differentiableAt.differentiableWithinAt
      · intro y hy
        have hy' : 2 ≤ y := interior_subset hy
        rw [(hd y).deriv]
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (by linarith) (Real.exp_pos _).le) (by linarith)
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using ha (show (2 : ℝ) ∈ Ici 2 by simp) (show x ∈ Ici 2 from le_of_not_ge hx2)
      (le_of_not_ge hx2)

lemma source_exponential_bounds {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 * Real.exp (-s / 2) ≤ 16 * Real.exp (-2) ∧
      s ^ 2 * Real.exp (-s) ≤ 4 * Real.exp (-2) := by
  have h := sq_mul_exp_neg_le (show 0 ≤ s / 2 by positivity)
  have heq : -(s / 2) = -s / 2 := by ring
  rw [heq] at h
  constructor
  · nlinarith
  · exact sq_mul_exp_neg_le hs

end Paper38.Cosine
