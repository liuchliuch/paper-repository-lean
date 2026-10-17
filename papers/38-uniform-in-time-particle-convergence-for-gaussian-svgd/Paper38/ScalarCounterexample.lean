import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.Strong
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proposition 8.1: an explicit scalar counterexample

The assertion in Proposition 8.1 is existential.  The quadratic potential
`V x = x^2 / 2` already supplies a witness.  Its centered Gaussian moment
flow has `m = 0`, `Γ = 1`, and standard-deviation equation
`r' = r * (1 - r^2)`.  We solve this equation explicitly, with the initial
standard deviation retained as a parameter, and prove that its positive
initial-value maps have no common finite Euclidean Lipschitz constant.
-/

namespace Paper38.ScalarCounterexample

open Set Filter Topology
open scoped NNReal ENNReal

noncomputable def potential (x : ℝ) : ℝ := x ^ 2 / 2

theorem potential_smooth : ContDiff ℝ ⊤ potential := by
  unfold potential
  fun_prop

theorem potential_hasDerivAt (x : ℝ) : HasDerivAt potential x x := by
  convert ((hasDerivAt_id x).pow 2).div_const 2 using 1
  simp

theorem potential_deriv (x : ℝ) : deriv potential x = x :=
  (potential_hasDerivAt x).deriv

theorem potential_hessian (x : ℝ) : deriv (deriv potential) x = 1 := by
  simp only [funext potential_deriv, deriv_id'']

theorem potential_hessian_bounds (x : ℝ) :
    1 ≤ deriv (deriv potential) x ∧ deriv (deriv potential) x ≤ 1 := by
  simp [potential_hessian]

theorem potential_strongly_convex : StrongConvexOn (Set.univ : Set ℝ) 1 potential := by
  rw [strongConvexOn_iff_convex]
  convert convexOn_const (0 : ℝ) convex_univ using 1
  ext x
  simp [potential, Real.norm_eq_abs, sq_abs]
  ring

/-- The mean-gradient integral is the actual expectation under the real Gaussian law. -/
theorem gaussian_mean_gradient (μ : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, deriv potential x ∂ProbabilityTheory.gaussianReal μ v) = μ := by
  simp only [potential_deriv, ProbabilityTheory.integral_id_gaussianReal]

/-- The Gaussian Hessian expectation is identically one, at every variance. -/
theorem gaussian_mean_hessian (μ : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, deriv (deriv potential) x ∂ProbabilityTheory.gaussianReal μ v) = 1 := by
  simp [potential_hessian]

/-- In particular, the centered Gaussian has the coefficients m=0 and Γ=1. -/
theorem centered_gaussian_coefficients (v : ℝ≥0) :
    (∫ x : ℝ, deriv potential x ∂ProbabilityTheory.gaussianReal 0 v) = 0 ∧
    (∫ x : ℝ, deriv (deriv potential) x ∂ProbabilityTheory.gaussianReal 0 v) = 1 :=
  ⟨gaussian_mean_gradient 0 v, gaussian_mean_hessian 0 v⟩

/-- The denominator squared in the explicit standard-deviation flow. -/
noncomputable def denominator (t r : ℝ) : ℝ :=
  1 + r ^ 2 * ((Real.exp t) ^ 2 - 1)

/-- The exact centered standard-deviation flow for the unit quadratic potential. -/
noncomputable def flow (t r : ℝ) : ℝ :=
  r * Real.exp t / Real.sqrt (denominator t r)

theorem denominator_ge_one {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    1 ≤ denominator t r := by
  have he : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have he2 : 0 ≤ (Real.exp t) ^ 2 - 1 := by nlinarith
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg r) he2)

theorem denominator_pos {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    0 < denominator t r := lt_of_lt_of_le zero_lt_one (denominator_ge_one ht r)

@[simp] theorem flow_initial (r : ℝ) : flow 0 r = r := by
  simp [flow, denominator]

theorem flow_pos {t r : ℝ} (ht : 0 ≤ t) (hr : 0 < r) : 0 < flow t r := by
  exact div_pos (mul_pos hr (Real.exp_pos t)) (Real.sqrt_pos.mpr (denominator_pos ht r))

theorem flow_sq {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    (flow t r) ^ 2 = r ^ 2 * (Real.exp t) ^ 2 / denominator t r := by
  simp only [flow, div_pow, mul_pow, Real.sq_sqrt (denominator_pos ht r).le]

/-- Derivative with respect to the positive initial standard deviation. -/
theorem flow_hasDerivAt_initial {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    HasDerivAt (flow t) (Real.exp t / (Real.sqrt (denominator t r)) ^ 3) r := by
  have hD : denominator t r ≠ 0 := (denominator_pos ht r).ne'
  have hs : Real.sqrt (denominator t r) ≠ 0 := (Real.sqrt_pos.mpr (denominator_pos ht r)).ne'
  have hd : HasDerivAt (fun x : ℝ => denominator t x)
      (2 * r * ((Real.exp t) ^ 2 - 1)) r := by
    unfold denominator
    convert (hasDerivAt_const r 1).add (((hasDerivAt_id r).pow 2).mul_const ((Real.exp t)^2 - 1)) using 1
    simp
  have h := ((hasDerivAt_id r).mul_const (Real.exp t)).div (hd.sqrt hD) hs
  convert h using 1
  have hidentity : (Real.sqrt (denominator t r)) ^ 2 -
      r ^ 2 * ((Real.exp t) ^ 2 - 1) = 1 := by
    rw [Real.sq_sqrt (denominator_pos ht r).le]
    unfold denominator
    ring
  dsimp only [id_eq]
  calc
    Real.exp t / (Real.sqrt (denominator t r)) ^ 3 =
        Real.exp t * ((Real.sqrt (denominator t r)) ^ 2 -
          r ^ 2 * ((Real.exp t) ^ 2 - 1)) /
            (Real.sqrt (denominator t r)) ^ 3 := by rw [hidentity]; ring
    _ = _ := by field_simp [hs]

/-- The explicit family solves the scalar moment ODE at every nonnegative time. -/
theorem flow_hasDerivAt_time {t r : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => flow s r) (flow t r * (1 - (flow t r) ^ 2)) t := by
  have hD : denominator t r ≠ 0 := (denominator_pos ht r).ne'
  have hs : Real.sqrt (denominator t r) ≠ 0 := (Real.sqrt_pos.mpr (denominator_pos ht r)).ne'
  have hd : HasDerivAt (fun s : ℝ => denominator s r)
      (r ^ 2 * (2 * (Real.exp t) ^ 2)) t := by
    unfold denominator
    convert (hasDerivAt_const t 1).add ((((Real.hasDerivAt_exp t).pow 2).sub_const 1).const_mul (r^2)) using 1
    dsimp
    ring
  have h := ((Real.hasDerivAt_exp t).const_mul r).div (hd.sqrt hD) hs
  convert h using 1
  dsimp [flow]
  field_simp [hs]

/-- Squaring the standard deviation gives the exact centered covariance equation. -/
theorem covariance_hasDerivAt {t r : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => (flow s r) ^ 2)
      (2 * (flow t r) ^ 2 - 2 * (flow t r) ^ 4) t := by
  convert (flow_hasDerivAt_time (r := r) ht).pow 2 using 1
  ring

/-- The one-dimensional moment vector field (2.3), with actual Gaussian
expectations rather than independently supplied coefficients. -/
noncomputable def gaussianMomentField (V : ℝ → ℝ) (μ σ : ℝ) : ℝ × ℝ :=
  let v := Real.toNNReal σ
  let m := ∫ x : ℝ, deriv V x ∂ProbabilityTheory.gaussianReal μ v
  let Γ := ∫ x : ℝ, deriv (deriv V) x ∂ProbabilityTheory.gaussianReal μ v
  ((1 - Γ * σ) * μ - (1 + μ ^ 2) * m,
    2 * σ - σ * (σ * Γ + μ * m) - (Γ * σ + m * μ) * σ)

noncomputable abbrev scalarMomentField := gaussianMomentField potential

theorem scalarMomentField_centered (σ : ℝ) :
    scalarMomentField 0 σ = (0, 2 * σ - 2 * σ ^ 2) := by
  simp [scalarMomentField, gaussianMomentField, gaussian_mean_gradient, gaussian_mean_hessian]
  ring

/-- The centered curve solves the full scalar mean/covariance moment equation. -/
theorem centered_moment_hasDerivAt {t r : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => ((0 : ℝ), (flow s r) ^ 2))
      (scalarMomentField 0 ((flow t r) ^ 2)) t := by
  rw [scalarMomentField_centered]
  convert (hasDerivAt_const t (0 : ℝ)).prodMk (covariance_hasDerivAt (r := r) ht) using 1
  congr 1
  ring

/-- The inverse squared radius obeys a linear equation. -/
theorem inverse_square_hasDerivAt {f : ℝ → ℝ} {t : ℝ}
    (hf : HasDerivAt f (f t * (1 - (f t) ^ 2)) t) (hp : 0 < f t) :
    HasDerivAt (fun s => ((f s) ^ 2)⁻¹) (2 - 2 * ((f t) ^ 2)⁻¹) t := by
  convert (hf.pow 2).inv (pow_ne_zero 2 hp.ne') using 1
  simp only [Pi.pow_apply]
  field_simp [hp.ne']
  ring

/-- Every positive solution with the prescribed initial value is the explicit flow. -/
theorem positive_solution_unique (f : ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    (hinitial : f 0 = r)
    (hpos : ∀ t, 0 ≤ t → 0 < f t)
    (hode : ∀ t, 0 ≤ t → HasDerivAt f (f t * (1 - (f t) ^ 2)) t)
    {t : ℝ} (ht : 0 ≤ t) : f t = flow t r := by
  have hlinear : ∀ s : ℝ, LipschitzWith (2 : ℝ≥0) (fun x : ℝ => 2 - 2 * x) := by
    intro s
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simp only [Real.dist_eq, NNReal.coe_ofNat]
    rw [show 2 - 2 * x - (2 - 2 * y) = -2 * (x - y) by ring, abs_mul]
    norm_num
  have hf : ∀ s, 0 ≤ s → HasDerivAt (fun u => ((f u) ^ 2)⁻¹)
      (2 - 2 * ((f s) ^ 2)⁻¹) s :=
    fun s hs => inverse_square_hasDerivAt (hode s hs) (hpos s hs)
  have hg : ∀ s, 0 ≤ s → HasDerivAt (fun u => ((flow u r) ^ 2)⁻¹)
      (2 - 2 * ((flow s r) ^ 2)⁻¹) s :=
    fun s hs => inverse_square_hasDerivAt (flow_hasDerivAt_time hs) (flow_pos hs hr)
  have hEq : Set.EqOn (fun u => ((f u) ^ 2)⁻¹)
      (fun u => ((flow u r) ^ 2)⁻¹) (Set.Icc 0 t) := by
    apply ODE_solution_unique (v := fun _ x : ℝ => 2 - 2 * x) hlinear
    · exact fun s hs => (hf s hs.1).continuousAt.continuousWithinAt
    · exact fun s hs => (hf s hs.1).hasDerivWithinAt
    · exact fun s hs => (hg s hs.1).continuousAt.continuousWithinAt
    · exact fun s hs => (hg s hs.1).hasDerivWithinAt
    · simp [hinitial]
  have hsq : (f t) ^ 2 = (flow t r) ^ 2 := inv_injective (hEq ⟨ht, le_rfl⟩)
  exact (sq_eq_sq₀ (hpos t ht).le (flow_pos ht hr).le).mp hsq

/-- The explicit solution has the autonomous flow composition law. -/
theorem flow_semigroup {s t r : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hr : 0 < r) :
    flow (s + t) r = flow s (flow t r) := by
  have hode : ∀ u, 0 ≤ u → HasDerivAt (fun v => flow (t + v) r)
      (flow (t + u) r * (1 - (flow (t + u) r) ^ 2)) u := by
    intro u hu
    simpa using (flow_hasDerivAt_time (r := r) (add_nonneg ht hu)).comp u
      ((hasDerivAt_id u).const_add t)
  have h := positive_solution_unique (fun u => flow (t + u) r) (flow_pos ht hr)
    (by simp) (fun u hu => flow_pos (add_nonneg ht hu) hr) hode hs
  simpa only [add_comm t s] using h

/-- No finite real constant controls all nonnegative-time maps on positive data. -/
theorem no_uniform_lipschitz :
    ¬ ∃ S : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ r q : ℝ, 0 < r → 0 < q →
      |flow t r - flow t q| ≤ S * |r - q| := by
  rintro ⟨S, hS⟩
  have hS1 : 1 ≤ S := by
    have h := hS 0 le_rfl 1 2 (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hS0 : 0 ≤ S := le_trans zero_le_one hS1
  let t : ℝ := 8 * S + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  let E : ℝ := Real.exp t
  have hE : 0 < E := Real.exp_pos t
  let r : ℝ := E⁻¹
  have hr : 0 < r := inv_pos.mpr hE
  have hderiv := flow_hasDerivAt_initial ht r
  have hbound : |E / (Real.sqrt (denominator t r)) ^ 3| ≤ S := by
    apply hderiv.le_of_lip' hS0
    filter_upwards [eventually_gt_nhds hr] with q hq
    simpa only [Real.norm_eq_abs] using hS t ht q r hq hr
  have hDle : denominator t r ≤ 2 := by
    dsimp [denominator, r, E]
    field_simp
    nlinarith [sq_nonneg (Real.exp t)]
  have hs0 : 0 < Real.sqrt (denominator t r) := Real.sqrt_pos.mpr (denominator_pos ht r)
  have hs2 : Real.sqrt (denominator t r) ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · linarith
  have hs3 : (Real.sqrt (denominator t r)) ^ 3 ≤ 8 := by
    nlinarith [sq_nonneg (Real.sqrt (denominator t r) - 2)]
  rw [abs_of_pos (div_pos hE (pow_pos hs0 3))] at hbound
  have hEbound : E ≤ S * (Real.sqrt (denominator t r)) ^ 3 :=
    (div_le_iff₀ (pow_pos hs0 3)).mp hbound
  have hE8 : E ≤ 8 * S := by nlinarith
  have hexp : t + 1 ≤ E := Real.add_one_le_exp t
  dsimp [t] at hexp
  linarith

/-- The witness includes the initial condition, positivity, and the genuine ODE. -/
theorem proposition_8_1_witness :
    ContDiff ℝ ⊤ potential ∧
    StrongConvexOn (Set.univ : Set ℝ) 1 potential ∧
    (∀ x, deriv (deriv potential) x = 1) ∧
    (∀ r, flow 0 r = r) ∧
    (∀ t r, 0 ≤ t → 0 < r → 0 < flow t r) ∧
    (∀ t r, 0 ≤ t → HasDerivAt (fun s => flow s r)
      (flow t r * (1 - (flow t r) ^ 2)) t) ∧
    (¬ ∃ S : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ r q : ℝ, 0 < r → 0 < q →
      |flow t r - flow t q| ≤ S * |r - q|) := by
  exact ⟨potential_smooth, potential_strongly_convex, potential_hessian,
    flow_initial, fun _ _ ht hr => flow_pos ht hr,
    fun _ _ ht => flow_hasDerivAt_time ht, no_uniform_lipschitz⟩

/-- Proposition 8.1, with the potential, positive moment solution, and all time
and initial-data quantifiers made explicit.  The Gaussian expectations in
`gaussianMomentField` are actual integrals. -/
theorem proposition_8_1 :
    ∃ (V : ℝ → ℝ) (φ : ℝ → ℝ → ℝ),
      ContDiff ℝ ⊤ V ∧
      StrongConvexOn (Set.univ : Set ℝ) 1 V ∧
      (∀ x, 1 ≤ deriv (deriv V) x ∧ deriv (deriv V) x ≤ 1) ∧
      (∀ r, 0 < r → φ 0 r = r) ∧
      (∀ t r, 0 ≤ t → 0 < r → 0 < φ t r) ∧
      (∀ t r, 0 ≤ t → HasDerivAt (fun s : ℝ => ((0 : ℝ), (φ s r) ^ 2))
        (gaussianMomentField V 0 ((φ t r) ^ 2)) t) ∧
      (¬ ∃ S : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ r q : ℝ, 0 < r → 0 < q →
        |φ t r - φ t q| ≤ S * |r - q|) := by
  exact ⟨potential, flow, potential_smooth, potential_strongly_convex,
    potential_hessian_bounds, fun r _ => flow_initial r,
    fun _ _ ht hr => flow_pos ht hr,
    fun _ _ ht => centered_moment_hasDerivAt ht, no_uniform_lipschitz⟩

end Paper38.ScalarCounterexample
