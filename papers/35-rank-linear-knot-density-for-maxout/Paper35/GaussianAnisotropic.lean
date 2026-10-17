import Paper35.GaussianLift
import Paper35.CrossingJacobian
import Paper35.Heterogeneous
import Mathlib.Tactic.FunProp

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace Paper35.GaussianAnisotropic
open Source

def append {d : ℕ} (x : Space d) (b : ℝ) : Space (d+1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) b)

lemma norm_append_sq {d : ℕ} (x : Space d) (b : ℝ) :
    ‖append x b‖^2 = ‖x‖^2+b^2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp [append, Fin.snoc_castSucc, Fin.snoc_last, Real.norm_eq_abs, sq_abs]

lemma inner_append {d : ℕ} (x y : Space d) (a b : ℝ) :
    inner ℝ (append x a) (append y b) = inner ℝ x y+a*b := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_castSucc,
    append, WithLp.ofLp_toLp, star_trivial]
  simp [mul_comm]

def lift {d : ℕ} (A : Space d →L[ℝ] Space d) (σ : ℝ) (x : Space d) : Space (d+1) :=
  append (A x) σ

def velocity {d : ℕ} (A : Space d →L[ℝ] Space d) (v : Space d) : Space (d+1) :=
  append (A v) 0

lemma lift_ne_zero {d : ℕ} (A : Space d →L[ℝ] Space d) {σ : ℝ} (hσ : 0 < σ)
    (x : Space d) : lift A σ x ≠ 0 := by
  intro hz
  have H := norm_append_sq (A x) σ
  change ‖lift A σ x‖^2 = _ at H
  rw [hz, norm_zero, zero_pow (by norm_num)] at H
  nlinarith [sq_nonneg ‖A x‖]

lemma norm_lift_lower {d : ℕ} (A : Space d →L[ℝ] Space d) {σ : ℝ} (hσ : 0 < σ)
    (x : Space d) : σ ≤ ‖lift A σ x‖ := by
  have H := norm_append_sq (A x) σ
  change ‖lift A σ x‖^2 = _ at H
  nlinarith [norm_nonneg (lift A σ x), sq_nonneg ‖A x‖]

lemma norm_velocity {d : ℕ} (A : Space d →L[ℝ] Space d) (v : Space d) :
    ‖velocity A v‖ = ‖A v‖ := by
  have H := norm_append_sq (A v) 0
  change ‖velocity A v‖^2 = _ at H
  nlinarith [norm_nonneg (velocity A v), norm_nonneg (A v)]

/-- The exact pointwise speed-square formula in (6.8), prior to its spectral bound. -/
theorem normalizedVelocity_sq {d : ℕ} (A : Space d →L[ℝ] Space d)
    {σ : ℝ} (hσ : 0 < σ) (x v : Space d) :
    ‖Gaussian.normalizedVelocity (lift A σ x) (velocity A v)‖^2 =
      ‖A v‖^2/(σ^2+‖A x‖^2) - (inner ℝ (A x) (A v))^2/(σ^2+‖A x‖^2)^2 := by
  rw [Gaussian.normalizedVelocity_norm_sq _ _ (lift_ne_zero A hσ x),
    norm_velocity, show inner ℝ (lift A σ x) (velocity A v) = inner ℝ (A x) (A v) by
      simp [lift, velocity, inner_append],
    show ‖lift A σ x‖^2 = σ^2+‖A x‖^2 by
      rw [lift, norm_append_sq, add_comm]]
  rw [show ‖lift A σ x‖^4 = (σ^2+‖A x‖^2)^2 by
    rw [show (4 : ℕ)=2*2 by norm_num, pow_mul, lift, norm_append_sq, add_comm]]

/-- The source local speed estimate, valid also for singular A. -/
theorem normalizedVelocity_le {d : ℕ} (A : Space d →L[ℝ] Space d)
    {σ : ℝ} (hσ : 0 < σ) (x v : Space d) :
    ‖Gaussian.normalizedVelocity (lift A σ x) (velocity A v)‖ ≤ ‖A‖/σ*‖v‖ := by
  calc
    _ ≤ ‖velocity A v‖/‖lift A σ x‖ :=
      Gaussian.normalizedVelocity_norm_le _ _ (lift_ne_zero A hσ x)
    _ ≤ (‖A‖*‖v‖)/σ := by
      rw [norm_velocity]
      exact div_le_div₀ (by positivity) (A.le_opNorm v) hσ (norm_lift_lower A hσ x)
    _ = _ := by ring

/-- The horizontal inclusion is a genuine continuous linear map. -/
def horizontal {d : ℕ} : Space d →L[ℝ] Space (d+1) :=
  (show Space d →ₗ[ℝ] Space (d+1) from
    { toFun := fun x => append x 0
      map_add' := by
        intro x y
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;>
          simp [append, Fin.snoc_last, Fin.snoc_castSucc]
      map_smul' := by
        intro c x
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;>
          simp [append, Fin.snoc_last, Fin.snoc_castSucc] }).toContinuousLinearMap

lemma append_eq_horizontal {d : ℕ} (x : Space d) (b : ℝ) :
    append x b = horizontal x + b • append (0 : Space d) 1 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [append, horizontal, Fin.snoc_last, Fin.snoc_castSucc]

lemma lift_eq_horizontal {d : ℕ} (A : Space d →L[ℝ] Space d)
    (σ : ℝ) (x : Space d) :
    lift A σ x = (horizontal.comp A) x + σ • append (0 : Space d) 1 :=
  append_eq_horizontal _ _

lemma continuous_lift {d : ℕ} (A : Space d →L[ℝ] Space d) (σ : ℝ) :
    Continuous (lift A σ) := by
  change Continuous (fun x => lift A σ x)
  simp_rw [lift_eq_horizontal]
  exact (horizontal.comp A).continuous.add continuous_const

lemma hasDerivAt_lift {d : ℕ} (A : Space d →L[ℝ] Space d) (σ : ℝ)
    {f : ℝ → Space d} {v : Space d} {s : ℝ} (hf : HasDerivAt f v s) :
    HasDerivAt (fun t => lift A σ (f t)) (velocity A v) s := by
  simp_rw [lift_eq_horizontal]
  simpa only [velocity, horizontal, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
    using ((horizontal.comp A).hasFDerivAt.comp_hasDerivAt s hf).add_const
      (σ • append (0 : Space d) 1)

end Paper35.GaussianAnisotropic
