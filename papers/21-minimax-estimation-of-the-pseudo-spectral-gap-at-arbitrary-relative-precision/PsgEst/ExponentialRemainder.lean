import PsgEst.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Scalar Bernstein exponential remainder, proved directly by differentiation. -/
open Real Set
namespace PsgEst

private noncomputable def bernsteinAux (x : ℝ) : ℝ :=
  ((x^2+4*x+6)/(6-2*x))*exp (-x)

private theorem bernsteinAux_deriv (x : ℝ) (hx : x < 3) :
    HasDerivAt bernsteinAux (x^3*exp (-x)/(2*(3-x)^2)) x := by
  have hn := (((hasDerivAt_id x).pow 2).add
    ((hasDerivAt_id x).const_mul 4)).add_const 6
  have hd := (hasDerivAt_const x (6:ℝ)).sub ((hasDerivAt_id x).const_mul 2)
  have he := ((hasDerivAt_id x).neg).exp
  have hne : (6:ℝ)-2*x ≠ 0 := by linarith
  convert (hn.div hd hne).mul he using 1 <;> dsimp [bernsteinAux]
  rw [show (6:ℝ)-2*x = 2*(3-x) by ring]
  field_simp [show (3:ℝ)-x ≠ 0 by linarith]
  <;> ring

private theorem one_le_bernsteinAux (x : ℝ) (hx : x < 3) :
    1 ≤ bernsteinAux x := by
  by_cases hpos : 0 ≤ x
  · have hcont : ContinuousOn bernsteinAux (Icc 0 x) := by
      intro y hy
      exact (bernsteinAux_deriv y (by linarith [hy.2])).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ bernsteinAux (interior (Icc 0 x)) := by
      intro y hy
      have hy' := interior_subset hy
      exact (bernsteinAux_deriv y (by linarith [hy'.2])).differentiableAt.differentiableWithinAt
    have hmono := monotoneOn_of_deriv_nonneg (convex_Icc 0 x) hcont hdiff
      (by
        intro y hy
        have hy' := interior_subset hy
        rw [(bernsteinAux_deriv y (by linarith [hy'.2])).deriv]
        exact div_nonneg (mul_nonneg (pow_nonneg hy'.1 3) (exp_nonneg _))
          (by positivity))
    have h := hmono (show (0:ℝ) ∈ Icc 0 x from ⟨le_rfl,hpos⟩)
      (show x ∈ Icc 0 x from ⟨hpos,le_rfl⟩) hpos
    simpa [bernsteinAux] using h
  · have hx0 : x ≤ 0 := le_of_not_ge hpos
    have hcont : ContinuousOn bernsteinAux (Icc x 0) := by
      intro y hy
      exact (bernsteinAux_deriv y (by linarith [hy.2])).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ bernsteinAux (interior (Icc x 0)) := by
      intro y hy
      have hy' := interior_subset hy
      exact (bernsteinAux_deriv y (by linarith [hy'.2])).differentiableAt.differentiableWithinAt
    have hanti := antitoneOn_of_deriv_nonpos (convex_Icc x 0) hcont hdiff
      (by
        intro y hy
        have hy' := interior_subset hy
        rw [(bernsteinAux_deriv y (by linarith [hy'.2])).deriv]
        apply div_nonpos_of_nonpos_of_nonneg
        · apply mul_nonpos_of_nonpos_of_nonneg _ (exp_nonneg _)
          have ht := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) hy'.2
          nlinarith
        · positivity)
    have h := hanti (show x ∈ Icc x 0 from ⟨le_rfl,hx0⟩)
      (show (0:ℝ) ∈ Icc x 0 from ⟨hx0,le_rfl⟩) hx0
    simpa [bernsteinAux] using h

/-- The scalar inequality underlying Bernstein/Freedman. It holds for every
`x < 3`, including all negative values. No probability bound is assumed. -/
theorem exp_le_one_add_add_sq (x : ℝ) (hx : x < 3) :
    exp x ≤ 1+x+x^2/(2*(1-x/3)) := by
  have h := mul_le_mul_of_nonneg_right (one_le_bernsteinAux x hx) (exp_nonneg x)
  have heq : bernsteinAux x * exp x = (x^2+4*x+6)/(6-2*x) := by
    unfold bernsteinAux
    rw [mul_assoc, ← exp_add]
    simp
  rw [heq, one_mul] at h
  have heq' : (x^2+4*x+6)/(6-2*x) = 1+x+x^2/(2*(1-x/3)) := by
    rw [show (6:ℝ)-2*x = 2*(3-x) by ring,
      show 2*(1-x/3) = 2*(3-x)/3 by ring]
    field_simp [show (3:ℝ)-x ≠ 0 by linarith]
    <;> ring
  exact h.trans_eq heq'

/-- Uniform remainder bound on a one-sided bounded interval. -/
theorem exp_le_one_add_add_sq_uniform (x c : ℝ) (hxc : x ≤ c) (hc : c < 3) :
    exp x ≤ 1+x+x^2/(2*(1-c/3)) := by
  refine (exp_le_one_add_add_sq x (hxc.trans_lt hc)).trans ?_
  gcongr
  linarith

/-- The conditional-mgf pointwise bound for a scalar increment `z ≤ R`. -/
theorem exp_mul_le_one_add_add_sq (θ R z : ℝ) (hθ : 0 ≤ θ)
    (hθR : θ*R < 3) (hz : z ≤ R) :
    exp (θ*z) ≤ 1+θ*z+θ^2*z^2/(2*(1-θ*R/3)) := by
  have h := exp_le_one_add_add_sq_uniform (θ*z) (θ*R)
    (mul_le_mul_of_nonneg_left hz hθ) hθR
  convert h using 1 <;> ring

end PsgEst
