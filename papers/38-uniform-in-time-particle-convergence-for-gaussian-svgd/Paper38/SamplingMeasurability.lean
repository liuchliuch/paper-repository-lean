import Paper38.Sampling
import Mathlib.Tactic.FunProp

/-! Elementary measurability of the raw Gaussian sample defect. -/
noncomputable section
namespace Paper38.Sampling
open Model MeasureTheory
open scoped BigOperators

lemma defect_measurable (d N : ℕ) : Measurable (defect d N) := by
  have hx (i : Fin N) : Measurable (fun ω : Sample d N => cloud d N ω i) :=
    (GaussianCoupling.continuous_vec (d := d)).measurable.comp
      (measurable_pi_lambda _ fun j => measurable_pi_apply (i,j))
  have hm : Measurable (mean d N) :=
    (Finset.measurable_sum Finset.univ (fun i _ => hx i)).const_smul (N : ℝ)⁻¹
  have hcoord (j : Fin d) : Measurable (fun v : E d => v j) :=
    ((continuous_apply j).comp (EuclideanSpace.equiv (Fin d) ℝ).continuous).measurable
  have hc (j k : Fin d) : Measurable (fun ω : Sample d N => covariance d N ω j k) := by
    simp only [covariance, empiricalCovariance, Matrix.smul_apply, Matrix.sum_apply,
      outer, Matrix.vecMulVec_apply, PiLp.sub_apply, smul_eq_mul]
    change Measurable (fun ω => (N : ℝ)⁻¹ * ∑ i : Fin N,
      ((cloud d N ω i) j - (mean d N ω) j)*((cloud d N ω i) k - (mean d N ω) k))
    exact (Finset.measurable_sum Finset.univ (fun i _ =>
      ((hcoord j).comp (hx i) |>.sub ((hcoord j).comp hm)).mul
        ((hcoord k).comp (hx i) |>.sub ((hcoord k).comp hm)))).const_mul _
  have hf : Measurable (fun ω : Sample d N => frobSq (1-covariance d N ω)) := by
    unfold frobSq
    exact Finset.measurable_sum Finset.univ (fun j _ =>
      Finset.measurable_sum Finset.univ (fun k _ =>
        ((measurable_const.sub (hc j k)).pow_const 2)))
  exact hf.add (hm.norm.pow_const 2)


end Paper38.Sampling
