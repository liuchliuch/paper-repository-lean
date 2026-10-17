import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith

/-! The stationarity and Hölder-transfer argument in (4.4)--(4.7).
The derivative takes values in the continuous dual of the displayed primal
normed space, so its norm is exactly the dual target norm. This file is an
outer-analysis component; it does not assert existence of an oracle solver. -/

open scoped BigOperators

namespace P31

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fermat stationarity for the actual accumulated objective. -/
theorem accumulated_stationarity {ι : Type*} (s : Finset ι)
    (f : E → ℝ) (atom : ι → E → ℝ) (α : ι → ℝ)
    (z : E) (df : E →L[ℝ] ℝ) (da : ι → E →L[ℝ] ℝ)
    (hf : HasFDerivAt f df z)
    (ha : ∀ i ∈ s, HasFDerivAt (atom i) (da i) z)
    (hmin : ∀ y, f z + ∑ i ∈ s, α i * atom i z ≤
      f y + ∑ i ∈ s, α i * atom i y) :
    df = -(∑ i ∈ s, α i • da i) := by
  have hd : HasFDerivAt (fun y => f y + ∑ i ∈ s, α i * atom i y)
      (df + ∑ i ∈ s, α i • da i) z := by
    apply hf.add
    exact HasFDerivAt.fun_sum fun i hi => (ha i hi).const_mul (α i)
  have hm : IsLocalMin (fun y => f y + ∑ i ∈ s, α i * atom i y) z :=
    Filter.Eventually.of_forall hmin
  exact eq_neg_of_add_eq_zero_left (hm.hasFDerivAt_eq_zero hd)

/-- Triangle inequality and the true nonnegative accumulation weights convert
stationarity to the weighted sum of the historical atom derivatives. -/
theorem accumulated_derivative_bound {ι : Type*} (s : Finset ι)
    (α : ι → ℝ) (df : E →L[ℝ] ℝ) (da : ι → E →L[ℝ] ℝ)
    (b : ι → ℝ) (hα : ∀ i ∈ s, 0 ≤ α i)
    (hstationary : df = -(∑ i ∈ s, α i • da i))
    (hbound : ∀ i ∈ s, ‖da i‖ ≤ b i) :
    ‖df‖ ≤ ∑ i ∈ s, α i * b i := by
  rw [hstationary, norm_neg]
  calc
    ‖∑ i ∈ s, α i • da i‖ ≤ ∑ i ∈ s, ‖α i • da i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, α i * b i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hα i hi)]
      exact mul_le_mul_of_nonneg_left (hbound i hi) (hα i hi)

/-- General version of the transfer in (4.7), with a genuine Hölder condition
on the derivative and the computed-to-exact minimizer distance. -/
theorem holder_terminal_transfer (grad : E → E →L[ℝ] ℝ)
    (x z : E) (L δ ε t : ℝ) (hL : 0 ≤ L) (ht : 0 ≤ t)
    (hholder : ∀ u v, ‖grad u - grad v‖ ≤ L * ‖u-v‖ ^ t)
    (hdist : ‖x-z‖ ≤ δ) (hbias : ‖grad z‖ ≤ ε / 2)
    (hscale : L * δ ^ t ≤ ε / 2) :
    ‖grad x‖ ≤ ε := by
  have htransfer : ‖grad x - grad z‖ ≤ ε / 2 := calc
    ‖grad x - grad z‖ ≤ L * ‖x-z‖ ^ t := hholder x z
    _ ≤ L * δ ^ t := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hdist ht) hL
    _ ≤ ε / 2 := hscale
  have htriangle : ‖grad x‖ ≤ ‖grad x - grad z‖ + ‖grad z‖ :=
    norm_le_norm_sub_add _ _
  linarith

/-- The zero-query regime in Section 3, in the norm and its continuous dual. -/
theorem zero_query_gradient_bound (grad : E → E →L[ℝ] ℝ)
    (x₀ xstar : E) (L R ε t : ℝ) (hL : 0 ≤ L) (ht : 0 ≤ t)
    (hholder : ∀ u v, ‖grad u - grad v‖ ≤ L * ‖u-v‖ ^ t)
    (hstar : grad xstar = 0) (hradius : ‖x₀-xstar‖ ≤ R)
    (heps : L * R ^ t ≤ ε) : ‖grad x₀‖ ≤ ε := by
  have h := hholder x₀ xstar
  rw [hstar, sub_zero] at h
  exact le_trans h (le_trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (norm_nonneg _) hradius ht) hL) heps)

/-- At a supplied genuine minimizer, differentiability supplies the zero
continuous-dual gradient used by the zero-query branch. -/
theorem derivative_zero_at_minimizer (f : E → ℝ) (xstar : E)
    (df : E →L[ℝ] ℝ) (hf : HasFDerivAt f df xstar)
    (hmin : ∀ x, f xstar ≤ f x) : df = 0 := by
  have hm : IsLocalMin f xstar := Filter.Eventually.of_forall hmin
  exact hm.hasFDerivAt_eq_zero hf

end P31
