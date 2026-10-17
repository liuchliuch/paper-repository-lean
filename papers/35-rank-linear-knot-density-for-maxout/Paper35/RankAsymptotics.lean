import Paper35.Rank
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring

noncomputable section
open Filter
open scoped Topology
namespace Paper35.RankAsymptotics

/-- The usual second-order approximation to the expected Gaussian maximum. -/
def meanMain (K : ℕ) : ℝ :=
  Real.sqrt (2 * Real.log K) -
    (Real.log (Real.log K) + Real.log (4 * Real.pi) -
      2 * Real.eulerMascheroniConstant) / (2 * Real.sqrt (2 * Real.log K))

/-- The expression printed on the right side of the source equation (7.2),
without its little-o remainder. -/
def coefficientMain (K : ℕ) : ℝ :=
  Real.sqrt (2 * Real.log K / Real.pi) -
    (Real.log (Real.log K) + Real.log (4 * Real.pi) -
      2 * Real.eulerMascheroniConstant) / (2 * Real.sqrt (2 * Real.pi * Real.log K))

/-- Explicit published classical extreme-value input about the actual mean of
an iid standard-normal maximum. The first component is the leading mean
asymptotic. The second is the standard second-order mean expansion, expressed
as a scaled remainder limit (equivalent to little-o of (log K)^(-1/2)).

Sources: Kabluchko--Zaporozhets, arXiv:1706.08092, Section 1.3, equations (9),
(11) and the displayed expected maximum expansion immediately following (11),
pp. 3--4. The latter includes expectation convergence, not only weak Gumbel
convergence. This input has no switch, path, visibility, network or c_K claim.
The actual c_K consequences and their normalization are proved below. -/
def GaussianExtremeMeanLaw : Prop :=
  Tendsto (fun K : ℕ => gaussianMaxMean K / Real.sqrt (2 * Real.log K))
    atTop (𝓝 1) ∧
  Tendsto (fun K : ℕ => Real.sqrt (Real.log K) *
    (gaussianMaxMean K - meanMain K)) atTop (𝓝 0)

lemma sqrt_pi_mul_scale (K : ℕ) :
    Real.sqrt (2 * Real.pi * Real.log K) =
      Real.sqrt Real.pi * Real.sqrt (2 * Real.log K) := by
  rw [← Real.sqrt_mul Real.pi_pos.le]
  congr 1
  ring

lemma coefficientMain_eq_meanMain_div (K : ℕ) :
    coefficientMain K = meanMain K / Real.sqrt Real.pi := by
  unfold coefficientMain meanMain
  rw [Real.sqrt_div (mul_nonneg (by norm_num) (Real.log_natCast_nonneg K)), sqrt_pi_mul_scale]
  simp only [div_eq_mul_inv, sub_mul, mul_inv_rev]
  ring

/-- Source (7.2): the actual Gaussian rank coefficient has the stated
second-order asymptotic. This theorem records the little-o claim as the
corresponding remainder limit and proves all conversion from m_K to c_K. -/
theorem gaussianRankCoefficient_second_order (hext : GaussianExtremeMeanLaw) :
    Tendsto (fun K : ℕ => Real.sqrt (Real.log K) *
      (gaussianRankCoefficient K - coefficientMain K)) atTop (𝓝 0) := by
  have H := hext.2.div_const (Real.sqrt Real.pi)
  simp only [zero_div] at H
  convert H using 1
  ext K
  rw [coefficientMain_eq_meanMain_div, gaussianRankCoefficient, ← sub_div]
  ring

/-- Source (2.23), in the ordinary ratio definition of asymptotic equivalence. -/
theorem gaussianRankCoefficient_leading (hext : GaussianExtremeMeanLaw) :
    Tendsto (fun K : ℕ => gaussianRankCoefficient K /
      Real.sqrt (2 * Real.log K / Real.pi)) atTop (𝓝 1) := by
  convert hext.1 using 1
  ext K
  rw [gaussianRankCoefficient, Real.sqrt_div (mul_nonneg (by norm_num) (Real.log_natCast_nonneg K))]
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  rw [mul_assoc, ← mul_assoc (Real.sqrt Real.pi)⁻¹,
    inv_mul_cancel₀ hp, one_mul]

end Paper35.RankAsymptotics
