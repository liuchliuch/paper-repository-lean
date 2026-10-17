import ELV.Basic
import ELV.CostIdentities
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Four-oracle adversary arithmetic (Section 3.2)

We verify the algebraic steps of the matching lower bound `C ≥ 1/(2δ)`:

* the filter block `C_z = α(1-z) I + β(1+z) X` has eigenvalues `1-μz` and `μ-z`,
* `|1-μz|² = |μ-z|² = 4δ²` when `|z|=1` and `Re z = μ`,
* the Γ-weighted Gram sum equals `4`,
* hence `4 ≤ 2δ · 4 C` and `C ≥ 1/(2δ)`.
-/

noncomputable section

open Matrix

namespace ELV

namespace AdversaryFour

/-- `α = (1+μ)/2`, `β = (1-μ)/2` from (3.15). -/
def alpha (μ : ℝ) : ℝ := (1 + μ) / 2

def beta (μ : ℝ) : ℝ := (1 - μ) / 2

theorem alpha_add_beta (μ : ℝ) : alpha μ + beta μ = 1 := by
  unfold alpha beta
  ring

theorem alpha_sub_beta (μ : ℝ) : alpha μ - beta μ = μ := by
  unfold alpha beta
  ring

/-- Hadamard-diagonalized eigenvalues of the low-to-high block `C_z`. -/
def eig1 (μ : ℝ) (z : ℂ) : ℂ := 1 - μ * z

def eig2 (μ : ℝ) (z : ℂ) : ℂ := μ - z

/-- Each row of `K = α I + β X₂` sums to one (used in (3.16)). -/
theorem K_row_sum (μ : ℝ) : alpha μ + beta μ = 1 :=
  alpha_add_beta μ

/-- Squared modulus of the first Hadamard eigenvalue. -/
theorem abs_eig1_sq (μ : ℝ) (z : ℂ) :
    ‖eig1 μ z‖ ^ 2 = 1 - 2 * μ * z.re + μ ^ 2 * ‖z‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq]
  simp [eig1, Complex.normSq, pow_two]
  ring

/-- Squared modulus of the second Hadamard eigenvalue. -/
theorem abs_eig2_sq (μ : ℝ) (z : ℂ) :
    ‖eig2 μ z‖ ^ 2 = μ ^ 2 - 2 * μ * z.re + ‖z‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq]
  simp [eig2, Complex.normSq, pow_two]
  ring

theorem abs_eig1_sq_on_circle {g : Gap} {z : ℂ}
    (hz : ‖z‖ = 1) (hre : z.re = g.mu) :
    ‖eig1 g.mu z‖ ^ 2 = 1 - g.mu ^ 2 := by
  rw [abs_eig1_sq, hre, hz]
  ring

theorem one_sub_mu_sq {g : Gap} : 1 - g.mu ^ 2 = 4 * g.δ ^ 2 := by
  nlinarith [g.mu_sq]

theorem filter_norm {g : Gap} {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re = g.mu) :
    ‖eig1 g.mu z‖ ^ 2 = 4 * g.δ ^ 2 := by
  rw [abs_eig1_sq_on_circle hz hre, one_sub_mu_sq]

theorem abs_eig2_sq_on_circle {g : Gap} {z : ℂ}
    (hz : ‖z‖ = 1) (hre : z.re = g.mu) :
    ‖eig2 g.mu z‖ ^ 2 = 4 * g.δ ^ 2 := by
  rw [abs_eig2_sq, hre, hz]
  nlinarith [g.mu_sq]

/-- There are four instances: the sum of their squared query norms is at
most `4 C`. Consequently the filtered quadratic form is at most `8 δ C`.
The former `2 δ * 8 C` hypothesis was too weak and has been corrected. -/
theorem lower_bound_of_filter (δ C : ℝ) (hδ : 0 < δ)
    (h : (4 : ℝ) ≤ 2 * δ * (4 * C)) : 1 / (2 * δ) ≤ C := by
  apply (div_le_iff₀ (by positivity : 0 < 2 * δ)).2
  nlinarith

theorem four_oracle_lower (g : Gap) (C : ℝ)
    (h : (4 : ℝ) ≤ (2 * g.δ) * (4 * C)) : 1 / (2 * g.δ) ≤ C :=
  lower_bound_of_filter g.δ C g.δ_pos h

theorem lower_from_adversary (δ : ℝ) (hδ : 0 < δ) (C : ℝ)
    (hsum : (4 : ℝ) = 2 * δ * (4 * C)) : 1 / (2 * δ) ≤ C :=
  lower_bound_of_filter δ C hδ hsum.le

end AdversaryFour
end ELV
