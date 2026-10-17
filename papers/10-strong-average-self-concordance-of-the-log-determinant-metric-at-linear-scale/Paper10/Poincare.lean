import Paper10.HermiteMoments
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Paper10

/-- Integration of the square of a finite orthogonal expansion. -/
theorem finite_orthogonal_square {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I]
    (μ : Measure Ω) (s : Finset I) (a : I → ℝ) (f : I → Ω → ℝ) (w : I → ℝ)
    (hi : ∀ α β, Integrable (fun ω => f α ω * f β ω) μ)
    (ho : ∀ α β, (∫ ω, f α ω * f β ω ∂μ) = if α = β then w α else 0) :
    (∫ ω, (∑ α ∈ s, a α * f α ω) ^ 2 ∂μ) = ∑ α ∈ s, a α ^ 2 * w α := by
  have he : ∀ ω, (∑ α ∈ s, a α * f α ω) ^ 2 =
      ∑ α ∈ s, ∑ β ∈ s, (a α * a β) * (f α ω * f β ω) := by
    intro ω
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro α hα
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β hβ
    ring
  simp_rw [he]
  rw [integral_finset_sum _ (fun α _ => integrable_finset_sum _
    (fun β _ => (hi α β).const_mul _))]
  simp_rw [integral_finset_sum _ (fun β _ => (hi _ β).const_mul _), integral_const_mul, ho]
  apply Finset.sum_congr rfl
  intro α hα
  simp [Finset.sum_ite_eq, hα, pow_two]

namespace Hermite
variable {m : ℕ}

/-- The actual coordinate gradient, defined by differentiation along coordinate lines. -/
def coordinateDerivative (f : (Fin m → ℝ) → ℝ) (ω : Fin m → ℝ) (i : Fin m) : ℝ :=
  deriv (fun t : ℝ => f (Function.update ω i t)) (ω i)

theorem partial_expansion (s : Finset (Fin m → ℕ)) (a : (Fin m → ℕ) → ℝ)
    (ω : Fin m → ℝ) (i : Fin m) :
    coordinateDerivative (fun ω => ∑ α ∈ s, a α * multi α ω) ω i = ∑ α ∈ s, a α * dMulti i α ω := by
  have hh := HasDerivAt.fun_sum (u := s) (fun α _ => (hasDerivAt_multi α i ω).const_mul (a α))
  exact hh.deriv

theorem integrable_expansion (s : Finset (Fin m → ℕ)) (a : (Fin m → ℕ) → ℝ) :
    Integrable (fun ω => ∑ α ∈ s, a α * multi α ω) (stdGaussianMeasure m) :=
  integrable_finset_sum _ (fun α _ => (integrable_multi α).const_mul _)

theorem expansion_mean (s : Finset (Fin m → ℕ)) (a : (Fin m → ℕ) → ℝ) :
    (∫ ω, (∑ α ∈ s, a α * multi α ω) ∂stdGaussianMeasure m) =
      if (0 : Fin m → ℕ) ∈ s then a 0 else 0 := by
  classical
  rw [integral_finset_sum _ (fun α _ => (integrable_multi α).const_mul _)]
  simp_rw [integral_const_mul, multi_integral]
  simp

/-- Centering deletes precisely the constant Hermite coefficient. -/
theorem expansion_centered (s : Finset (Fin m → ℕ)) (a : (Fin m → ℕ) → ℝ) (ω : Fin m → ℝ) :
    (∑ α ∈ s, a α * multi α ω) - (∫ η, (∑ α ∈ s, a α * multi α η) ∂stdGaussianMeasure m) =
      ∑ α ∈ s, (if α = 0 then 0 else a α) * multi α ω := by
  classical
  rw [expansion_mean]
  have he : ∑ α ∈ s, (if α = 0 then a α * multi α ω else 0) =
      if (0 : Fin m → ℕ) ∈ s then a 0 else 0 := by simp
  rw [← he, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro α hα
  by_cases hα0 : α = 0 <;> simp [hα0]

/-- Exact variance identity in Appendix A.1, obtained from actual Gaussian integrals. -/
theorem expansion_variance (s : Finset (Fin m → ℕ)) (a : (Fin m → ℕ) → ℝ) :
    Var[fun ω => ∑ α ∈ s, a α * multi α ω; stdGaussianMeasure m] =
      ∑ α ∈ s, if α = 0 then 0 else a α ^ 2 * factorial α := by
  classical
  rw [variance_eq_integral (integrable_expansion s a).aemeasurable]
  simp_rw [expansion_centered]
  rw [finite_orthogonal_square _ s _ multi factorial integrable_multi_mul multi_orthogonal]
  apply Finset.sum_congr rfl
  intro α hα
  by_cases hh : α = 0 <;> simp [hh]

/-- Exact gradient-energy identity in Appendix A.1. -/
theorem expansion_energy (s : Finset (Fin m → ℕ)) (a : (Fin m → ℕ) → ℝ) :
    (∫ ω, ∑ i, (coordinateDerivative (fun η => ∑ α ∈ s, a α * multi α η) ω i) ^ 2 ∂stdGaussianMeasure m) =
      ∑ α ∈ s, (order α : ℝ) * a α ^ 2 * factorial α := by
  classical
  simp_rw [partial_expansion]
  have hi (i : Fin m) : Integrable (fun ω => (∑ α ∈ s, a α * dMulti i α ω) ^ 2) (stdGaussianMeasure m) := by
    have he : ∀ ω, (∑ α ∈ s, a α * dMulti i α ω) ^ 2 =
        ∑ α ∈ s, ∑ β ∈ s, (a α * a β) * (dMulti i α ω * dMulti i β ω) := by
      intro ω
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro α hα
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro β hβ
      ring
    simp_rw [he]
    exact integrable_finset_sum _ (fun α _ => integrable_finset_sum _
      (fun β _ => (integrable_dMulti_mul i α β).const_mul _))
  rw [integral_finset_sum _ (fun i _ => hi i)]
  simp_rw [finite_orthogonal_square _ s _ (dMulti _) _ (integrable_dMulti_mul _) (dMulti_orthogonal _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α hα
  simp only [order, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- General polynomial Gaussian Poincaré inequality (Appendix A.1).
The gradient consists of actual derivatives and the polynomial is arbitrary in any finite dimension. -/
theorem gaussian_poincare_poly (p : MvPolynomial (Fin m) ℝ) :
    Var[fun ω => MvPolynomial.eval ω p; stdGaussianMeasure m] ≤
      ∫ ω, ∑ i, (coordinateDerivative (fun η => MvPolynomial.eval η p) ω i) ^ 2 ∂stdGaussianMeasure m := by
  classical
  obtain ⟨s, a, he⟩ := finite_expansion p
  have hf : (fun ω => MvPolynomial.eval ω p) = fun ω => ∑ α ∈ s, a α * multi α ω := funext he
  rw [hf, expansion_variance, expansion_energy]
  apply Finset.sum_le_sum
  intro α hα
  by_cases hα0 : α = 0
  · simp [hα0, order]
  · rw [if_neg hα0]
    have ho : 1 ≤ order α := by
      obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
        by_contra hh
        push_neg at hh
        exact hα0 (funext hh)
      have hle := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => Nat.zero_le (α j))
        (Finset.mem_univ i)
      unfold order
      omega
    have hor : (1 : ℝ) ≤ order α := by exact_mod_cast ho
    have hn : 0 ≤ a α ^ 2 * factorial α := mul_nonneg (sq_nonneg _) (factorial_nonneg α)
    nlinarith

end Hermite
end Paper10
