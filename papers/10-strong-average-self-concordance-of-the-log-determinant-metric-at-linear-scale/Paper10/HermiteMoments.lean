import Paper10.HermiteExpansion
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open Polynomial MeasureTheory ProbabilityTheory
namespace Paper10.Hermite
variable {m : ℕ}

/-- Integrability of arbitrary tensor products of one-variable polynomials. -/
theorem integrable_tensor (p : Fin m → Polynomial ℝ) :
    Integrable (fun ω : Fin m → ℝ => ∏ i, (p i).eval (ω i)) (stdGaussianMeasure m) :=
  Integrable.fintype_prod (fun i => integrable_eval (p i))

theorem integrable_multi (α : Fin m → ℕ) : Integrable (multi α) (stdGaussianMeasure m) :=
  integrable_tensor (fun i => hp (α i))

theorem integrable_multi_mul (α β : Fin m → ℕ) :
    Integrable (fun ω => multi α ω * multi β ω) (stdGaussianMeasure m) := by
  simpa only [multi, ← Finset.prod_mul_distrib, ← Polynomial.eval_mul] using
    integrable_tensor (fun i => hp (α i) * hp (β i))

theorem multi_integral (α : Fin m → ℕ) :
    (∫ ω, multi α ω ∂stdGaussianMeasure m) = if α = 0 then 1 else 0 := by
  classical
  unfold multi stdGaussianMeasure
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => (hp (α i)).eval x)]
  simp_rw [hp_integral]
  by_cases hα : α = 0
  · simp [hα]
  · rw [if_neg hα]
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra hh
      push_neg at hh
      exact hα (funext hh)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Tensor Hermite orthogonality and exact multi-index factorial. -/
theorem multi_orthogonal (α β : Fin m → ℕ) :
    (∫ ω, multi α ω * multi β ω ∂stdGaussianMeasure m) = if α = β then factorial α else 0 := by
  classical
  simp only [multi, ← Finset.prod_mul_distrib, stdGaussianMeasure]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => (hp (α i)).eval x * (hp (β i)).eval x)]
  simp_rw [orthogonal]
  by_cases hαβ : α = β
  · simp [hαβ, factorial]
  · rw [if_neg hαβ]
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
      by_contra hh
      push_neg at hh
      exact hαβ (funext hh)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem integrable_dMulti_mul (i : Fin m) (α β : Fin m → ℕ) :
    Integrable (fun ω => dMulti i α ω * dMulti i β ω) (stdGaussianMeasure m) := by
  simpa only [dMulti, ← Finset.prod_mul_distrib, ← Polynomial.eval_mul] using
    integrable_tensor (fun j =>
      (if j = i then (hp (α j)).derivative else hp (α j)) *
      (if j = i then (hp (β j)).derivative else hp (β j)))

/-- The derivative energy is diagonal in the tensor Hermite basis. -/
theorem dMulti_orthogonal (i : Fin m) (α β : Fin m → ℕ) :
    (∫ ω, dMulti i α ω * dMulti i β ω ∂stdGaussianMeasure m) =
      if α = β then (α i : ℝ) * factorial α else 0 := by
  classical
  simp only [dMulti, ← Finset.prod_mul_distrib, stdGaussianMeasure]
  rw [integral_fintype_prod_eq_prod (fun j (x : ℝ) =>
    (if j = i then (hp (α j)).derivative else hp (α j)).eval x *
    (if j = i then (hp (β j)).derivative else hp (β j)).eval x)]
  have he : ∀ j, (∫ x, (if j = i then (hp (α j)).derivative else hp (α j)).eval x *
      (if j = i then (hp (β j)).derivative else hp (β j)).eval x ∂gaussianReal 0 1) =
      if α j = β j then (if j = i then (α j : ℝ) else 1) * (α j).factorial else 0 := by
    intro j
    by_cases hj : j = i
    · simp only [if_pos hj, derivative_orthogonal]
    · simp only [if_neg hj, orthogonal, one_mul]
  simp_rw [he]
  by_cases hαβ : α = β
  · subst β
    simp only [ite_true]
    rw [Finset.prod_mul_distrib]
    have hh : (∏ j : Fin m, if j = i then (α j : ℝ) else 1) = (α i : ℝ) := by simp
    rw [hh]
    rfl
  · rw [if_neg hαβ]
    obtain ⟨j, hj⟩ : ∃ j, α j ≠ β j := by
      by_contra hh
      push_neg at hh
      exact hαβ (funext hh)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

/-- Actual one-variable derivative of a tensor along a coordinate line. -/
theorem hasDerivAt_multi (α : Fin m → ℕ) (i : Fin m) (ω : Fin m → ℝ) :
    HasDerivAt (fun t : ℝ => multi α (Function.update ω i t)) (dMulti i α ω) (ω i) := by
  classical
  have he : (fun t : ℝ => multi α (Function.update ω i t)) =
      fun t => (hp (α i)).eval t * ∏ j ∈ Finset.univ.erase i, (hp (α j)).eval (ω j) := by
    funext t
    rw [multi_split α i, Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he]
  have hd := ((hp (α i)).hasDerivAt (ω i)).mul_const
    (∏ j ∈ Finset.univ.erase i, (hp (α j)).eval (ω j))
  convert hd using 1
  unfold dMulti
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [if_neg (Finset.ne_of_mem_erase hj)]

end Paper10.Hermite
