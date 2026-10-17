import Paper10.Hermite
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section
open Polynomial MeasureTheory ProbabilityTheory
namespace Paper10.Hermite
variable {m : ℕ}

/-- Tensor products of the actual univariate Hermite polynomials. -/
def multi (α : Fin m → ℕ) (ω : Fin m → ℝ) : ℝ := ∏ i, (hp (α i)).eval (ω i)

/-- Coordinate partial derivative of a Hermite tensor. -/
def dMulti (i : Fin m) (α : Fin m → ℕ) (ω : Fin m → ℝ) : ℝ :=
  ∏ j, (if j = i then (hp (α j)).derivative else hp (α j)).eval (ω j)

/-- Multi-index factorial. -/
def factorial (α : Fin m → ℕ) : ℝ := ∏ i, (α i).factorial

/-- Total degree of a multi-index. -/
def order (α : Fin m → ℕ) : ℕ := ∑ i, α i

@[simp] theorem multi_zero (ω : Fin m → ℝ) : multi 0 ω = 1 := by simp [multi]
@[simp] theorem factorial_zero : factorial (0 : Fin m → ℕ) = 1 := by simp [factorial]

theorem factorial_nonneg (α : Fin m → ℕ) : 0 ≤ factorial α := by unfold factorial; positivity

theorem multi_split (α : Fin m → ℕ) (i : Fin m) (ω : Fin m → ℝ) :
    multi α ω = (hp (α i)).eval (ω i) * ∏ j ∈ Finset.univ.erase i, (hp (α j)).eval (ω j) := by
  classical
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

theorem multi_update (α : Fin m → ℕ) (i : Fin m) (k : ℕ) (ω : Fin m → ℝ) :
    multi (Function.update α i k) ω = (hp k).eval (ω i) *
      ∏ j ∈ Finset.univ.erase i, (hp (α j)).eval (ω j) := by
  classical
  rw [multi_split _ i, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- Multiplying by a coordinate raises or lowers the corresponding Hermite index. -/
theorem coordinate_mul (α : Fin m → ℕ) (i : Fin m) (ω : Fin m → ℝ) :
    ω i * multi α ω = multi (Function.update α i (α i + 1)) ω +
      (α i : ℝ) * multi (Function.update α i (α i - 1)) ω := by
  rw [multi_split α i, multi_update, multi_update]
  have hh : ω i * (hp (α i)).eval (ω i) = (hp (α i + 1)).eval (ω i) +
      (α i : ℝ) * (hp (α i - 1)).eval (ω i) := by
    rw [hp_succ, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
      hp_derivative_all, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  rw [← mul_assoc, hh]
  ring

/-- The finite Hermite span contains every actual multivariate polynomial function. -/
theorem eval_mem_span (p : MvPolynomial (Fin m) ℝ) :
    (fun ω => MvPolynomial.eval ω p) ∈ Submodule.span ℝ (Set.range (multi (m := m))) := by
  let S := Submodule.span ℝ (Set.range (multi (m := m)))
  have hc (i : Fin m) (f : (Fin m → ℝ) → ℝ) (hf : f ∈ S) :
      (fun ω => f ω * ω i) ∈ S := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨α, rfl⟩ := hf
      have hu : multi (Function.update α i (α i + 1)) ∈ S := Submodule.subset_span ⟨_, rfl⟩
      have hl := Submodule.smul_mem S (α i : ℝ)
        (show multi (Function.update α i (α i - 1)) ∈ S from Submodule.subset_span ⟨_, rfl⟩)
      convert Submodule.add_mem S hu hl using 1
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm]
      exact coordinate_mul α i ω
    | zero =>
      convert S.zero_mem using 1
      funext ω
      simp
    | add f g hf hg ihf ihg =>
      convert S.add_mem ihf ihg using 1
      funext ω
      simp only [Pi.add_apply]
      ring
    | smul a f hf ih =>
      convert S.smul_mem a ih using 1
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hh := S.smul_mem a (show multi (0 : Fin m → ℕ) ∈ S from Submodule.subset_span ⟨_, rfl⟩)
    convert hh using 1
    funext ω
    simp [multi, Pi.smul_apply, smul_eq_mul]
  | add p q hp hq => simpa only [map_add, Pi.add_apply] using S.add_mem hp hq
  | mul_X p i hp => simpa only [map_mul, MvPolynomial.eval_X] using hc i _ hp

/-- Every polynomial has a finite Hermite expansion, with no expansion supplied as an assumption. -/
theorem finite_expansion (p : MvPolynomial (Fin m) ℝ) :
    ∃ (s : Finset (Fin m → ℕ)) (a : (Fin m → ℕ) → ℝ),
      ∀ ω, MvPolynomial.eval ω p = ∑ α ∈ s, a α * multi α ω := by
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (eval_mem_span p)
  refine ⟨a.support, a, ?_⟩
  intro ω
  have hh := congrFun ha ω
  simpa only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hh.symm

end Paper10.Hermite
