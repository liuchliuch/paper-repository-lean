import Paper29.Sampling
import Mathlib.Logic.Equiv.Prod

noncomputable section
open scoped BigOperators Classical
namespace Paper29.Sampling

/-- One-coordinate expectation for an arbitrary heterogeneous finite product law. -/
theorem product_coordinate_expectation {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (p : ι → α → ℝ) (hp : ∀ i, ∑ a, p i a = 1) (g : α → ℝ) (j : ι) :
    (∑ f : ι → α, (∏ i, p i (f i))*g (f j)) = ∑ a, p j a*g a := by
  have hh := Fintype.prod_sum (fun i : ι => fun a : α => p i a*(if j=i then g a else 1))
  have hl : (∏ i, ∑ a, p i a*(if j=i then g a else 1)) = ∑ a, p j a*g a := by
    have he (i : ι) : (∑ a, p i a*(if j=i then g a else 1)) =
        if j=i then ∑ a, p j a*g a else 1 := by
      by_cases hi : j=i
      · subst i
        simp
      · simp [hi,hp]
    simp_rw [he]
    exact Fintype.prod_ite_eq j _
  have hr : (∑ f : ι → α, ∏ i, p i (f i)*(if j=i then g (f i) else 1)) =
      ∑ f : ι → α, (∏ i, p i (f i))*g (f j) := by
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq]
  rw [hl,hr] at hh
  exact hh.symm

end Paper29.Sampling
