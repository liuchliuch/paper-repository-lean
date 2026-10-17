import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The full space of actual iterated formal partial derivatives, including
order zero. No surrogate coefficient-space dimension enters its definition. -/
noncomputable section
namespace UniformBorderRank

variable {σ : Type*}

/-- An arbitrary ordered iterated formal partial derivative. -/
def iteratedPDeriv : List σ → MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ
  | [] => LinearMap.id
  | i :: l => (MvPolynomial.pderiv i).toLinearMap.comp (iteratedPDeriv l)

@[simp] lemma iteratedPDeriv_nil (p : MvPolynomial σ ℂ) : iteratedPDeriv [] p = p := rfl
@[simp] lemma iteratedPDeriv_cons (i : σ) (l : List σ) (p : MvPolynomial σ ℂ) :
    iteratedPDeriv (i :: l) p = MvPolynomial.pderiv i (iteratedPDeriv l p) := rfl

/-- The actual full partial-derivative space of a polynomial. -/
def fullDerivativeSpace (p : MvPolynomial σ ℂ) : Submodule ℂ (MvPolynomial σ ℂ) :=
  Submodule.span ℂ (Set.range (fun l : List σ => iteratedPDeriv l p))

lemma self_mem_fullDerivativeSpace (p : MvPolynomial σ ℂ) : p ∈ fullDerivativeSpace p :=
  Submodule.subset_span ⟨[], rfl⟩

lemma iteratedPDeriv_mem (p : MvPolynomial σ ℂ) (l : List σ) :
    iteratedPDeriv l p ∈ fullDerivativeSpace p := Submodule.subset_span ⟨l, rfl⟩

lemma pderiv_mem_fullDerivativeSpace (p q : MvPolynomial σ ℂ)
    (hq : q ∈ fullDerivativeSpace p) (i : σ) :
    MvPolynomial.pderiv i q ∈ fullDerivativeSpace p := by
  have h : fullDerivativeSpace p ≤
      (fullDerivativeSpace p).comap (MvPolynomial.pderiv i).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    exact iteratedPDeriv_mem p (i :: l)
  exact h hq

/-- The derivative space is the smallest subspace containing the polynomial
and closed under every actual formal partial derivative. -/
theorem fullDerivativeSpace_le (p : MvPolynomial σ ℂ)
    (W : Submodule ℂ (MvPolynomial σ ℂ)) (hp : p ∈ W)
    (hW : ∀ i q, q ∈ W → MvPolynomial.pderiv i q ∈ W) :
    fullDerivativeSpace p ≤ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  induction l with
  | nil => exact hp
  | cons i l ih => exact hW i _ ih

end UniformBorderRank
