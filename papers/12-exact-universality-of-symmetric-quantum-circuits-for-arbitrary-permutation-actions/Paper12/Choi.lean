import Paper12.Main
noncomputable section
namespace Paper12
open Matrix Complex Classical
variable {X : Type*} [Fintype X]

def choiScale (X : Type*) [Fintype X] : ℝ := (Real.sqrt (2 ^ Fintype.card X))⁻¹

def bellCoeff (a b : Basis X) : ℂ := if a = b then (choiScale X : ℂ) else 0

def choiCoeff (U : Op X) (a b : Basis X) : ℂ := (choiScale X : ℂ) * U b a

theorem choiScale_sq : (choiScale X : ℂ) * (choiScale X : ℂ) =
    ((2 : ℂ) ^ Fintype.card X)⁻¹ := by
  have hr : choiScale X ^ 2 = ((2 : ℝ) ^ Fintype.card X)⁻¹ := by
    unfold choiScale
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [sq] at hr
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hr
  simpa only [_root_.Complex.ofReal_mul, _root_.Complex.ofReal_inv,
    _root_.Complex.ofReal_pow, _root_.Complex.ofReal_ofNat] using hc

/-- Appendix A, equation (23): exact Bell contraction, including its factor 1/d. -/
theorem choi_contraction (U : Op X) (ψ : Vec X) (b : Basis X) :
    (∑ i : Basis X, ∑ a : Basis X, bellCoeff i a * ψ i * choiCoeff U a b) =
      ((2 : ℂ) ^ Fintype.card X)⁻¹ * applyOp U ψ b := by
  have hi : ∀ i : Basis X,
      (∑ a : Basis X, bellCoeff i a * ψ i * choiCoeff U a b) =
        (choiScale X : ℂ) * (choiScale X : ℂ) * (U b i * ψ i) := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp only [bellCoeff, if_true, choiCoeff]; ring
    · intro a _ ha
      simp [bellCoeff, Ne.symm ha]
    · intro hi
      exact (hi (Finset.mem_univ _)).elim
  simp_rw [hi, choiScale_sq]
  exact (Finset.mul_sum _ _ _).symm

theorem bellCoeff_invariant (γ : X ≃ X) (a b : Basis X) :
    bellCoeff (a ∘ γ) (b ∘ γ) = bellCoeff a b := by
  have heq : a ∘ γ = b ∘ γ ↔ a = b := by
    constructor
    · intro h
      funext x
      have hh := congrFun h (γ.symm x)
      simpa using hh
    · intro h; rw [h]
  simp only [bellCoeff, heq]

theorem choiCoeff_invariant {γ : X ≃ X} {U : Op X}
    (h : U * R γ = R γ * U) (a b : Basis X) :
    choiCoeff U (a ∘ γ) (b ∘ γ) = choiCoeff U a b := by
  have hc : R γ * U * (R γ)ᴴ = U := by
    rw [← h, Matrix.mul_assoc, R_mul_adj, Matrix.mul_one]
  have he := R_conj_apply γ U b a
  rw [hc] at he
  unfold choiCoeff
  rw [← he]
end Paper12
