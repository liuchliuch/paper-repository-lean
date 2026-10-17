import Paper10.Gaussian
import Paper10.SSC

noncomputable section
open Matrix
namespace Paper10
variable {q m : ℕ}

/-- Symmetric part of a product of two symmetric matrices. -/
def symProduct (U V : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  (1 / 2 : ℝ) • (U * V + V * U)

theorem symProduct_isSymm {U V : Matrix (Fin q) (Fin q) ℝ}
    (hU : U.IsSymm) (hV : V.IsSymm) : (symProduct U V).IsSymm := by
  unfold Matrix.IsSymm symProduct
  rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
    show Uᵀ = U from hU, show Vᵀ = V from hV, add_comm]

/-- For symmetric matrices the trace of a triple is fully symmetric. -/
theorem trace_triple_swap {A B C : Matrix (Fin q) (Fin q) ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) (hC : C.IsSymm) :
    Matrix.trace (A * B * C) = Matrix.trace (A * C * B) := by
  calc
    _ = Matrix.trace ((A * B * C)ᵀ) := (Matrix.trace_transpose _).symm
    _ = Matrix.trace (C * B * A) := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, hA, hB, hC, Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_cycle _ _ _

theorem frob_symProduct {A B C : Matrix (Fin q) (Fin q) ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) (hC : C.IsSymm) :
    frob A (symProduct B C) = Matrix.trace (A * B * C) := by
  simp only [frob, symProduct, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul,
    Matrix.trace_add, smul_eq_mul, ← Matrix.mul_assoc]
  rw [← trace_triple_swap hA hB hC]
  ring

theorem symProduct_norm_sq {U V : Matrix (Fin q) (Fin q) ℝ}
    (hU : U.IsSymm) (hV : V.IsSymm) :
    frobNormSq (symProduct U V) =
      (Matrix.trace (U * U * V * V) + Matrix.trace (U * V * U * V)) / 2 := by
  have h1 := trace_four_cycle U V V U
  have h2 : Matrix.trace (V * U * U * V) = Matrix.trace (U * U * V * V) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm V (U * U * V)
  have h3 := trace_four_cycle V U V U
  simp only [frobNormSq, frob, symProduct, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_smul, smul_eq_mul, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add,
    ← Matrix.mul_assoc]
  rw [h1, h2, h3]
  ring

theorem symProduct_norm_le {U V : Matrix (Fin q) (Fin q) ℝ}
    (hU : U.IsSymm) (hV : V.IsSymm) :
    frobNormSq (symProduct U V) ≤ Matrix.trace (U * U * V * V) := by
  rw [symProduct_norm_sq hU hV]
  have h := frob_cs_UVUV hU hV
  have hh := le_abs_self (Matrix.trace (U * V * U * V))
  linarith

/-- Bessel's inequality for a covariance contraction diagonalized in any full basis. -/
theorem covariance_bessel (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) (σ : Fin m → ℝ) (hσ : ∀ a, 0 ≤ σ a ∧ σ a ≤ 1)
    (U : Matrix (Fin q) (Fin q) ℝ) (hU : U.IsSymm) :
    (∑ a, frob (σ a • F a) U ^ 2) ≤ frobNormSq U := by
  have hh : (∑ a, frob (σ a • F a) U ^ 2) ≤ ∑ a, frob (F a) U ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    simp only [frob, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_pow]
    have hs : σ a ^ 2 ≤ 1 := by nlinarith [(hσ a).1, (hσ a).2]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (sq_nonneg (Matrix.trace (F a * U)))
  exact hh.trans_eq (frob_parseval F hF U hU)

/-- Tensor square contribution in the sixth Wick expansion. -/
theorem cubic_tensor_le (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) (σ : Fin m → ℝ) (hσ : ∀ a, 0 ≤ σ a ∧ σ a ≤ 1) :
    let B := fun a => σ a • F a
    (∑ a, ∑ b, ∑ c, Matrix.trace (B a * B b * B c) ^ 2) ≤
      Matrix.trace ((∑ a, B a * B a) * (∑ a, B a * B a)) := by
  let B := fun a => σ a • F a
  have hB : ∀ a, (B a).IsSymm := fun a => (hF.1 a).smul (σ a)
  have hp : ∀ b c, (∑ a, Matrix.trace (B a * B b * B c) ^ 2) ≤
      Matrix.trace (B b * B b * B c * B c) := by
    intro b c
    have hh := covariance_bessel F hF σ hσ (symProduct (B b) (B c))
      (symProduct_isSymm (hB b) (hB c))
    have he : ∀ a, frob (σ a • F a) (symProduct (B b) (B c)) =
        Matrix.trace (B a * B b * B c) := by
      intro a
      exact frob_symProduct (hB a) (hB b) (hB c)
    simp_rw [he] at hh
    exact hh.trans (symProduct_norm_le (hB b) (hB c))
  calc
    _ = ∑ b, ∑ c, ∑ a, Matrix.trace (B a * B b * B c) ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ ≤ ∑ b, ∑ c, Matrix.trace (B b * B b * B c * B c) :=
      Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun c _ => hp b c))
    _ = _ := by
      simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
      rw [Finset.sum_comm]

/-- Contraction contribution in the sixth Wick expansion. -/
theorem cubic_contraction_le (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) (σ : Fin m → ℝ) (hσ : ∀ a, 0 ≤ σ a ∧ σ a ≤ 1) :
    let B := fun a => σ a • F a
    (∑ a, (Matrix.trace (B a * ∑ b, B b * B b)) ^ 2) ≤
      Matrix.trace ((∑ a, B a * B a) * (∑ a, B a * B a)) := by
  let B := fun a => σ a • F a
  have hB : ∀ a, (B a).IsSymm := fun a => (hF.1 a).smul (σ a)
  exact covariance_bessel F hF σ hσ _
    (sum_sq_posSemidef B hB).isHermitian

end Paper10
