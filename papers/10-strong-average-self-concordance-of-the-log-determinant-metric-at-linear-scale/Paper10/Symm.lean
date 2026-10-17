import Paper10.Basic
import Paper10.FiniteSums

/-!
# Symmetric matrices: orthonormal basis and sum-of-squares identity

Equation (12): for any Frobenius-orthonormal basis `{F_a}` of `S^q`,
  `sum_a F_a^2 = c_q * I`.
-/

noncomputable section

open Matrix

namespace Paper10

/-- A full Frobenius orthonormal basis, including the necessary spanning condition. -/
def OrthonormalFrob {q : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → Matrix (Fin q) (Fin q) ℝ) : Prop := by
  classical
  exact (∀ a, (F a).IsSymm) ∧ (∀ a b : ι, frob (F a) (F b) = if a = b then 1 else 0) ∧
    (∀ U : Matrix (Fin q) (Fin q) ℝ, U.IsSymm →
      ∃ v : ι → ℝ, U = ∑ a, v a • F a)

/-- The diagonal unit agrees with the library's elementary matrix. -/
theorem eii_eq_single {q : ℕ} (i : Fin q) : eii i = Matrix.single i i (1 : ℝ) := by
  ext a b
  simp only [eii, Matrix.single, Matrix.of_apply]
  by_cases ha : a = i <;> by_cases hb : b = i <;> simp_all [eq_comm]

/-- Off-diagonal symmetric units as sums of elementary matrices. -/
theorem eijSymm_eq_single {q : ℕ} (i j : Fin q) (hij : i ≠ j) :
    eijSymm i j = Matrix.single i j (1 / Real.sqrt 2) +
      Matrix.single j i (1 / Real.sqrt 2) := by
  ext a b
  simp only [eijSymm, Matrix.single, Matrix.of_apply, Matrix.add_apply]
  by_cases ha : a = i <;> by_cases hb : b = j <;>
    by_cases hc : a = j <;> by_cases hd : b = i <;> simp_all [eq_comm]

/-- Diagonal unit squares to itself: `E_{ii} * E_{ii} = E_{ii}`. -/
theorem eii_mul_self {q : ℕ} (i : Fin q) :
    eii i * eii i = eii i := by
  rw [eii_eq_single, Matrix.single_mul_single_same, one_mul]

/-- Off-diagonal unit square: `((E_{ij}+E_{ji})/√2)^2 = (E_{ii}+E_{jj})/2`. -/
theorem eijSymm_sq {q : ℕ} (i j : Fin q) (hij : i ≠ j) :
    eijSymm i j * eijSymm i j
      = (1 / 2 : ℝ) • (eii i + eii j) := by
  rw [eijSymm_eq_single i j hij, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  rw [Matrix.single_mul_single_of_ne (1 / Real.sqrt 2) i j i hij.symm (1 / Real.sqrt 2),
    Matrix.single_mul_single_of_ne (1 / Real.sqrt 2) j i j hij (1 / Real.sqrt 2),
    Matrix.single_mul_single_same, Matrix.single_mul_single_same]
  have hs : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1 / 2 := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    nlinarith
  rw [hs, eii_eq_single, eii_eq_single, smul_add, Matrix.smul_single, Matrix.smul_single]
  simp

/-- Sum of diagonal units is the identity: `sum_i E_{ii} = I`. -/
theorem sum_eii (q : ℕ) :
    ∑ i : Fin q, eii i = oneMat q := by
  ext a b
  simp only [Matrix.sum_apply, oneMat, eii]
  by_cases hab : a = b
  · subst b
    simp [Matrix.one_apply, eq_comm]
  · simp [Matrix.one_apply, hab, show ∀ i, ¬(a = i ∧ b = i) by grind]

/-- Equation (12) in the standard basis. -/
theorem sum_squares_standard (q : ℕ) :
    (∑ i : Fin q, (eii i) * (eii i)) +
      (∑ p : {x : Fin q × Fin q // x.1 < x.2},
        (eijSymm p.val.1 p.val.2) * (eijSymm p.val.1 p.val.2))
      = (c q) • (oneMat q) := by
  classical
  simp_rw [eii_mul_self]
  rw [sum_eii]
  have hp : ∀ p : {x : Fin q × Fin q // x.1 < x.2},
      eijSymm p.1.1 p.1.2 * eijSymm p.1.1 p.1.2 = (1 / 2 : ℝ) • (eii p.1.1 + eii p.1.2) :=
    fun p => eijSymm_sq _ _ (ne_of_lt p.2)
  simp_rw [hp]
  ext a b
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hu := twice_sum_upper (fun i j => eii i a b + eii j a b) (by intros; ring)
  have he : (∑ i : Fin q, eii i a b) = oneMat q a b := by
    simpa only [Matrix.sum_apply] using congrArg (fun M : Matrix (Fin q) (Fin q) ℝ => M a b) (sum_eii q)
  have hdiag : (∑ i : Fin q, (eii i a b + eii i a b)) = 2 * oneMat q a b := by
    rw [Finset.sum_add_distrib, he]; ring
  have hall : (∑ i : Fin q, ∑ j : Fin q, (eii i a b + eii j a b)) =
      2 * (q : ℝ) * oneMat q a b := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, he, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [hdiag, hall] at hu
  rw [← Finset.mul_sum]
  simp only [c, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- Frobenius reconstruction from orthonormality and spanning. -/
theorem frob_orthonormal_sum {q : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F)
    (U : Matrix (Fin q) (Fin q) ℝ) (hU : U.IsSymm) :
    U = ∑ a, frob (F a) U • F a := by
  classical
  obtain ⟨v, hv⟩ := hF.2.2 U hU
  have hc : ∀ a, frob (F a) U = v a := by
    intro a
    rw [hv]
    simp only [frob, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      smul_eq_mul]
    change (∑ b, v b * frob (F a) (F b)) = v a
    simp [hF.2.1]
  simp_rw [hc]
  exact hv

/-- An unnormalised symmetric elementary matrix, also defined on the diagonal. -/
def symUnit {q : ℕ} (i j : Fin q) : Matrix (Fin q) (Fin q) ℝ :=
  Matrix.single i j 1 + Matrix.single j i 1

theorem symUnit_isSymm {q : ℕ} (i j : Fin q) : (symUnit i j).IsSymm := by
  simp only [Matrix.IsSymm, symUnit, Matrix.transpose_add, Matrix.transpose_single]
  exact add_comm _ _

theorem frob_single {q : ℕ} (U : Matrix (Fin q) (Fin q) ℝ) (i j : Fin q) (r : ℝ) :
    frob U (Matrix.single i j r) = r * U j i := by
  simp [frob, Matrix.trace, Matrix.mul_apply, Matrix.single, ite_and, eq_comm, mul_comm]

theorem frob_symUnit {q : ℕ} (U : Matrix (Fin q) (Fin q) ℝ) (hU : U.IsSymm) (i j : Fin q) :
    frob U (symUnit i j) = 2 * U i j := by
  unfold symUnit
  have hh : frob U (Matrix.single i j 1 + Matrix.single j i 1) =
      frob U (Matrix.single i j 1) + frob U (Matrix.single j i 1) := by
    simp [frob, Matrix.mul_add, Matrix.trace_add]
  rw [hh, frob_single, frob_single, ← hU.apply i j]
  ring

/-- Entrywise completeness relation for any full Frobenius orthonormal basis. -/
theorem orthonormal_kernel {q : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F) (i j k l : Fin q) :
    2 * (∑ a, F a i j * F a k l) = symUnit i j k l := by
  have h := congrArg (fun U : Matrix (Fin q) (Fin q) ℝ => U k l)
    (frob_orthonormal_sum F hF (symUnit i j) (symUnit_isSymm i j))
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
  simp_rw [frob_symUnit _ (hF.1 _) i j] at h
  simpa only [Finset.mul_sum, mul_assoc] using h.symm

/-- Rotation-invariant identity (12) for any full orthonormal basis. -/
theorem sum_squares_orthonormal {q : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F) :
    ∑ a, F a * F a = (c q) • (oneMat q) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  have hh : 2 * (∑ a, ∑ k, F a i k * F a k j) = ∑ k, symUnit i k k j := by
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => orthonormal_kernel F hF i k k j)
  have he : (∑ k : Fin q, symUnit i k k j) = ((q : ℝ) + 1) * oneMat q i j := by
    by_cases hij : i = j
    · subst j
      simp [symUnit, Matrix.single, oneMat, Matrix.one_apply, eq_comm, Finset.sum_add_distrib, add_comm]
    · simp [symUnit, Matrix.single, oneMat, Matrix.one_apply, hij, Ne.symm hij,
        show ∀ k, ¬(i = k ∧ k = j) by grind]
  rw [he] at hh
  simp only [c, Nat.cast_add, Nat.cast_one]
  linarith

/-- Parseval's identity in the full symmetric space. -/
theorem frob_parseval {q : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F)
    (U : Matrix (Fin q) (Fin q) ℝ) (hU : U.IsSymm) :
    ∑ a, frob (F a) U ^ 2 = frob U U := by
  have hu := frob_orthonormal_sum F hF U hU
  calc
    _ = frob (∑ a, frob (F a) U • F a) U := by
      simp [frob, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
        Matrix.trace_smul, pow_two]
    _ = frob U U := by rw [← hu]

/-- Parseval for traces of basis elements. -/
theorem parseval_trace_one {q : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F) :
    ∑ a, (Matrix.trace (F a)) ^ 2 = q := by
  have hh := frob_parseval F hF 1 (by exact Matrix.transpose_one)
  simpa [frob] using hh

theorem parseval_trace_sq {q : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F) :
    ∑ a, Matrix.trace (F a * F a) = n q := by
  rw [← Matrix.trace_sum, sum_squares_orthonormal F hF]
  simp only [Matrix.trace_smul, oneMat, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  rw [n_mul_c]
  ring

/-- Completeness identity (23) on all real matrices. -/
theorem sum_FUF {q : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F)
    (U : Matrix (Fin q) (Fin q) ℝ) :
    ∑ a, F a * U * F a = (1 / 2 : ℝ) • (Uᵀ + Matrix.trace U • (1 : Matrix _ _ ℝ)) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul, Matrix.one_apply]
  have hexp : (∑ a, ∑ l, (∑ k, F a i k * U k l) * F a l j) =
      ∑ l, ∑ k, U k l * ∑ a, F a i k * F a l j := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hexp]
  have hh : 2 * (∑ l, ∑ k, U k l * ∑ a, F a i k * F a l j) =
      ∑ l, ∑ k, U k l * symUnit i k l j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    calc
      _ = U k l * (2 * ∑ a, F a i k * F a l j) := by ring
      _ = _ := by rw [orthonormal_kernel F hF i k l j]
  have he : (∑ l, ∑ k, U k l * symUnit i k l j) =
      U j i + Matrix.trace U * (if i = j then 1 else 0) := by
    simp only [symUnit, Matrix.add_apply, Matrix.single, Matrix.of_apply, mul_add,
      Finset.sum_add_distrib]
    simp_rw [mul_ite, mul_one, mul_zero, ite_and]
    by_cases hij : i = j
    · subst j
      simp [Matrix.trace, eq_comm]
    · simp [hij, Ne.symm hij, eq_comm]
  rw [he] at hh
  linarith

end Paper10
