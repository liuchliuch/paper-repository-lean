import Paper22.Tensor
import Paper22.Programs

/-! Actual two-by-two classical blocks on the output of one noiseless bit. -/
open scoped MatrixOrder ComplexOrder Kronecker
open Matrix
noncomputable section
namespace Paper22
variable {d : ℕ}

/-- Insert two matrices as the two classical diagonal blocks. -/
def bitDiagonal (B : Fin 2 → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ :=
  (Matrix.blockDiagonal B).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- Compress to the output block carrying classical bit b. -/
def bitCompression (A : Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ) (b : Fin 2) :
    Matrix (Fin d) (Fin d) ℂ :=
  A.submatrix (fun i => finProdFinEquiv (i,b)) (fun i => finProdFinEquiv (i,b))

@[simp] theorem bitCompression_diagonal (B : Fin 2 → Matrix (Fin d) (Fin d) ℂ)
    (b : Fin 2) : bitCompression (bitDiagonal B) b = B b := by
  ext i j
  simp [bitCompression, bitDiagonal, Matrix.blockDiagonal_apply]

@[simp] theorem bitDiagonal_one : bitDiagonal (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
  exact (congrArg (fun A : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ =>
    A.submatrix finProdFinEquiv.symm finProdFinEquiv.symm) Matrix.blockDiagonal_one).trans
      (Matrix.submatrix_one_equiv _)

@[simp] theorem bitDiagonal_zero : bitDiagonal (fun _ => (0 : Matrix (Fin d) (Fin d) ℂ)) = 0 := by
  ext i j
  simp [bitDiagonal, Matrix.blockDiagonal_apply]

@[simp] theorem bitDiagonal_add (B C : Fin 2 → Matrix (Fin d) (Fin d) ℂ) :
    bitDiagonal (fun b => B b + C b) = bitDiagonal B + bitDiagonal C := by
  simp only [bitDiagonal, ← Pi.add_def, Matrix.blockDiagonal_add]
  rfl

@[simp] theorem bitDiagonal_sub (B C : Fin 2 → Matrix (Fin d) (Fin d) ℂ) :
    bitDiagonal (fun b => B b - C b) = bitDiagonal B - bitDiagonal C := by
  simp only [bitDiagonal, ← Pi.sub_def, Matrix.blockDiagonal_sub]
  rfl

@[simp] theorem bitDiagonal_smul (t : ℝ) (B : Fin 2 → Matrix (Fin d) (Fin d) ℂ) :
    bitDiagonal (fun b => t • B b) = t • bitDiagonal B := by
  simp only [bitDiagonal, ← Pi.smul_def, Matrix.blockDiagonal_smul]
  rfl

theorem bitDiagonal_nonneg {B : Fin 2 → Matrix (Fin d) (Fin d) ℂ}
    (hB : ∀ b, 0 ≤ B b) : 0 ≤ bitDiagonal B := by
  let C : Fin 2 → Matrix (Fin d) (Fin d) ℂ := fun b => CFC.sqrt (B b)
  have hC : ∀ b, (C b)ᴴ = C b := fun b => (CFC.sqrt_nonneg (B b)).posSemidef.isHermitian.eq
  have hCC : ∀ b, C b * C b = B b := fun b => CFC.sqrt_mul_sqrt_self _ (hB b)
  have heq : Matrix.blockDiagonal B =
      (Matrix.blockDiagonal C)ᴴ * Matrix.blockDiagonal C := by
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    congr 1
    funext b
    rw [hC b, hCC b]
  exact ((heq ▸ Matrix.posSemidef_conjTranspose_mul_self (Matrix.blockDiagonal C)).submatrix
    finProdFinEquiv.symm).nonneg

theorem bitDiagonal_mono {B C : Fin 2 → Matrix (Fin d) (Fin d) ℂ}
    (h : ∀ b, B b ≤ C b) : bitDiagonal B ≤ bitDiagonal C := by
  apply sub_nonneg.mp
  rw [← bitDiagonal_sub]
  exact bitDiagonal_nonneg fun b => sub_nonneg.mpr (h b)

theorem bitDiagonal_isEffect {B : Fin 2 → Matrix (Fin d) (Fin d) ℂ}
    (hB : ∀ b, IsEffect (B b)) : IsEffect (bitDiagonal B) := by
  refine ⟨bitDiagonal_nonneg fun b => (hB b).1, ?_⟩
  simpa using bitDiagonal_mono fun b => (hB b).2

@[simp] theorem bitCompression_one (b : Fin 2) :
    bitCompression (1 : Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ) b = 1 := by
  apply Matrix.submatrix_one
  intro i j hij
  exact congrArg Prod.fst (finProdFinEquiv.injective hij)

@[simp] theorem bitCompression_zero (b : Fin 2) :
    bitCompression (0 : Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ) b = 0 := rfl

@[simp] theorem bitCompression_add (A B : Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ) (b : Fin 2) :
    bitCompression (A+B) b = bitCompression A b + bitCompression B b := rfl

@[simp] theorem bitCompression_sub (A B : Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ) (b : Fin 2) :
    bitCompression (A-B) b = bitCompression A b - bitCompression B b := rfl

@[simp] theorem bitCompression_smul (t : ℝ) (A : Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ) (b : Fin 2) :
    bitCompression (t • A) b = t • bitCompression A b := rfl

theorem bitCompression_nonneg {A : Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ}
    (hA : 0 ≤ A) (b : Fin 2) : 0 ≤ bitCompression A b :=
  (hA.posSemidef.submatrix _).nonneg

theorem bitCompression_mono {A B : Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ}
    (h : A ≤ B) (b : Fin 2) : bitCompression A b ≤ bitCompression B b := by
  apply sub_nonneg.mp
  rw [← bitCompression_sub]
  exact bitCompression_nonneg (sub_nonneg.mpr h) b

@[simp] theorem bitCompression_sum {ι : Type*} [Fintype ι]
    (A : ι → Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ) (b : Fin 2) :
    bitCompression (∑ i, A i) b = ∑ i, bitCompression (A i) b := by
  ext i j
  simp only [bitCompression, Matrix.submatrix_apply, Matrix.sum_apply]

@[simp] theorem bitDiagonal_sum {ι : Type*} [Fintype ι]
    (B : ι → Fin 2 → Matrix (Fin d) (Fin d) ℂ) :
    bitDiagonal (fun b => ∑ i, B i b) = ∑ i, bitDiagonal (B i) := by
  classical
  ext i j
  simp only [bitDiagonal, Matrix.submatrix_apply, Matrix.blockDiagonal_apply, Matrix.sum_apply]
  split_ifs <;> simp

/-- Reindexing to product indices does not change the trace of a product. -/
theorem bit_reindex_trace_mul (A B : Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ) :
    (A * B).trace = ((A.submatrix finProdFinEquiv finProdFinEquiv) *
      (B.submatrix finProdFinEquiv finProdFinEquiv)).trace := by
  rw [Matrix.submatrix_mul_equiv]
  exact (trace_submatrix_equiv (A * B) finProdFinEquiv).symm

/-- Pairing a state supported on one classical block with an arbitrary effect. -/
theorem bitDiagonal_single_trace (ρ : Matrix (Fin d) (Fin d) ℂ) (b : Fin 2)
    (A : Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ) :
    (bitDiagonal (fun c => if c = b then ρ else 0) * A).trace =
      (ρ * bitCompression A b).trace := by
  rw [bit_reindex_trace_mul]
  simp only [bitDiagonal, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
    Matrix.submatrix_id_id]
  fin_cases b <;> simp [Matrix.trace, Matrix.mul_apply, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, bitCompression, ite_mul]

/-- The actual tensor-channel output is supported on its noiseless-bit block. -/
theorem activationFamily_states {n : ℕ} (V : CQChannel n d) (x : Fin n) (b : Fin 2) :
    (activationFamily V).states (finProdFinEquiv (x,b)) =
      bitDiagonal (fun c => if c = b then V.states x else 0) := by
  ext i j
  simp only [activationFamily, CQChannel.tensor, noiselessBit, bitDiagonal,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.kronecker_apply,
    Matrix.diagonal_apply, Matrix.blockDiagonal_apply]
  split_ifs <;> simp_all

/-- The source objective for a tensor output only sees the matching diagonal block. -/
theorem activationFamily_trace {n : ℕ} (V : CQChannel n d) (x : Fin n) (b : Fin 2)
    (A : Matrix (Fin (d * 2)) (Fin (d * 2)) ℂ) :
    ((activationFamily V).states (finProdFinEquiv (x,b)) * A).trace.re =
      (V.states x * bitCompression A b).trace.re := by
  rw [activationFamily_states, bitDiagonal_single_trace]


/-- Sums over the actual mixed-radix input alphabet split into bit blocks. -/
theorem sum_bit_indices {n : ℕ} {G : Type*} [AddCommMonoid G]
    (f : Fin (n * 2) → G) :
    (∑ a, f a) = ∑ x : Fin n, ∑ b : Fin 2, f (finProdFinEquiv (x,b)) := by
  rw [← finProdFinEquiv.sum_comp f]
  exact Fintype.sum_prod_type _

/-- Complementary classical labels interchange the two diagonal blocks. -/
theorem bitDiagonal_swap_sum (S H : Matrix (Fin d) (Fin d) ℂ) :
    (∑ b : Fin 2, bitDiagonal (fun c => if c = b then S else H)) =
      bitDiagonal (fun _ => S + H) := by
  rw [Fin.sum_univ_two, ← bitDiagonal_add]
  congr 1
  funext c
  fin_cases c <;> simp [add_comm]


end Paper22
end
