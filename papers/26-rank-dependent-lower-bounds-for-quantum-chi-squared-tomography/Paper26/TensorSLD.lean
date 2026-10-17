import Paper26.TensorCopies
import Paper26.EnergyReality

/-!
# Actual tensor-copy SLD sums

Single-site lifts act on the actual function-indexed tensor basis `Fin n → ι`.
Finite products/sums prove their multiplication, adjoints and trace identities.
For a centered Hermitian single-copy score H, the sum over sites is Hermitian,
has zero tensor-state mean, and has n times the single-copy squared energy.
The single-copy SLD equation lifts to the actual sum of tensor slots of D.
No information-additivity theorem is an input. Identifying the tensor-slot sum
with the derivative of a smooth tensor-state family is a separate calculus step.
-/

noncomputable section

namespace Paper26.TensorSLD

open QuantumModel
open scoped BigOperators Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- Tensor product of possibly different actual matrices at every site. -/
def tensor (A : Fin n → Matrix ι ι ℂ) : Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  fun x y => ∏ k, A k (x k) (y k)

omit [Fintype ι] [DecidableEq ι] in
theorem tensor_const (A : Matrix ι ι ℂ) (n : ℕ) :
    tensor (fun _ : Fin n => A) = TensorCopies.matrix A n := rfl

omit [DecidableEq ι] in
theorem tensor_mul (A B : Fin n → Matrix ι ι ℂ) :
    tensor (fun k => A k * B k) = tensor A * tensor B := by
  ext x y
  simpa only [tensor, Matrix.mul_apply, Finset.prod_mul_distrib] using
    (Fintype.prod_sum (fun k : Fin n => fun j : ι => A k (x k) j * B k j (y k)))

omit [Fintype ι] [DecidableEq ι] in
theorem tensor_conjTranspose (A : Fin n → Matrix ι ι ℂ) :
    tensor (fun k => (A k)ᴴ) = (tensor A)ᴴ := by
  ext x y
  simp [tensor, Matrix.conjTranspose_apply]

omit [DecidableEq ι] in
theorem tensor_trace (A : Fin n → Matrix ι ι ℂ) :
    Matrix.trace (tensor A) = ∏ k, Matrix.trace (A k) := by
  simpa only [tensor, Matrix.trace, Matrix.diag_apply] using
    (Fintype.prod_sum (fun k : Fin n => fun j : ι => A k j j)).symm

omit [Fintype ι] in
theorem tensor_one (n : ℕ) : tensor (fun _ : Fin n => (1 : Matrix ι ι ℂ)) = 1 := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [tensor]
  · have hn : ∃ k, x k ≠ y k := by
      by_contra h
      apply hxy
      funext k
      exact not_ne_iff.mp (not_exists.mp h k)
    obtain ⟨k, hk⟩ := hn
    rw [Matrix.one_apply_ne hxy]
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [hk]

/-- A tensor product with one matrix replaced at site k. -/
def slot (A X : Matrix ι ι ℂ) (k : Fin n) : Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  tensor (fun j => if j = k then X else A)

/-- The operator H at site k and identity deltas on every other coordinate. -/
def lift (H : Matrix ι ι ℂ) (k : Fin n) : Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  slot 1 H k

omit [Fintype ι] [DecidableEq ι] in
theorem slot_apply (A X : Matrix ι ι ℂ) (k : Fin n) (x y : Fin n → ι) :
    slot A X k x y = X (x k) (y k) *
      ∏ j ∈ Finset.univ.erase k, A (x j) (y j) := by
  unfold slot tensor
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [if_neg (Finset.ne_of_mem_erase hj)]

omit [Fintype ι] in
/-- The explicit identity-delta action on all untouched coordinates. -/
theorem lift_apply (H : Matrix ι ι ℂ) (k : Fin n) (x y : Fin n → ι) :
    lift H k x y = H (x k) (y k) *
      ∏ j ∈ Finset.univ.erase k, (if x j = y j then (1 : ℂ) else 0) := by
  rw [lift, slot_apply]
  simp only [Matrix.one_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem slot_add (A X Y : Matrix ι ι ℂ) (k : Fin n) :
    slot A (X + Y) k = slot A X k + slot A Y k := by
  ext x y
  simp only [slot_apply, Matrix.add_apply]
  exact add_mul _ _ _

omit [Fintype ι] [DecidableEq ι] in
theorem slot_smul (A X : Matrix ι ι ℂ) (k : Fin n) (c : ℂ) :
    slot A (c • X) k = c • slot A X k := by
  ext x y
  simp only [slot_apply, Matrix.smul_apply, smul_eq_mul]
  exact mul_assoc _ _ _

omit [Fintype ι] in
theorem lift_conjTranspose (H : Matrix ι ι ℂ) (k : Fin n) :
    (lift H k)ᴴ = lift Hᴴ k := by
  unfold lift slot
  rw [← tensor_conjTranspose]
  congr 1
  funext j
  split_ifs <;> simp

omit [Fintype ι] in
theorem lift_hermitian (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (k : Fin n) :
    (lift H k).IsHermitian := by
  change (lift H k)ᴴ = lift H k
  rw [lift_conjTranspose, hH.eq]

theorem lift_mul_same (H K : Matrix ι ι ℂ) (k : Fin n) :
    lift H k * lift K k = lift (H * K) k := by
  unfold lift slot
  rw [← tensor_mul]
  congr 1
  funext j
  split_ifs <;> simp

theorem copies_mul_lift (A H : Matrix ι ι ℂ) (k : Fin n) :
    TensorCopies.matrix A n * lift H k = slot A (A * H) k := by
  change tensor (fun _ : Fin n => A) * tensor (fun j => if j = k then H else 1) = _
  rw [← tensor_mul]
  unfold slot
  congr 1
  funext j
  split_ifs <;> simp

theorem lift_mul_copies (A H : Matrix ι ι ℂ) (k : Fin n) :
    lift H k * TensorCopies.matrix A n = slot A (H * A) k := by
  change tensor (fun j => if j = k then H else 1) * tensor (fun _ : Fin n => A) = _
  rw [← tensor_mul]
  unfold slot
  congr 1
  funext j
  split_ifs <;> simp

omit [DecidableEq ι] in
/-- A trace-one background removes every untouched tensor slot. -/
theorem trace_slot (A X : Matrix ι ι ℂ) (hA : Matrix.trace A = 1) (k : Fin n) :
    Matrix.trace (slot A X k) = Matrix.trace X := by
  rw [slot, tensor_trace]
  calc
    (∏ j : Fin n, Matrix.trace (if j = k then X else A)) =
        Matrix.trace (if k = k then X else A) := by
      apply Finset.prod_eq_single k
      · intro j _ hj
        rw [if_neg hj, hA]
      · simp
    _ = Matrix.trace X := by simp

theorem trace_copies_mul_lift (ρ : Density ι) (H : Matrix ι ι ℂ) (k : Fin n) :
    Matrix.trace (TensorCopies.matrix ρ.matrix n * lift H k) =
      Matrix.trace (ρ.matrix * H) := by
  rw [copies_mul_lift, trace_slot _ _ ρ.trace_one]

/-- Distinct centered slots have exactly zero mixed trace. -/
theorem trace_copies_mul_lifts_ne (ρ : Density ι) (H : Matrix ι ι ℂ)
    (hz : Matrix.trace (ρ.matrix * H) = 0) (k l : Fin n) (hkl : k ≠ l) :
    Matrix.trace (TensorCopies.matrix ρ.matrix n * lift H k * lift H l) = 0 := by
  change Matrix.trace (tensor (fun _ : Fin n => ρ.matrix) *
    tensor (fun j => if j = k then H else 1) *
    tensor (fun j => if j = l then H else 1)) = 0
  rw [← tensor_mul, ← tensor_mul, tensor_trace]
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simpa only [ite_true, if_neg hkl, Matrix.mul_one] using hz

/-- The sum of single-site operators on the actual tensor basis. -/
def totalLift (H : Matrix ι ι ℂ) (n : ℕ) : Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  ∑ k : Fin n, lift H k

omit [Fintype ι] in
theorem totalLift_hermitian (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (n : ℕ) :
    (totalLift H n).IsHermitian := by
  change (∑ k : Fin n, lift H k)ᴴ = ∑ k : Fin n, lift H k
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact (lift_hermitian H hH k).eq

theorem trace_copies_totalLift (ρ : Density ι) (H : Matrix ι ι ℂ) (n : ℕ) :
    Matrix.trace (TensorCopies.matrix ρ.matrix n * totalLift H n) =
      (n : ℂ) * Matrix.trace (ρ.matrix * H) := by
  simp only [totalLift, Matrix.mul_sum, Matrix.trace_sum, trace_copies_mul_lift]
  simp

/-- Hermitian product trace reality turns the stated real centering into
actual complex trace zero. No commutation assumption is used. -/
theorem centered_trace_eq_zero (ρ : Density ι) (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hz : (Matrix.trace (ρ.matrix * H)).re = 0) :
    Matrix.trace (ρ.matrix * H) = 0 := by
  rw [← EnergyReality.trace_hermitian_product_real _ _ ρ.hermitian.eq hH.eq, hz]
  rfl

theorem totalLift_mean_zero (ρ : Density ι) (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hz : (Matrix.trace (ρ.matrix * H)).re = 0) (n : ℕ) :
    Matrix.trace ((TensorCopies.density ρ n).matrix * totalLift H n) = 0 := by
  rw [show (TensorCopies.density ρ n).matrix = TensorCopies.matrix ρ.matrix n from rfl,
    trace_copies_totalLift, centered_trace_eq_zero ρ H hH hz, mul_zero]

/-- Full complex trace energy additivity, including the empty tensor n=0. -/
theorem totalLift_trace_square (ρ : Density ι) (H : Matrix ι ι ℂ)
    (hz : Matrix.trace (ρ.matrix * H) = 0) (n : ℕ) :
    Matrix.trace (TensorCopies.matrix ρ.matrix n * (totalLift H n * totalLift H n)) =
      (n : ℂ) * Matrix.trace (ρ.matrix * (H * H)) := by
  have hpair (k l : Fin n) :
      Matrix.trace (TensorCopies.matrix ρ.matrix n * lift H k * lift H l) =
        if k = l then Matrix.trace (ρ.matrix * (H * H)) else 0 := by
    by_cases hkl : k = l
    · subst l
      rw [if_pos rfl, Matrix.mul_assoc, lift_mul_same, trace_copies_mul_lift]
    · rw [if_neg hkl]
      exact trace_copies_mul_lifts_ne ρ H hz k l hkl
  calc
    Matrix.trace (TensorCopies.matrix ρ.matrix n * (totalLift H n * totalLift H n)) =
        ∑ k : Fin n, ∑ l : Fin n,
          Matrix.trace (TensorCopies.matrix ρ.matrix n * lift H k * lift H l) := by
      simp only [totalLift, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum,
        Matrix.mul_assoc]
      exact Finset.sum_comm
    _ = ∑ k : Fin n, Matrix.trace (ρ.matrix * (H * H)) := by
      simp_rw [hpair]
      simp
    _ = (n : ℂ) * Matrix.trace (ρ.matrix * (H * H)) := by simp

/-- The actual real tensor SLD energy is exactly n times the single-copy one. -/
theorem totalLift_energy (ρ : Density ι) (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hz : (Matrix.trace (ρ.matrix * H)).re = 0) (n : ℕ) :
    (Matrix.trace ((TensorCopies.density ρ n).matrix * (totalLift H n) ^ 2)).re =
      (n : ℝ) * (Matrix.trace (ρ.matrix * H ^ 2)).re := by
  have he := congrArg Complex.re
    (totalLift_trace_square ρ H (centered_trace_eq_zero ρ H hH hz) n)
  simpa only [pow_two, TensorCopies.density, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero] using he

/-- The actual sum of tensors with D at one site and ρ elsewhere. It is not
assumed to be a derivative of any parameterized family. -/
def derivativeCopy (ρ : Density ι) (D : Matrix ι ι ℂ) (n : ℕ) :
    Matrix (Fin n → ι) (Fin n → ι) ℂ := ∑ k : Fin n, slot ρ.matrix D k

/-- Native lifting of the single-copy SLD equation to n tensor copies. -/
theorem sld_equation (ρ : Density ι) (H D : Matrix ι ι ℂ)
    (hSLD : ρ.matrix * H + H * ρ.matrix = (2 : ℂ) • D) (n : ℕ) :
    (TensorCopies.density ρ n).matrix * totalLift H n +
      totalLift H n * (TensorCopies.density ρ n).matrix =
        (2 : ℂ) • derivativeCopy ρ D n := by
  change TensorCopies.matrix ρ.matrix n * totalLift H n +
    totalLift H n * TensorCopies.matrix ρ.matrix n = _
  simp only [totalLift, Matrix.mul_sum, Matrix.sum_mul, copies_mul_lift, lift_mul_copies]
  rw [← Finset.sum_add_distrib]
  simp_rw [← slot_add, hSLD, slot_smul]
  exact Finset.smul_sum.symm

end Paper26.TensorSLD
