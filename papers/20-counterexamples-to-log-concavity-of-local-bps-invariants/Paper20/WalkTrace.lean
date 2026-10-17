import Mathlib
import Verification.Objects

/-! The combinatorial side of (22), using actual words in a finite group.
The count is related to a group-algebra power and the ordinary regular
representation trace before any representation-theoretic spectral formula
is invoked. -/
namespace Paper20.WalkTrace
open Finset
noncomputable section
set_option maxHeartbeats 2000000

variable {G I : Type*} [Group G] [Fintype I]

def wordProduct (s : I → G) {n : ℕ} (w : Fin n → I) : G :=
  (List.ofFn (fun i => s (w i))).prod

def generator (s : I → G) : MonoidAlgebra ℚ G :=
  ∑ i, MonoidAlgebra.single (s i) 1

lemma wordProduct_cons (s : I → G) (i : I) {n : ℕ} (w : Fin n → I) :
    wordProduct s (Fin.cons i w) = s i*wordProduct s w := by
  simp [wordProduct, List.ofFn_succ]

theorem generator_pow (s : I → G) (n : ℕ) :
    generator s^n = ∑ w : Fin n → I, MonoidAlgebra.single (wordProduct s w) 1 := by
  classical
  induction n with
  | zero => simp [wordProduct, MonoidAlgebra.one_def]
  | succ n ih =>
    rw [pow_succ', ih]
    unfold generator
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, MonoidAlgebra.single_mul_single, mul_one]
    have he := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => I))
      (fun p : I × (Fin n → I) =>
        (MonoidAlgebra.single (s p.1*wordProduct s p.2) 1 : MonoidAlgebra ℚ G))
      (fun w => MonoidAlgebra.single (wordProduct s w) 1)
      (by intro p; simp [Fin.consEquiv, wordProduct_cons])
    rw [Fintype.sum_prod_type] at he
    exact he

def returnCount (s : I → G) (n : ℕ) : ℕ :=
  Nat.card {w : Fin n → I // wordProduct s w = 1}

/-- The identity coefficient counts the actual ordered return words. -/
theorem generator_pow_identity (s : I → G) (n : ℕ) :
    (generator s^n) 1 = (returnCount s n : ℚ) := by
  classical
  rw [generator_pow, Finsupp.finset_sum_apply]
  simp only [MonoidAlgebra.single, Finsupp.single_apply]
  unfold returnCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]

variable [Fintype G] [DecidableEq G]

/-- Matrix of left multiplication in the actual group-element basis. -/
def regularMatrix (a : MonoidAlgebra ℚ G) : Matrix G G ℚ :=
  fun i j => a (i*j⁻¹)

@[simp] theorem regularMatrix_one : regularMatrix (1 : MonoidAlgebra ℚ G) = 1 := by
  classical
  ext i j
  simp [regularMatrix, MonoidAlgebra.one_def, MonoidAlgebra.single,
    Finsupp.single_apply, Matrix.one_apply, mul_inv_eq_one, eq_comm]

theorem regularMatrix_mul (a b : MonoidAlgebra ℚ G) :
    regularMatrix (a*b) = regularMatrix a*regularMatrix b := by
  classical
  ext i j
  change (a*b) (i*j⁻¹) = ∑ k, a (i*k⁻¹)*b (k*j⁻¹)
  rw [MonoidAlgebra.mul_apply_left, Finsupp.sum_fintype _ _ (by intro; simp)]
  let e : G ≃ G :=
    { toFun := fun g => g⁻¹*i
      invFun := fun k => i*k⁻¹
      left_inv := by intro g; simp [mul_inv_rev, mul_assoc]
      right_inv := by intro k; simp [mul_inv_rev, mul_assoc] }
  apply Fintype.sum_equiv e
  intro g
  simp [e, mul_inv_rev, mul_assoc]

theorem regularMatrix_pow (a : MonoidAlgebra ℚ G) (n : ℕ) :
    regularMatrix (a^n) = regularMatrix a^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, regularMatrix_mul, ih, pow_succ]

theorem regular_trace (a : MonoidAlgebra ℚ G) :
    Matrix.trace (regularMatrix a) = (Fintype.card G : ℚ)*a 1 := by
  simp [Matrix.trace, Matrix.diag, regularMatrix]

/-- Return counts are normalized regular traces of generator powers. -/
theorem returnCount_eq_normalized_trace (s : I → G) (n : ℕ) :
    (returnCount s n : ℚ) = Matrix.trace (regularMatrix (generator s^n)) /
      (Fintype.card G : ℚ) := by
  rw [regular_trace, generator_pow_identity]
  have hn : (Fintype.card G : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

def transpositionSum (r : ℕ) : MonoidAlgebra ℚ (Equiv.Perm (Fin r)) :=
  by
    classical
    exact generator (fun σ : P20Objects.Transposition r => σ.val)

/-- Equation (22)'s walk count, with the independently specified actual
transpositions and ordered return condition. -/
theorem transpositionReturns_eq_identity_coeff (r h : ℕ) :
    (P20Objects.transpositionReturns r h : ℚ) = (transpositionSum r^(2*h)) 1 := by
  classical
  exact (generator_pow_identity (fun σ : P20Objects.Transposition r => σ.val) (2*h)).symm

theorem transpositionReturns_eq_regular_trace (r h : ℕ) :
    (P20Objects.transpositionReturns r h : ℚ) =
      Matrix.trace (regularMatrix (transpositionSum r^(2*h))) / (r.factorial:ℚ) := by
  classical
  have he := returnCount_eq_normalized_trace
    (fun σ : P20Objects.Transposition r => σ.val) (2*h)
  simpa only [Fintype.card_perm, Fintype.card_fin, returnCount, wordProduct,
    P20Objects.transpositionReturns, transpositionSum] using he

theorem transpositionReturns_eq_matrix_moment (r h : ℕ) :
    (P20Objects.transpositionReturns r h : ℚ) =
      Matrix.trace (regularMatrix (transpositionSum r)^(2*h)) / (r.factorial:ℚ) := by
  rw [← regularMatrix_pow]
  exact transpositionReturns_eq_regular_trace r h

end
end Paper20.WalkTrace
