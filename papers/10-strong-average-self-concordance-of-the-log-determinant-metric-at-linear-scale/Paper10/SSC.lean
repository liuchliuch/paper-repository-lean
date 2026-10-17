import Paper10.Basic
import Paper10.FiniteSums
import Paper10.PairedTraces
import Paper10.Spectral
import Paper10.Symm
import Paper10.Metric
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Strong self-concordance and Proposition 4.1

Normalized derivative identity and the exact SSC threshold `s ≥ (q+1)/2`.
-/

noncomputable section

open Matrix

namespace Paper10

variable {q : ℕ}

/-- Super-operator `L_K(U) = -(K U + U K)`. -/
def anticomm (K U : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  -(K * U + U * K)

theorem anticomm_apply (K U : Matrix (Fin q) (Fin q) ℝ) :
    anticomm K U = -(K * U + U * K) := rfl

theorem anticomm_add (K U V : Matrix (Fin q) (Fin q) ℝ) :
    anticomm K (U + V) = anticomm K U + anticomm K V := by
  simp only [anticomm, Matrix.mul_add, Matrix.add_mul]
  abel

theorem anticomm_smul (K U : Matrix (Fin q) (Fin q) ℝ) (a : ℝ) :
    anticomm K (a • U) = a • anticomm K U := by
  simp only [anticomm, Matrix.mul_smul, Matrix.smul_mul, smul_neg, smul_add]

/-- Algebraic identity of Proposition 4.1:
`4∑k_i² + ∑_{i<j}(k_i+k_j)² = (q+2)∑k_i² + (∑k_i)²`. -/
theorem hsNormSq_anticomm_eq (q : ℕ) (k : Fin q → ℝ) :
    4 * ∑ i, k i ^ 2
      + ∑ p : {x : Fin q × Fin q // x.1 < x.2}, (k p.val.1 + k p.val.2) ^ 2
      = (q + 2 : ℝ) * (∑ i, k i ^ 2) + (∑ i, k i) ^ 2 := by
  have hu := twice_sum_upper (fun i j => (k i + k j) ^ 2) (by intros; ring)
  have hd : (∑ i, (k i + k i) ^ 2) = 4 * ∑ i, k i ^ 2 := by
    simp_rw [show ∀ x : ℝ, (x + x) ^ 2 = 4 * x ^ 2 by intro x; ring]
    rw [Finset.mul_sum]
  have hcross : (∑ i, ∑ j, 2 * k i * k j) = 2 * (∑ i, k i) ^ 2 := by
    calc
      _ = ∑ i, (2 * k i) * ∑ j, k j := by simp only [Finset.mul_sum]
      _ = (2 * ∑ i, k i) * ∑ j, k j := by rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = _ := by ring
  have hf : (∑ i, ∑ j, (k i + k j) ^ 2) =
      2 * (q : ℝ) * (∑ i, k i ^ 2) + 2 * (∑ i, k i) ^ 2 := by
    simp_rw [add_sq, Finset.sum_add_distrib]
    rw [hcross]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [hd, hf] at hu
  linarith

/-- Proposition 4.1 operator bound:
`(q+2)‖K‖² + (Tr K)² ≤ 2(q+1)‖K‖²` when `K` is diagonal with eigenvalues `k_i`,
via `(∑ k_i)² ≤ q ∑ k_i²`. -/
theorem prop_4_1_eigenvalue_bound (q : ℕ) (k : Fin q → ℝ) :
    (q + 2 : ℝ) * ∑ i, k i ^ 2 + (∑ i, k i) ^ 2
      ≤ 2 * (q + 1 : ℝ) * ∑ i, k i ^ 2 := by
  have h : (∑ i, k i) ^ 2 ≤ (q : ℝ) * ∑ i, k i ^ 2 := sum_sq_le q k
  have h2 : (q + 2 : ℝ) * ∑ i, k i ^ 2 + (∑ i, k i) ^ 2
      ≤ (q + 2 : ℝ) * ∑ i, k i ^ 2 + (q : ℝ) * ∑ i, k i ^ 2 := by
    exact add_le_add_left h _
  have h3 : (q + 2 : ℝ) * ∑ i, k i ^ 2 + (q : ℝ) * ∑ i, k i ^ 2
      = 2 * (q + 1 : ℝ) * ∑ i, k i ^ 2 := by
    ring
  linarith

/-- Equality case: for `k_i = 1/√q` the bound is tight. -/
theorem prop_4_1_op_bound_eq (q : ℕ) (hq : 0 < q) :
    (q + 2 : ℝ) * ∑ i : Fin q, (1 / Real.sqrt q) ^ 2
      + (∑ i : Fin q, (1 / Real.sqrt q)) ^ 2
      = 2 * (q + 1 : ℝ) * ∑ i : Fin q, (1 / Real.sqrt q) ^ 2 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- SSC threshold in scalar form: the inequality
`(q+2)r + t² ≤ 4 s r` for all `r ≥ 0`, `t` with `t² ≤ q r`
holds iff `s ≥ (q+1)/2`. -/
theorem ssc_threshold_scalar (q : ℕ) (s : ℝ) (hq : 0 < q) :
    (∀ r t : ℝ, 0 ≤ r → t ^ 2 ≤ (q : ℝ) * r →
      (q + 2 : ℝ) * r + t ^ 2 ≤ 4 * s * r)
      ↔ c q ≤ s := by
  constructor
  · intro h
    have h2 := h (q : ℝ) (q : ℝ) (Nat.cast_nonneg q) (by nlinarith)
    have h3 : (q + 2 : ℝ) * (q:ℝ) + (q:ℝ) ^ 2 = 2 * (q:ℝ) * ((q:ℝ) + 1) := by ring
    rw [h3] at h2
    have hq1 : ((q + 1 : ℕ) : ℝ) = (q:ℝ) + 1 := by norm_cast
    have h7 : 0 < (q:ℝ) := by exact_mod_cast hq
    have h8 : (2:ℝ) * ((q:ℝ) + 1) ≤ 4 * s := by nlinarith [h2]
    have h9 : ((q + 1 : ℕ) : ℝ) / 2 ≤ s := by rw [hq1]; linarith
    simpa [c_eq] using h9
  · intro hs r t hr ht
    have h1 : (q + 2 : ℝ) * r + t ^ 2
        ≤ (q + 2 : ℝ) * r + (q : ℝ) * r := by
      exact add_le_add_left ht _
    have h2 : (q + 2 : ℝ) * r + (q : ℝ) * r = 2 * (q + 1 : ℝ) * r := by ring
    have hq1 : ((q + 1 : ℕ) : ℝ) = (q:ℝ) + 1 := by norm_cast
    have h3 : (2 * (q + 1 : ℝ) : ℝ) ≤ 4 * s := by
      have : c q = ((q + 1 : ℕ) : ℝ) / 2 := c_eq q
      rw [this, hq1] at hs
      field_simp at hs
      linarith
    nlinarith [h1, h2, h3, hr]

/-- Trace Cauchy–Schwarz for real symmetric matrices. -/
theorem trace_sq_le_frob (K : Matrix (Fin q) (Fin q) ℝ) (hK : K.IsSymm) :
    (Matrix.trace K) ^ 2 ≤ (q : ℝ) * frobNormSq K := by
  have hd : (∑ i, K i i ^ 2) ≤ frobNormSq K := by
    unfold frobNormSq
    rw [frob_of_isSymm hK]
    apply Finset.sum_le_sum
    intro i _
    calc K i i ^ 2 = K i i * K i i := sq _
      _ ≤ ∑ j, K i j * K i j :=
        Finset.single_le_sum (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
  exact (sum_sq_le q (fun i => K i i)).trans
    (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg q))

/-- The sharp upper bound in Proposition 4.1. -/
theorem prop_4_1_op_bound (K : Matrix (Fin q) (Fin q) ℝ) (hK : K.IsSymm) :
    (q + 2 : ℝ) * frobNormSq K + (Matrix.trace K) ^ 2
      ≤ 2 * (q + 1 : ℝ) * frobNormSq K := by
  have := trace_sq_le_frob K hK
  linarith

/-- Exact threshold for the normalized derivative inequality; the matrix order is positive. -/
theorem ssc_threshold_iff (q : ℕ) (s : ℝ) (hq : 0 < q) (hs : 0 < s) :
    (∀ K : Matrix (Fin q) (Fin q) ℝ, K.IsSymm →
      (q + 2 : ℝ) * frobNormSq K + (Matrix.trace K) ^ 2 ≤ 4 * s * frobNormSq K)
      ↔ c q ≤ s := by
  constructor
  · intro h
    have hh := h 1 (by exact Matrix.transpose_one)
    simp only [frobNormSq, frob, Matrix.one_mul, Matrix.trace_one, Fintype.card_fin] at hh
    have hqp : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    simp only [c, Nat.cast_add, Nat.cast_one]
    nlinarith
  · intro h K hK
    have hb := prop_4_1_op_bound K hK
    have hn := frobNormSq_nonneg hK
    have hc : 2 * (q + 1 : ℝ) ≤ 4 * s := by
      have : ((q : ℝ) + 1) / 2 ≤ s := by simpa [c] using h
      linarith
    nlinarith

/-- `|Tr(K³)| ≤ ‖K‖_F³`. -/
theorem trace_cube_le_frob (q : ℕ) (K : Matrix (Fin q) (Fin q) ℝ) (hK : K.IsSymm) :
    |Matrix.trace (K * K * K)| ≤ (frobNormSq K) ^ (3 / 2 : ℝ) := by
  have h2 := trace_pow_spectral K hK 2
  have h3 := trace_pow_spectral K hK 3
  have hnorm : frobNormSq K = ∑ i, ((real_isHermitian hK).eigenvalues i) ^ 2 := by
    simpa [frobNormSq, frob, pow_two] using h2
  rw [hnorm]
  rw [show K * K * K = K ^ 3 by simp [pow_succ, pow_two], h3]
  exact abs_sum_cube_le _

/-- Ordinary self-concordance at scales `s ≥ c_q`. -/
theorem ordinary_sc {q : ℕ} (K : Matrix (Fin q) (Fin q) ℝ) (hK : K.IsSymm)
    {s : ℝ} (hs : c q ≤ s) (hq : 0 < q) :
    |2 * s * Matrix.trace (K * K * K)|
      ≤ 2 * (s * frobNormSq K) ^ (3 / 2 : ℝ) := by
  have hs1 := (one_le_c hq).trans hs
  have hs0 : 0 ≤ s := by linarith
  have hn := frobNormSq_nonneg hK
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * s), Real.mul_rpow hs0 hn]
  have hc := trace_cube_le_frob q K hK
  have hpow : s ≤ s ^ (3 / 2 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have hnn := Real.rpow_nonneg hn (3 / 2 : ℝ)
  nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * s),
    mul_le_mul_of_nonneg_right hpow hnn]

/-- Main SSC consequence. -/
theorem g_s_ssc_iff (q : ℕ) (s : ℝ) (hq : 0 < q) (hs : 0 < s) :
    (∀ K : Matrix (Fin q) (Fin q) ℝ, K.IsSymm →
      (q + 2 : ℝ) * frobNormSq K + (Matrix.trace K) ^ 2 ≤ 4 * s * frobNormSq K)
      ↔ c q ≤ s :=
  ssc_threshold_iff q s hq hs

/-- Hilbert–Schmidt norm squared of the anticommutator in an orthonormal symmetric basis. -/
def hsNormSqAnticomm {ι : Type*} [Fintype ι]
    (F : ι → Matrix (Fin q) (Fin q) ℝ) (K : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  ∑ a, frobNormSq (anticomm K (F a))

/-- Cyclic rotation of a four-factor matrix trace. -/
theorem trace_four_cycle (A B C D : Matrix (Fin q) (Fin q) ℝ) :
    Matrix.trace (A * B * C * D) = Matrix.trace (D * A * B * C) := by
  rw [Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]

/-- The exact Hilbert–Schmidt identity in Proposition 4.1, on the full symmetric space. -/
theorem hsNormSqAnticomm_eq {ι : Type*} [Fintype ι]
    (F : ι → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F)
    (K : Matrix (Fin q) (Fin q) ℝ) (hK : K.IsSymm) :
    hsNormSqAnticomm F K = (q + 2 : ℝ) * frobNormSq K + (Matrix.trace K) ^ 2 := by
  have hterm : ∀ a, frobNormSq (anticomm K (F a)) =
      2 * Matrix.trace (K * K * F a * F a) + 2 * Matrix.trace (K * F a * K * F a) := by
    intro a
    have h1 := trace_four_cycle K (F a) (F a) K
    have h2 : Matrix.trace (F a * K * K * F a) = Matrix.trace (K * K * F a * F a) := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (F a) (K * K * F a)
    have h3 := trace_four_cycle (F a) K (F a) K
    simp only [frobNormSq, frob, anticomm, neg_mul_neg, Matrix.add_mul, Matrix.mul_add,
      Matrix.trace_add]
    simp only [← Matrix.mul_assoc]
    rw [h1, h2, h3]
    ring
  have hsum1 : (∑ a, Matrix.trace (K * K * F a * F a)) = c q * frobNormSq K := by
    calc
      _ = Matrix.trace (K * K * (∑ a, F a * F a)) := by
        simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
      _ = _ := by rw [sum_squares_orthonormal F hF]; simp [oneMat, frobNormSq, frob]
  have hsum2 : (∑ a, Matrix.trace (K * F a * K * F a)) =
      (frobNormSq K + (Matrix.trace K) ^ 2) / 2 := by
    calc
      _ = Matrix.trace (K * ∑ a, F a * K * F a) := by
        simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
      _ = _ := by
        rw [sum_FUF F hF K]
        simp only [hK, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, Matrix.trace_smul,
          Matrix.trace_add, smul_eq_mul, frobNormSq, frob]
        rw [show Kᵀ = K from hK]
        ring
  unfold hsNormSqAnticomm
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum1, hsum2]
  simp only [c, Nat.cast_add, Nat.cast_one]
  ring

end Paper10
