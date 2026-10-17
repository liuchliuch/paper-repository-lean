import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Core notation for the log-determinant metric at linear scale

We work with real symmetric `q x q` matrices. The ambient dimension is
`n = q(q+1)/2` and `c_q = (q+1)/2`, so that `n = q * c_q`.
-/

noncomputable section

open Matrix

namespace Paper10

/-- Ambient dimension of the space of real symmetric `q x q` matrices. -/
def n (q : ℕ) : ℕ := q * (q + 1) / 2

/-- Half-integer scale parameter `c_q = (q+1)/2`. -/
def c (q : ℕ) : ℝ := ((q + 1 : ℕ) : ℝ) / 2

@[simp]
theorem c_eq (q : ℕ) : c q = ((q + 1 : ℕ) : ℝ) / 2 := rfl

theorem n_eq (q : ℕ) : n q = q * (q + 1) / 2 := rfl

theorem even_mul_succ (q : ℕ) : Even (q * (q + 1)) :=
  Nat.even_mul_succ_self q

theorem two_dvd_mul_succ (q : ℕ) : 2 ∣ q * (q + 1) :=
  even_iff_two_dvd.mp (even_mul_succ q)

theorem n_mul_c (q : ℕ) : ((n q : ℕ) : ℝ) = (q : ℝ) * c q := by
  have hdiv := two_dvd_mul_succ q
  have hcast : ((q * (q + 1) / 2 : ℕ) : ℝ) = (q : ℝ) * ((q + 1 : ℕ) : ℝ) / 2 := by
    rw [Nat.cast_div hdiv (by norm_num : ((2:ℕ):ℝ) ≠ 0)]
    push_cast
    ring
  rw [n_eq, hcast, c]
  field_simp

theorem c_pos (q : ℕ) : 0 < c q := by
  unfold c
  have : (0:ℝ) < ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos q
  positivity

theorem one_le_c {q : ℕ} (hq : 0 < q) : 1 ≤ c q := by
  have h2 : (2:ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
    have : (2:ℕ) ≤ q + 1 := by omega
    exact_mod_cast this
  show (1:ℝ) ≤ ((q + 1 : ℕ) : ℝ) / 2
  linarith

theorem n_pos {q : ℕ} (hq : 0 < q) : 0 < n q := by
  obtain ⟨k, hk⟩ := two_dvd_mul_succ q
  have hk2 : 1 ≤ k := by
    have h : 2 ≤ q * (q + 1) := by
      have h1 : 1 ≤ q := hq
      have h2 : q * (q + 1) = q * q + q := by ring
      nlinarith
    omega
  have : 0 < q * (q + 1) / 2 := by
    have : q * (q + 1) / 2 = k := by omega
    omega
  simpa [n_eq] using this

/-- Frobenius inner product, defined as `trace(U * V)`. -/
def frob {q : ℕ} (U V : Matrix (Fin q) (Fin q) ℝ) : ℝ := Matrix.trace (U * V)

theorem frob_eq_sum {q : ℕ} (U V : Matrix (Fin q) (Fin q) ℝ) :
    frob U V = ∑ i, ∑ j, U i j * V j i := by
  simp only [frob, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

theorem frob_of_isSymm {q : ℕ} {U V : Matrix (Fin q) (Fin q) ℝ}
    (hV : V.IsSymm) : frob U V = ∑ i, ∑ j, U i j * V i j := by
  rw [frob_eq_sum]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by rw [← Matrix.IsSymm.apply hV j i]

/-- Squared Frobenius norm. -/
def frobNormSq {q : ℕ} (U : Matrix (Fin q) (Fin q) ℝ) : ℝ := frob U U

theorem frobNormSq_eq {q : ℕ} (U : Matrix (Fin q) (Fin q) ℝ) :
    frobNormSq U = Matrix.trace (U * U) := rfl

theorem frobNormSq_eq_sum {q : ℕ} (U : Matrix (Fin q) (Fin q) ℝ) :
    frobNormSq U = ∑ i, ∑ j, U i j * U j i :=
  frob_eq_sum U U

theorem frobNormSq_nonneg {q : ℕ} {U : Matrix (Fin q) (Fin q) ℝ} (hU : U.IsSymm) :
    0 ≤ frobNormSq U := by
  have h := frob_of_isSymm (q := q) (U := U) (V := U) hU
  rw [frobNormSq, h]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

/-- Diagonal matrix unit `E_{ii}`. -/
def eii {q : ℕ} (i : Fin q) : Matrix (Fin q) (Fin q) ℝ :=
  fun a b => if a = i ∧ b = i then 1 else 0

/-- Symmetrized off-diagonal unit `(E_{ij} + E_{ji})/sqrt 2`. -/
def eijSymm {q : ℕ} (i j : Fin q) : Matrix (Fin q) (Fin q) ℝ :=
  fun a b => if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then 1 / Real.sqrt 2 else 0

theorem eii_isymm {q : ℕ} (i : Fin q) : (eii i).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  simp only [eii]
  by_cases ha : a = i <;> by_cases hb : b = i <;> simp [ha, hb, and_comm]

theorem eijSymm_isymm {q : ℕ} (i j : Fin q) : (eijSymm i j).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  simp only [eijSymm]
  by_cases ha : a = i <;> by_cases hb : b = j <;>
    by_cases ha' : a = j <;> by_cases hb' : b = i <;>
    simp [ha, hb, ha', hb', or_comm, and_comm]

/-- The identity matrix as a real matrix. -/
def oneMat (q : ℕ) : Matrix (Fin q) (Fin q) ℝ := 1

theorem oneMat_isymm (q : ℕ) : (oneMat q).IsSymm := by
  rw [oneMat, Matrix.IsSymm]
  exact Matrix.transpose_one

end Paper10
