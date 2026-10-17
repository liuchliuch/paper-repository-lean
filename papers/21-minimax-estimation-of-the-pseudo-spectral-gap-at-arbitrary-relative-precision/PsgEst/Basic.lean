import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Finite-state Markov chains and the pseudo-spectral gap

Definitions matching Sections 1–2 of the paper:
row-stochastic transition matrices on `Fin d`, stationary laws, `D_mu`, `Π`,
similarity transform `L_k`, singular-value deficit `a_k`, and Paulin's
pseudo-spectral gap `γ_ps = sup_k a_k / k`.
-/

open Matrix BigOperators Real

namespace PsgEst

variable {d : ℕ}

/-- Row-stochastic transition matrix on `Fin d`. -/
structure Stoch (d : ℕ) where
  P : Matrix (Fin d) (Fin d) ℝ
  nonneg : ∀ i j, 0 ≤ P i j
  row_stoch : ∀ i, ∑ j, P i j = 1

namespace Stoch

lemma entry_mul_nonneg {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) (i j : Fin d) :
    0 ≤ (A * B) i j := by
  change 0 ≤ (∑ k, A i k * B k j)
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hA i k) (hB k j)

lemma one_entry (i j : Fin d) :
    (1 : Matrix (Fin d) (Fin d) ℝ) i j = if i = j then (1 : ℝ) else 0 :=
  Matrix.one_apply (i := i) (j := j)

lemma pow_nonneg (S : Stoch d) : ∀ k i j, 0 ≤ (S.P ^ k) i j := by
  intro k
  induction k with
  | zero =>
    intro i j
    rw [pow_zero, one_entry]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  | succ k ih =>
    intro i j
    rw [pow_succ']
    exact entry_mul_nonneg S.nonneg ih i j

lemma pow_row_stoch (S : Stoch d) : ∀ k i, ∑ j, (S.P ^ k) i j = 1 := by
  intro k
  induction k with
  | zero =>
    intro i
    classical
    rw [pow_zero]
    have h : ∑ j : Fin d, (1 : Matrix (Fin d) (Fin d) ℝ) i j
        = ∑ j : Fin d, (if j = i then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [one_entry]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij.symm]
      · rw [if_neg hij, if_neg (Ne.symm hij)]
    rw [h, Finset.sum_ite_eq']
    simp
  | succ k ih =>
    intro i
    have hmul : ∀ j, (S.P ^ (k + 1)) i j = ∑ j', S.P i j' * (S.P ^ k) j' j := by
      intro j
      rw [pow_succ', Matrix.mul_apply]
    calc ∑ j, (S.P ^ (k + 1)) i j
        = ∑ j, ∑ j', S.P i j' * (S.P ^ k) j' j := Finset.sum_congr rfl (fun j _ => hmul j)
      _ = ∑ j', ∑ j, S.P i j' * (S.P ^ k) j' j := Finset.sum_comm
      _ = ∑ j', S.P i j' * ∑ j, (S.P ^ k) j' j := by simp_rw [Finset.mul_sum]
      _ = ∑ j', S.P i j' * 1 := by simp_rw [ih]
      _ = ∑ j', S.P i j' := by simp_rw [mul_one]
      _ = 1 := S.row_stoch i

/-- Matrix power is again row-stochastic. -/
noncomputable def pow (S : Stoch d) (k : ℕ) : Stoch d where
  P := S.P ^ k
  nonneg := S.pow_nonneg k
  row_stoch := S.pow_row_stoch k

end Stoch

/-- Stationary law: positive probability vector, total mass one, `mu P = mu`. -/
structure Stationary {d : ℕ} (S : Stoch d) where
  mu : Fin d → ℝ
  pos : ∀ i, 0 < mu i
  sum_one : ∑ i, mu i = 1
  station : ∀ j, ∑ i, mu i * S.P i j = mu j

namespace Stationary

variable {S : Stoch d}

lemma nonneg (st : Stationary S) (i : Fin d) : 0 ≤ st.mu i := le_of_lt (st.pos i)

lemma sum_one' (st : Stationary S) : ∑ i, st.mu i = 1 := st.sum_one

/-- Minimum stationary mass `π_⋆ = min i, mu i`. -/
noncomputable def star [NeZero d] (st : Stationary S) : ℝ :=
  (Finset.univ : Finset (Fin d)).inf' Finset.univ_nonempty st.mu

lemma star_le [NeZero d] (st : Stationary S) (i : Fin d) : star st ≤ st.mu i :=
  Finset.inf'_le (f := (st.mu : Fin d → ℝ)) (Finset.mem_univ i)

lemma star_pos [NeZero d] (st : Stationary S) : 0 < star st := by
  obtain ⟨i, -, himin⟩ := Finset.exists_min_image
    (s := (Finset.univ : Finset (Fin d))) (f := st.mu) Finset.univ_nonempty
  have h2 : star st = st.mu i := by
    apply le_antisymm
    · exact star_le st i
    · exact Finset.le_inf' Finset.univ_nonempty (st.mu : Fin d → ℝ)
        (fun j _ => himin j (Finset.mem_univ j))
  rw [h2]
  exact st.pos i

lemma star_le_all [NeZero d] (st : Stationary S) (i : Fin d) : star st ≤ st.mu i := star_le st i

end Stationary

/-- Diagonal matrix `D_mu`. -/
def dpi {d : ℕ} (mu : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ := diagonal mu

/-- Rank-one matrix `Π = 1 mu` (orthogonal projection onto constants in the `mu` inner product). -/
def piMat {d : ℕ} (mu : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ := fun _ j => mu j

/-- Similarity transform `L = D_mu^{1/2} P D_mu^{-1/2}`. -/
noncomputable def simil {d : ℕ} (mu : Fin d → ℝ) (P : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  diagonal (fun i => (mu i) ^ (1 / 2 : ℝ)) * P * diagonal (fun i => (mu i) ^ (-(1 / 2 : ℝ)))

/-- Componentwise square root of a vector. -/
noncomputable def vecSqrt {d : ℕ} (v : Fin d → ℝ) : Fin d → ℝ := fun i => (v i) ^ (1 / 2 : ℝ)

/-- `L_k = D_mu^{1/2} P^k D_mu^{-1/2}`. -/
noncomputable def Lk {d : ℕ} (S : Stoch d) (st : Stationary S) (k : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  simil st.mu (S.P ^ k)

/-- Gram matrix `Lᵀ L`, whose eigenvalues are the squared singular values. -/
def gram (L : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ := L.transpose * L

lemma gram_isHermitian (L : Matrix (Fin d) (Fin d) ℝ) : (gram L).IsHermitian := by
  have h : ((L : Matrix (Fin d) (Fin d) ℝ)ᴴ * L).IsHermitian :=
    isHermitian_transpose_mul_self L
  have key : (L : Matrix (Fin d) (Fin d) ℝ)ᴴ = L.transpose := by
    ext i j
    simp [Matrix.conjTranspose]
  rwa [key] at h

/-- `j`-th eigenvalue of the Gram matrix via `IsHermitian.eigenvalues`
(note: the indexing is not guaranteed sorted; use `gramEig₀` for the sorted list). -/
noncomputable def gramEig (L : Matrix (Fin d) (Fin d) ℝ) [DecidableEq (Fin d)] (j : Fin d) : ℝ :=
  (gram_isHermitian L).eigenvalues j

/-- Sorted (decreasing) Gram eigenvalues via `IsHermitian.eigenvalues₀`. -/
noncomputable def gramEig₀ (L : Matrix (Fin d) (Fin d) ℝ) [DecidableEq (Fin d)]
    (j : Fin (Fintype.card (Fin d))) : ℝ :=
  (gram_isHermitian L).eigenvalues₀ j

/-- Singular values via the (unsorted) Gram eigenvalues, nonnegative. -/
noncomputable def sval (L : Matrix (Fin d) (Fin d) ℝ) [DecidableEq (Fin d)] (j : Fin d) : ℝ :=
  Real.sqrt (max 0 (gramEig L j))

/-- Second singular value `σ_2` from the sorted Gram spectrum (index `1` when `d ≥ 2`). -/
noncomputable def sigma2 (L : Matrix (Fin d) (Fin d) ℝ) [DecidableEq (Fin d)] : ℝ :=
  if h : 1 < d then
    Real.sqrt (max 0 (gramEig₀ L ⟨1, by rw [Fintype.card_fin]; exact h⟩))
  else 0

/-- Spectral deficit `a = 1 - σ_2(L)^2`. -/
noncomputable def aOf (L : Matrix (Fin d) (Fin d) ℝ) [DecidableEq (Fin d)] : ℝ :=
  1 - (sigma2 L) ^ 2

/-- `a_k = 1 - σ_2(D_mu^{1/2} P^k D_mu^{-1/2})^2`. -/
noncomputable def aK {d : ℕ} [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S)
    (k : ℕ) : ℝ :=
  aOf (Lk S st k)

/-- Paulin pseudo-spectral gap `γ_ps = ⨆_{k≥1} a_k / k`. -/
noncomputable def gammaPS {d : ℕ} [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S) : ℝ :=
  ⨆ k : ℕ, if 0 < k then aK S st k / k else 0

/-- Ergodicity package: stationary law with full support and positive pseudo-spectral gap.
The paper assumes irreducible + aperiodic, which for finite chains yields `0 < γ_ps ≤ 1`
and `P^k → Π`.  We package the properties actually used. -/
structure Ergodic (d : ℕ) [DecidableEq (Fin d)] where
  S : Stoch d
  st : Stationary S
  gap_pos : 0 < gammaPS S st
  gap_le_one : gammaPS S st ≤ 1

end PsgEst
