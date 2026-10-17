import Paper10.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.StarOrdered

/-!
# Lemma 2.3 (Paired traces)

If `B := sum_a B_a^2` and `Psi - B` is PSD (with `Psi` PSD), then
  `sum_{a,b} |Tr(B_a B_b B_a B_b)| <= Tr(B^2) <= Tr(Psi^2)`.
-/

noncomputable section

open Matrix

namespace Paper10

variable {q : ℕ}

theorem star_eq_conjTranspose_real (A : Matrix (Fin q) (Fin q) ℝ) : star A = Aᴴ := rfl

theorem conjTranspose_eq_transpose_real (A : Matrix (Fin q) (Fin q) ℝ) : Aᴴ = Aᵀ :=
  Matrix.conjTranspose_eq_transpose_of_trivial A

theorem trace_transpose_mul_eq_sum (A B : Matrix (Fin q) (Fin q) ℝ) :
    Matrix.trace (Aᵀ * B) = ∑ i, ∑ j, A i j * B i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem sum_sq_eq_trace_transpose_mul (A : Matrix (Fin q) (Fin q) ℝ) :
    ∑ i, ∑ j, A i j ^ 2 = Matrix.trace (Aᵀ * A) := by
  have h : (∑ i, ∑ j, A i j ^ 2) = (∑ i, ∑ j, A i j * A i j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h, trace_transpose_mul_eq_sum]

theorem sum_sum_eq_sum_prod (f : Fin q → Fin q → ℝ) :
    ∑ i, ∑ j, f i j = ∑ p : Fin q × Fin q, f p.1 p.2 := by
  rw [← Finset.univ_product_univ]
  exact (Finset.sum_product Finset.univ Finset.univ
    (fun p : Fin q × Fin q => f p.1 p.2)).symm

theorem congruence_diag (U N : Matrix (Fin q) (Fin q) ℝ) (i : Fin q) :
    (Uᵀ * N * U) i i = (fun k => U k i) ⬝ᵥ (N *ᵥ fun k => U k i) := by
  show (Uᵀ * N * U) i i = ∑ j, U j i * (∑ k, N j k * U k i)
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hstep : (∑ x, (∑ y, U y i * N y x) * U x i)
      = ∑ x, ∑ y, U y i * (N y x * U x i) := by
    apply Finset.sum_congr rfl
    intro x _
    have hinner : (∑ y, U y i * N y x) * U x i
        = ∑ y, (U y i * N y x) * U x i :=
      Finset.sum_mul Finset.univ (fun y => U y i * N y x) (U x i)
    rw [hinner]
    apply Finset.sum_congr rfl
    intro y _
    exact mul_assoc _ _ _
  rw [hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hR : U j i * (∑ k, N j k * U k i)
      = ∑ k, U j i * (N j k * U k i) :=
    Finset.mul_sum Finset.univ (fun k => N j k * U k i) (U j i)
  rw [hR]

theorem trace_diagonal_mul (d : Fin q → ℝ) (X : Matrix (Fin q) (Fin q) ℝ) :
    Matrix.trace (diagonal d * X) = ∑ i, d i * X i i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg (fun h => hb (id h.symm)), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem trace_transpose_mul_self_nonneg (N A : Matrix (Fin q) (Fin q) ℝ)
    (hN : N.PosSemidef) : 0 ≤ Matrix.trace (Aᵀ * N * A) := by
  have h := hN.conjTranspose_mul_mul_same A
  have htr : 0 ≤ Matrix.trace (Aᴴ * N * A) := h.trace_nonneg
  rwa [conjTranspose_eq_transpose_real] at htr

theorem trace_mul_nonneg {M N : Matrix (Fin q) (Fin q) ℝ}
    (hM : M.PosSemidef) (hN : N.PosSemidef) :
    0 ≤ Matrix.trace (M * N) := by
  classical
  have hMh : M.IsHermitian := hM.isHermitian
  set U : Matrix (Fin q) (Fin q) ℝ := (hMh.eigenvectorUnitary : Matrix (Fin q) (Fin q) ℝ)
    with hUdef
  set μ : Fin q → ℝ := hMh.eigenvalues with hμdef
  set D : Matrix (Fin q) (Fin q) ℝ := diagonal μ with hDdef
  have hMD : M = U * D * Uᵀ := by
    rw [hMh.spectral_theorem]
    rw [hUdef, hDdef, hμdef]
    congr! 2
  have key : Matrix.trace (M * N) = ∑ i, μ i * ((Uᵀ * N * U) i i) := by
    rw [hMD]
    have h1 : (U * D * Uᵀ) * N = U * (D * (Uᵀ * N)) := by
      simp only [Matrix.mul_assoc]
    rw [h1, Matrix.trace_mul_comm]
    have h2 : (D * (Uᵀ * N)) * U = D * (Uᵀ * N * U) := by
      simp only [Matrix.mul_assoc]
    rw [h2, hDdef, trace_diagonal_mul]
  rw [key]
  refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ ?_
  · rw [hμdef]
    exact hM.eigenvalues_nonneg i
  · have hq : (Uᵀ * N * U) i i
        = (fun k => U k i) ⬝ᵥ (N *ᵥ fun k => U k i) := congruence_diag U N i
    rw [hq]
    exact hN.2 _

/-! ## Frobenius Cauchy-Schwarz -/

theorem frob_cs_UVUV {U V : Matrix (Fin q) (Fin q) ℝ}
    (hU : U.IsSymm) (hV : V.IsSymm) :
    |Matrix.trace (U * V * U * V)| ≤ Matrix.trace (U * U * V * V) := by
  have hVU : (V * U)ᵀ = U * V := by
    rw [Matrix.transpose_mul, hU, hV]
  have h1 : Matrix.trace (U * V * U * V)
      = Matrix.trace ((V * U)ᵀ * (U * V)) := by
    rw [hVU]
    simp only [Matrix.mul_assoc]
  have hUV : ∑ i, ∑ j, (U * V) i j ^ 2 = Matrix.trace ((U * U) * V * V) := by
    rw [sum_sq_eq_trace_transpose_mul]
    have heq : (U * V)ᵀ * (U * V) = V * (U * U) * V := by
      rw [Matrix.transpose_mul, hV, hU]
      simp only [Matrix.mul_assoc]
    rw [heq]
    exact (Matrix.trace_mul_cycle (U * U) V V).symm
  have hVU2 : ∑ i, ∑ j, (V * U) i j ^ 2 = Matrix.trace ((U * U) * V * V) := by
    rw [sum_sq_eq_trace_transpose_mul]
    have heq : (V * U)ᵀ * (V * U) = U * (V * V) * U := by
      rw [Matrix.transpose_mul, hU, hV]
      simp only [Matrix.mul_assoc]
    rw [heq]
    have hcy : Matrix.trace (U * (V * V) * U) = Matrix.trace ((U * U) * V * V) := by
      have e1 : U * (V * V) * U = (U * (V * V)) * U := rfl
      have e2 : (U * U) * V * V = (U * U) * (V * V) := Matrix.mul_assoc _ _ _
      rw [e1, e2, Matrix.trace_mul_comm]
      congr 1
      rw [← Matrix.mul_assoc]
    exact hcy
  have hcs : (∑ p : Fin q × Fin q, (V * U) p.1 p.2 * (U * V) p.1 p.2) ^ 2
      ≤ (∑ p : Fin q × Fin q, (V * U) p.1 p.2 ^ 2)
        * ∑ p : Fin q × Fin q, (U * V) p.1 p.2 ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h1' : Matrix.trace (U * V * U * V)
      = ∑ p : Fin q × Fin q, (V * U) p.1 p.2 * (U * V) p.1 p.2 := by
    rw [h1, trace_transpose_mul_eq_sum]
    exact sum_sum_eq_sum_prod _
  have hUV' : ∑ p : Fin q × Fin q, (U * V) p.1 p.2 ^ 2
      = Matrix.trace ((U * U) * V * V) := by
    have h := (sum_sum_eq_sum_prod fun i j => (U * V) i j ^ 2).symm
    rw [h, hUV]
  have hVU' : ∑ p : Fin q × Fin q, (V * U) p.1 p.2 ^ 2
      = Matrix.trace ((U * U) * V * V) := by
    have h := (sum_sum_eq_sum_prod fun i j => (V * U) i j ^ 2).symm
    rw [h, hVU2]
  rw [hUV', hVU'] at hcs
  have hT : 0 ≤ Matrix.trace ((U * U) * V * V) := by
    rw [← hUV]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsq : (Matrix.trace (U * V * U * V)) ^ 2
      ≤ (Matrix.trace ((U * U) * V * V)) ^ 2 := by
    rw [h1']
    have hs : (∑ p : Fin q × Fin q, (V * U) p.1 p.2 * (U * V) p.1 p.2) ^ 2
        = (∑ p : Fin q × Fin q, (V * U) p.1 p.2 * (U * V) p.1 p.2)
          * (∑ p : Fin q × Fin q, (V * U) p.1 p.2 * (U * V) p.1 p.2) := sq _
    rw [hs, sq]
    have hcs' : (∑ p : Fin q × Fin q, (V * U) p.1 p.2 * (U * V) p.1 p.2)
          * (∑ p : Fin q × Fin q, (V * U) p.1 p.2 * (U * V) p.1 p.2)
        ≤ (Matrix.trace ((U * U) * V * V)) * (Matrix.trace ((U * U) * V * V)) := by
      have := hcs
      rw [sq] at this
      exact this
    exact hcs'
  have habs : |Matrix.trace (U * V * U * V)|
      ≤ |Matrix.trace ((U * U) * V * V)| :=
    sq_le_sq.mp hsq
  rwa [abs_of_nonneg hT] at habs

/-! ## Lemma 2.3 -/

theorem lemma_2_3_first {ι : Type*} [Fintype ι]
    (B : ι → Matrix (Fin q) (Fin q) ℝ)
    (hB : ∀ a, (B a).IsSymm) :
    ∑ a, ∑ b, |Matrix.trace (B a * B b * B a * B b)|
      ≤ Matrix.trace ((∑ a, B a * B a) * (∑ a, B a * B a)) := by
  have hpt : ∀ a b, |Matrix.trace (B a * B b * B a * B b)|
      ≤ Matrix.trace (B a * B a * B b * B b) :=
    fun a b => frob_cs_UVUV (hB a) (hB b)
  have hassoc : ∀ a b, Matrix.trace (B a * B a * B b * B b)
      = Matrix.trace ((B a * B a) * (B b * B b)) :=
    fun a b => congrArg Matrix.trace (Matrix.mul_assoc (B a * B a) (B b) (B b))
  calc ∑ a, ∑ b, |Matrix.trace (B a * B b * B a * B b)|
      ≤ ∑ a, ∑ b, Matrix.trace (B a * B a * B b * B b) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
    _ = ∑ a, ∑ b, Matrix.trace ((B a * B a) * (B b * B b)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        exact hassoc a b
    _ = Matrix.trace (∑ a, ∑ b, (B a * B a) * (B b * B b)) := by
        have hinner : ∀ a, (∑ b, Matrix.trace ((B a * B a) * (B b * B b)))
            = Matrix.trace (∑ b, (B a * B a) * (B b * B b)) := by
          intro a
          exact (Matrix.trace_sum Finset.univ
            (fun b => (B a * B a) * (B b * B b))).symm
        simp_rw [hinner]
        rw [← Matrix.trace_sum]
    _ = Matrix.trace ((∑ a, B a * B a) * (∑ b, B b * B b)) := by
        have hsum : (∑ a, ∑ b, (B a * B a) * (B b * B b))
            = (∑ a, B a * B a) * (∑ b, B b * B b) := by
          conv_rhs => rw [Matrix.sum_mul]
          simp_rw [Matrix.mul_sum]
        rw [hsum]
    _ = Matrix.trace ((∑ a, B a * B a) * (∑ a, B a * B a)) := by
        congr 1

theorem sum_sq_posSemidef {ι : Type*} [Fintype ι]
    (B : ι → Matrix (Fin q) (Fin q) ℝ)
    (hB : ∀ a, (B a).IsSymm) :
    (∑ a, B a * B a).PosSemidef := by
  have h : ∀ a, (B a * B a).PosSemidef := by
    intro a
    have h1 : (B a)ᴴ * B a = B a * B a := by
      rw [conjTranspose_eq_transpose_real, hB a]
    rw [← h1]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have key : ∀ s : Finset ι, (∑ a ∈ s, B a * B a).PosSemidef := by
    classical
    intro s
    induction s using Finset.induction with
    | empty => simp [Matrix.PosSemidef.zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a).add ih
  exact key Finset.univ

theorem lemma_2_3_second {ι : Type*} [Fintype ι]
    (Bfn : ι → Matrix (Fin q) (Fin q) ℝ)
    (Ψ : Matrix (Fin q) (Fin q) ℝ)
    (hΨ : Ψ.PosSemidef)
    (hB : ∀ a, (Bfn a).IsSymm)
    (hle : (Ψ - ∑ a, Bfn a * Bfn a).PosSemidef) :
    Matrix.trace ((∑ a, Bfn a * Bfn a) * (∑ a, Bfn a * Bfn a))
      ≤ Matrix.trace (Ψ * Ψ) := by
  classical
  set Bmat := ∑ a, Bfn a * Bfn a
  have hBpsd : Bmat.PosSemidef := sum_sq_posSemidef Bfn hB
  have hΨB : (Ψ - Bmat).PosSemidef := hle
  have hsplit : Matrix.trace (Ψ * Ψ) - Matrix.trace (Bmat * Bmat)
      = Matrix.trace ((Ψ - Bmat) * (Ψ + Bmat)) := by
    have h1 : Ψ * Ψ - Bmat * Bmat
        = (Ψ - Bmat) * Ψ + Bmat * (Ψ - Bmat) := by
      rw [Matrix.sub_mul, Matrix.mul_sub]
      abel
    rw [← Matrix.trace_sub, h1, Matrix.trace_add]
    have h2 : Matrix.trace (Bmat * (Ψ - Bmat))
        = Matrix.trace ((Ψ - Bmat) * Bmat) :=
      Matrix.trace_mul_comm _ _
    rw [h2]
    have h3 : Matrix.trace ((Ψ - Bmat) * Ψ) + Matrix.trace ((Ψ - Bmat) * Bmat)
        = Matrix.trace ((Ψ - Bmat) * (Ψ + Bmat)) := by
      rw [← Matrix.trace_add, ← Matrix.mul_add]
    rw [h3]
  have hΨB_sum : (Ψ + Bmat).PosSemidef := hΨ.add hBpsd
  have hprod : 0 ≤ Matrix.trace ((Ψ - Bmat) * (Ψ + Bmat)) :=
    trace_mul_nonneg hΨB hΨB_sum
  have : Matrix.trace (Bmat * Bmat) ≤ Matrix.trace (Ψ * Ψ) := by
    linarith
  exact this

theorem lemma_2_3 {ι : Type*} [Fintype ι]
    (B : ι → Matrix (Fin q) (Fin q) ℝ)
    (Ψ : Matrix (Fin q) (Fin q) ℝ)
    (hΨ : Ψ.PosSemidef)
    (hB : ∀ a, (B a).IsSymm)
    (hle : (Ψ - ∑ a, B a * B a).PosSemidef) :
    (∑ a, ∑ b, |Matrix.trace (B a * B b * B a * B b)|
      ≤ Matrix.trace ((∑ a, B a * B a) * (∑ a, B a * B a)))
    ∧ (Matrix.trace ((∑ a, B a * B a) * (∑ a, B a * B a))
      ≤ Matrix.trace (Ψ * Ψ)) := by
  constructor
  · exact lemma_2_3_first B hB
  · exact lemma_2_3_second B Ψ hΨ hB hle

end Paper10
