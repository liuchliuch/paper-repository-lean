import Paper25.Norms
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing

/-!
# Lemma 3: CPTP Frobenius bound

If `S` is the Liouville matrix of a CPTP map on a `d`-dimensional system, then
`‖S‖_F² ≤ d²`.

The proof follows the paper:

* The unnormalized Choi matrix `J = ∑_{i,j} Ψ(|i⟩⟨j|) ⊗ |i⟩⟨j|` is positive
  semidefinite (complete positivity) and has trace `d` (trace preservation).
* The entries of `J` are a reshuffling of the entries of `S`, so the two
  Frobenius norms agree (entrywise `ℓ²` is invariant under a permutation of
  summands).
* If `μ_i ≥ 0` are the eigenvalues of `J` then
  `‖J‖_F² = Tr(J²) = ∑ μ_i² ≤ (∑ μ_i)² = d²`.

This file proves the mathematical core:

* `entryNormSq`: entrywise squared `ℓ²` norm of an arbitrary finite matrix;
* invariance of `entryNormSq` under index reshuffling (`liouvilleToChoi`);
* `entryNormSq J = Tr(J²) = ∑ μ_i²` for Hermitian `J` (via the spectral theorem);
* `psd_trace_frob_bound`: a PSD matrix of trace `t` has `entryNormSq ≤ t²`;
* `lemma_3_cptp_frob_bound`: the packaged statement for CPTP Liouville matrices.
-/

noncomputable section

open scoped ComplexOrder ComplexConjugate

namespace Paper25

variable {m : ℕ}

/-! ## General entrywise squared `ℓ²` norm -/

/-- Entrywise squared `ℓ²` norm of a finite (possibly rectangular) matrix. -/
def entryNormSq {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

lemma entryNormSq_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    0 ≤ entryNormSq A :=
  Fintype.sum_nonneg fun _ => Fintype.sum_nonneg fun _ => Complex.normSq_nonneg _

lemma entryNormSq_eq_frobNormSq (A : Matrix (Fin m) (Fin m) ℂ) :
    entryNormSq A = frobNormSq A :=
  rfl

lemma frobNormSq_eq_entryNormSq (A : Matrix (Fin m) (Fin m) ℂ) :
    frobNormSq A = entryNormSq A :=
  rfl

/-- Single sum over row-column pairs. -/
lemma entryNormSq_eq_sum_prod {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    entryNormSq A = ∑ p : ι × κ, Complex.normSq (A p.1 p.2) := by
  classical
  unfold entryNormSq
  rw [Fintype.sum_prod_type]

/-- Reindexing rows and columns by equivalences preserves `entryNormSq`. -/
lemma entryNormSq_submatrix_equiv {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ]
    [Fintype ι'] [Fintype κ'] (A : Matrix ι κ ℂ) (e : ι' ≃ ι) (f : κ' ≃ κ) :
    entryNormSq (A.submatrix e f) = entryNormSq A := by
  classical
  rw [entryNormSq_eq_sum_prod, entryNormSq_eq_sum_prod]
  simp only [Matrix.submatrix_apply]
  have h : (fun p : ι' × κ' => Complex.normSq (A (e p.1) (f p.2)))
      = (fun q : ι × κ => Complex.normSq (A q.1 q.2)) ∘ (e.prodCongr f) := by
    funext p
    rcases p with ⟨p1, p2⟩
    rfl
  rw [h, ← (e.prodCongr f).sum_comp]
  rfl

/-! ## Reshuffling: Liouville ↔ Choi -/

/-- Reshuffling of a Liouville matrix into unnormalized Choi form.

A Liouville entry `S_{(a,b),(α,β)}` records the `(a,b)` output entry of
`Ψ(|α⟩⟨β|)`.  The Choi matrix reads the same number with row index `(a,α)`
and column index `(b,β)`.  The four-index map
`(a,b),(α,β) ↦ (a,α),(b,β)` is a permutation of summands, so the entrywise
`ℓ²` norm is unchanged. -/
def liouvilleToChoi {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun a b => S (a.1, b.1) (a.2, b.2)

lemma liouvilleToChoi_apply {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (a b : Fin d × Fin d) :
    liouvilleToChoi S a b = S (a.1, b.1) (a.2, b.2) :=
  rfl

/-- The four-index reshuffling bijection `(a,b),(α,β) ↦ (a,α),(b,β)`.

Both directions use the same pairing formula because the map is an involution
once the four factors are identified. -/
def reshuffleEquiv {α β γ δ : Type*} :
    ((α × β) × (γ × δ)) ≃ ((α × γ) × (β × δ)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv x := by
    rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rfl
  right_inv x := by
    rcases x with ⟨⟨a, c⟩, ⟨b, d⟩⟩
    rfl

/-- Reshuffling preserves the entrywise squared `ℓ²` norm. -/
lemma entryNormSq_liouvilleToChoi {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    entryNormSq (liouvilleToChoi S) = entryNormSq S := by
  classical
  rw [entryNormSq_eq_sum_prod, entryNormSq_eq_sum_prod]
  unfold liouvilleToChoi
  simp only [Matrix.of_apply]
  set e : ((Fin d × Fin d) × (Fin d × Fin d)) ≃ ((Fin d × Fin d) × (Fin d × Fin d)) :=
    reshuffleEquiv
  have h : (fun p : (Fin d × Fin d) × (Fin d × Fin d) =>
      Complex.normSq (S (p.1.1, p.2.1) (p.1.2, p.2.2)))
      = (fun q : (Fin d × Fin d) × (Fin d × Fin d) => Complex.normSq (S q.1 q.2)) ∘ e := by
    funext p
    simp only [Function.comp_apply]
    rfl
  rw [h, ← e.sum_comp]
  rfl

/-! ## Frobenius norm via the trace -/

/-- The entrywise squared `ℓ²` norm is `Tr(Aᴴ A)`. -/
lemma entryNormSq_eq_trace_conjTranspose_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    (entryNormSq A : ℂ) = Matrix.trace (A.conjTranspose * A) := by
  classical
  have hcell : ∀ z : ℂ, (Complex.normSq z : ℂ) = star z * z := by
    intro z
    conv_rhs => rw [show star z = conj z from rfl]
    exact Complex.normSq_eq_conj_mul_self
  have hL : (entryNormSq A : ℂ) = ∑ i, ∑ j, (Complex.normSq (A i j) : ℂ) := by
    unfold entryNormSq
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.ofReal_sum _ _
  have hR : Matrix.trace (A.conjTranspose * A)
      = ∑ i, ∑ k, star (A k i) * A k i := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hL, hR]
  simp only [hcell]
  exact Finset.sum_comm

lemma frobNormSq_eq_trace_conjTranspose_mul (A : Matrix (Fin m) (Fin m) ℂ) :
    (frobNormSq A : ℂ) = Matrix.trace (A.conjTranspose * A) := by
  rw [frobNormSq_eq_entryNormSq, entryNormSq_eq_trace_conjTranspose_mul]

/-- For Hermitian `A`, the entrywise squared `ℓ²` norm is `Tr(A²)`. -/
lemma entryNormSq_eq_trace_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (entryNormSq A : ℂ) = Matrix.trace (A * A) := by
  rw [entryNormSq_eq_trace_conjTranspose_mul, hA.eq]

/-! ## Spectral expression `‖J‖_F² = ∑ μ_i²` -/

/-- Cyclic invariance of the trace under a unitary conjugation. -/
lemma trace_conj_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U X : Matrix ι ι ℂ} (hU : star U * U = 1) :
    Matrix.trace (U * X * star U) = Matrix.trace X := by
  calc Matrix.trace (U * X * star U)
      = Matrix.trace (star U * U * X) := by
        rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (1 * X) := by rw [hU]
    _ = Matrix.trace X := by rw [one_mul]

/-- For Hermitian `A`, `Tr(A²) = (∑_i μ_i² : ℝ)` embedded in `ℂ`. -/
lemma trace_mul_self_eq_sum_eigenvalues_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    Matrix.trace (A * A) = ((∑ i, (hA.eigenvalues i) ^ 2 : ℝ) : ℂ) := by
  classical
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDdef
  have hUU : star U * U = 1 := by
    rw [hUdef]
    exact (Matrix.mem_unitaryGroup_iff').mp (hA.eigenvectorUnitary).2
  have hspec : A = U * D * star U := by
    rw [hUdef, hDdef]
    exact hA.spectral_theorem
  have htrace : Matrix.trace (A * A)
      = Matrix.trace ((U * D * star U) * (U * D * star U)) := by
    rw [hspec]
  rw [htrace]
  have hsq : (U * D * star U) * (U * D * star U) = U * (D * D) * star U := by
    calc (U * D * star U) * (U * D * star U)
        = U * D * (star U * U) * D * star U := by noncomm_ring
      _ = U * D * 1 * D * star U := by rw [hUU]
      _ = U * (D * D) * star U := by noncomm_ring
  rw [hsq, trace_conj_unitary hUU, hDdef, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  show ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) * ((hA.eigenvalues i : ℝ) : ℂ)
    = ((∑ i, (hA.eigenvalues i) ^ 2 : ℝ) : ℂ)
  have h1 : ∀ i, ((hA.eigenvalues i : ℝ) : ℂ) * ((hA.eigenvalues i : ℝ) : ℂ)
      = (((hA.eigenvalues i) ^ 2 : ℝ) : ℂ) := by
    intro i
    exact_mod_cast (sq (hA.eigenvalues i)).symm
  rw [Finset.sum_congr rfl fun i _ => h1 i]
  show (∑ i : ι, (((hA.eigenvalues i) ^ 2 : ℝ) : ℂ))
    = (((∑ i : ι, (hA.eigenvalues i) ^ 2 : ℝ) : ℂ))
  exact (Complex.ofReal_sum (Finset.univ) (fun i : ι => (hA.eigenvalues i) ^ 2)).symm

/-- For Hermitian `A`, `‖A‖_F² = ∑_i μ_i²`. -/
lemma entryNormSq_eq_sum_eigenvalues_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    entryNormSq A = ∑ i, (hA.eigenvalues i) ^ 2 := by
  have h1 : (entryNormSq A : ℂ) = Matrix.trace (A * A) :=
    entryNormSq_eq_trace_mul_self A hA
  have h2 : Matrix.trace (A * A) = ((∑ i, (hA.eigenvalues i) ^ 2 : ℝ) : ℂ) :=
    trace_mul_self_eq_sum_eigenvalues_sq A hA
  have h3 : (entryNormSq A : ℂ) = ((∑ i, (hA.eigenvalues i) ^ 2 : ℝ) : ℂ) := by
    rw [h1, h2]
  exact_mod_cast h3

lemma frobNormSq_eq_sum_eigenvalues_sq (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.IsHermitian) :
    frobNormSq A = ∑ i, (hA.eigenvalues i) ^ 2 := by
  rw [frobNormSq_eq_entryNormSq]
  exact entryNormSq_eq_sum_eigenvalues_sq A hA

/-! ## Scalar inequality `∑ μ_i² ≤ (∑ μ_i)²` for `μ_i ≥ 0` -/

/-- For nonnegative reals, the sum of squares is at most the square of the sum. -/
lemma sum_sq_le_sq_sum {ι : Type*} [Fintype ι] (μ : ι → ℝ) (h : ∀ i, 0 ≤ μ i) :
    (∑ i, μ i ^ 2) ≤ (∑ i, μ i) ^ 2 := by
  classical
  have aux : ∀ s : Finset ι, (∑ i ∈ s, μ i ^ 2) ≤ (∑ i ∈ s, μ i) ^ 2 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      have ha' : 0 ≤ μ a := h a
      have hsum : 0 ≤ ∑ i ∈ s, μ i := Finset.sum_nonneg fun i _ => h i
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hexpand : (μ a + ∑ i ∈ s, μ i) ^ 2
          = μ a ^ 2 + (∑ i ∈ s, μ i) ^ 2 + 2 * μ a * ∑ i ∈ s, μ i := by
        ring
      rw [hexpand]
      have hmul : 0 ≤ 2 * μ a * ∑ i ∈ s, μ i :=
        mul_nonneg (mul_nonneg (by norm_num) ha') hsum
      linarith
  simpa using aux Finset.univ

/-! ## PSD trace bound (mathematical core of Lemma 3) -/

/-- A positive semidefinite matrix of trace `t` has squared Frobenius norm at most `t²`.

This is `∑ μ_i² ≤ (∑ μ_i)²` for the nonnegative eigenvalues `μ_i`. -/
theorem psd_trace_frob_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℂ) (hJ : J.PosSemidef) (t : ℝ) (ht : Matrix.trace J = (t : ℂ)) :
    entryNormSq J ≤ t ^ 2 := by
  classical
  have hherm : J.IsHermitian := hJ.isHermitian
  have hnonneg : ∀ i, 0 ≤ hherm.eigenvalues i := fun i => hJ.eigenvalues_nonneg i
  have hsq := entryNormSq_eq_sum_eigenvalues_sq J hherm
  rw [hsq]
  have htrace := hherm.trace_eq_sum_eigenvalues
  have hsum : (∑ i, (hherm.eigenvalues i : ℂ)) = (t : ℂ) := htrace.symm.trans ht
  have hsumRe : (∑ i, hherm.eigenvalues i) = t := by
    have h := congrArg Complex.re hsum
    exact_mod_cast h
  rw [← hsumRe]
  exact sum_sq_le_sq_sum _ hnonneg

theorem psd_trace_frob_bound_fin {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J.PosSemidef) (t : ℝ) (ht : Matrix.trace J = (t : ℂ)) :
    frobNormSq J ≤ t ^ 2 := by
  rw [frobNormSq_eq_entryNormSq]
  exact psd_trace_frob_bound J hJ t ht

/-- Special case used for a Choi matrix of size `n` and trace `n`. -/
theorem psd_trace_frob_bound_dim {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J.PosSemidef) (hd : Matrix.trace J = (n : ℂ)) :
    frobNormSq J ≤ (n : ℝ) ^ 2 :=
  psd_trace_frob_bound_fin J hJ (n : ℝ) hd

/-! ## Packaged Lemma 3 for CPTP Liouville matrices -/

/-- A sufficient Choi certificate for the Frobenius estimate. The historical
name `IsCPTP` records only two consequences of complete positivity and trace
preservation: PSD and total Choi trace `d`. These conditions alone do not
characterize trace preservation. Actual channels are defined by Kraus
completeness in `SourceChannels.lean`, which also proves the full Choi partial
trace identity and derives this weaker certificate. -/
structure IsCPTP {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop where
  /-- Complete positivity: the Choi matrix is positive semidefinite. -/
  choi_posSemidef : (liouvilleToChoi S).PosSemidef
  /-- Total Choi trace, a consequence of trace preservation. -/
  choi_trace : Matrix.trace (liouvilleToChoi S) = (d : ℂ)

/-- **Lemma 3 (CPTP Frobenius bound).**
The squared Frobenius (entrywise `ℓ²`) norm of the Liouville matrix of a CPTP
map on a `d`-dimensional system is at most `d²`. -/
theorem lemma_3_cptp_frob_bound {d : ℕ} (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (h : IsCPTP S) : entryNormSq S ≤ (d : ℝ) ^ 2 := by
  have hresh := entryNormSq_liouvilleToChoi S
  have hcore := psd_trace_frob_bound (liouvilleToChoi S) h.choi_posSemidef (d : ℝ) h.choi_trace
  rw [← hresh]
  exact hcore

/-- Abstract square-matrix form of Lemma 3: if `J` is a reshuffling of `S`
(identified by equal entrywise `ℓ²` norms) and `J` is the Choi matrix of a CPTP
map (`J` PSD of trace `d`), then `‖S‖_F² ≤ d²`. -/
theorem lemma_3_frob_bound_of_choi {n d : ℕ} (S J : Matrix (Fin n) (Fin n) ℂ)
    (hresh : entryNormSq J = entryNormSq S)
    (hPSD : J.PosSemidef) (htr : Matrix.trace J = (d : ℂ)) :
    frobNormSq S ≤ (d : ℝ) ^ 2 := by
  have hcore := psd_trace_frob_bound_fin J hPSD (d : ℝ) htr
  rw [frobNormSq_eq_entryNormSq, ← hresh]
  exact hcore

end Paper25
