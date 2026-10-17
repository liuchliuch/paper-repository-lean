import Paper26.TailConvexity
import Paper26.SpectralAveraging
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# The matrix and set symmetries used in Lemma 2.3

This module proves actual sublevel-set transport under unitary row rotations,
actual permutation-matrix diagonal conjugation, and the final finite Jensen
transport from diagonal spectra to arbitrary positive definite matrices.
Concavity and unitary invariance of a scalar functional are explicit hypotheses;
no volume inequality or measure-preservation theorem is assumed here.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace Paper26.VolumeSymmetry

open Normalization TailConvexity

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The actual quartic tail sublevel set. -/
def body (A : Matrix ι ι ℂ) (K : ℝ) : Set (Matrix ι κ ℂ) :=
  {Z | H A Z ≤ K}

/-- Rotating the positive matrix rotates the entire tail body by left multiplication. -/
theorem body_conjugate (U A : Matrix ι ι ℂ) (K : ℝ)
    (hU₁ : Uᴴ * U = 1) (hU₂ : U * Uᴴ = 1) (hA : A.PosDef) :
    body (conjugate U A) K = (fun Z : Matrix ι κ ℂ => U * Z) '' body A K := by
  ext Z
  constructor
  · intro hZ
    have hinverse : U * (Uᴴ * Z) = Z := by
      rw [← Matrix.mul_assoc, hU₂, Matrix.one_mul]
    refine ⟨Uᴴ * Z, ?_, hinverse⟩
    have hinv := H_unitary U A (Uᴴ * Z) hU₁ hU₂ hA
    rw [hinverse] at hinv
    change H A (Uᴴ * Z) ≤ K
    rw [← hinv]
    exact hZ
  · rintro ⟨W, hW, rfl⟩
    change H (conjugate U A) (U * W) ≤ K
    rw [H_unitary U A W hU₁ hU₂ hA]
    exact hW

/-- Both unitary identities for the actual complex permutation matrix. -/
theorem permMatrix_unitary (σ : Equiv.Perm ι) :
    (σ.permMatrix ℂ)ᴴ * σ.permMatrix ℂ = 1 ∧
      σ.permMatrix ℂ * (σ.permMatrix ℂ)ᴴ = 1 := by
  constructor
  · rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul]
    ext i j
    simp [Matrix.submatrix_apply, PEquiv.toMatrix_toPEquiv_apply,
      Pi.single_apply, Matrix.one_apply, eq_comm]
  · rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul]
    ext i j
    simp [Matrix.submatrix_apply, PEquiv.toMatrix_toPEquiv_apply,
      Pi.single_apply, Matrix.one_apply, eq_comm]

/-- This convention for permutation matrices sends the spectrum to `a ∘ σ`. -/
theorem permMatrix_diagonal_conjugate (σ : Equiv.Perm ι) (a : ι → ℝ) :
    conjugate (σ.permMatrix ℂ) (diagonalMatrix a) = diagonalMatrix (a ∘ σ) := by
  unfold conjugate
  rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.submatrix_apply, diagonalMatrix, Function.comp_def, Equiv.Perm.inv_def]
  · have hs : σ i ≠ σ j := fun h => hij (σ.injective h)
    simp [Matrix.submatrix_apply, diagonalMatrix, Function.comp_def, Equiv.Perm.inv_def, hij, hs]

lemma diagonalMatrix_const (x : ℝ) :
    diagonalMatrix (fun _ : ι => x) = (x : ℂ) • (1 : Matrix ι ι ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [diagonalMatrix]
  · simp [diagonalMatrix, Matrix.one_apply, hij]

/-- A concise exact interface for unitary-conjugation invariance on the positive cone. -/
def UnitaryInvariantOnPosDef (v : Matrix ι ι ℂ → ℝ) : Prop :=
  ∀ (U A : Matrix ι ι ℂ), Uᴴ * U = 1 → U * Uᴴ = 1 → A.PosDef →
    v (conjugate U A) = v A

/-- Unitary invariance provides the cyclic permutation invariance needed by
finite spectral averaging. -/
theorem cyclic_orbit_invariance [AddCommGroup ι]
    (v : Matrix ι ι ℂ → ℝ) (hv : UnitaryInvariantOnPosDef v)
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (j : ι) :
    v (diagonalMatrix (fun i => a (i + j))) = v (diagonalMatrix a) := by
  let σ : Equiv.Perm ι := Equiv.addRight j
  have hD : (diagonalMatrix a).PosDef :=
    Matrix.posDef_diagonal_iff.mpr fun i => RCLike.ofReal_pos.mpr (ha i)
  have hU := permMatrix_unitary σ
  have h := hv (σ.permMatrix ℂ) (diagonalMatrix a) hU.1 hU.2 hD
  rw [permMatrix_diagonal_conjugate] at h
  simpa only [σ, Function.comp_def, Equiv.coe_addRight] using h

/-- Every concave, unitary-invariant functional on positive matrices is
maximized at the uniform matrix with the same trace.  The finite additive
index type covers `ZMod s` for every positive dimension `s`. -/
theorem uniform_matrix_maximal_of_concavity [AddCommGroup ι] [Nonempty ι]
    (v : Matrix ι ι ℂ → ℝ)
    (hv : ConcaveOn ℝ {A : Matrix ι ι ℂ | A.PosDef} v)
    (hunitary : UnitaryInvariantOnPosDef v)
    (A : Matrix ι ι ℂ) (hA : A.PosDef) :
    v A ≤ v ((((Matrix.trace A).re / (Fintype.card ι : ℝ) : ℝ) : ℂ) •
      (1 : Matrix ι ι ℂ)) := by
  obtain ⟨U, a, hU₁, hU₂, ha, hAeq⟩ := exists_positive_spectral_representation A hA
  have hD : (diagonalMatrix a).PosDef :=
    Matrix.posDef_diagonal_iff.mpr fun i => RCLike.ofReal_pos.mpr (ha i)
  have hVA : v A = v (diagonalMatrix a) := by
    rw [hAeq]
    exact hunitary U _ hU₁ hU₂ hD
  have htrace : (Matrix.trace A).re = ∑ i, a i := by
    rw [hAeq, trace_conjugate_diagonal U a hU₁]
  have hjensen := SpectralAveraging.uniform_diagonal_maximal_of_concavity v hv a ha
    (cyclic_orbit_invariance v hunitary a ha)
  calc
    v A = v (diagonalMatrix a) := hVA
    _ ≤ v (diagonalMatrix (fun _ : ι => (∑ i, a i) / Fintype.card ι)) := hjensen
    _ = v ((((Matrix.trace A).re / (Fintype.card ι : ℝ) : ℝ) : ℂ) •
        (1 : Matrix ι ι ℂ)) := by rw [htrace, diagonalMatrix_const]

end Paper26.VolumeSymmetry
