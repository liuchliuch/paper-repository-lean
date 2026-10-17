import Paper26.PositiveLossBridge
import Paper26.VolumeSymmetry
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Ordered spectral decomposition of every positive definite density output

The index type is any prescribed finite sum `κ ⊕ σ`.  The first block has
exactly `card κ` eigenvalues, and every eigenvalue in the second block is at
most every eigenvalue in the first block.  Sorting is entirely internal:
Mathlib's Hermitian spectral theorem already supplies its `Fin`-indexed
spectrum in decreasing order (`eigenvalues₀_antitone`).  We explicitly
reindex that spectrum and its actual unitary eigenbasis.

No rank restriction, external sorting theorem, or special assumption about
the chosen eigenvectors is used.  The final identity is an equality of
actual `QuantumModel.Density` objects after conjugation by the inverse
unitary, in addition to the ordinary matrix reconstruction.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace Paper26.PositiveOutputDecomposition

open QuantumModel Normalization PositiveLossBridge

variable {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ] [DecidableEq σ]

/-- Enumerate the prescribed head block first, followed by the tail block. -/
def blockEnumeration : (κ ⊕ σ) ≃ Fin (Fintype.card (κ ⊕ σ)) :=
  ((Equiv.sumCongr (Fintype.equivFin κ) (Fintype.equivFin σ)).trans
    finSumFinEquiv).trans (finCongr (show Fintype.card (κ ⊕ σ) = Fintype.card κ + Fintype.card σ from
      Fintype.card_sum).symm)

@[simp] theorem blockEnumeration_inl_val (i : κ) :
    (blockEnumeration (σ := σ) (Sum.inl i)).val = (Fintype.equivFin κ i).val := rfl

@[simp] theorem blockEnumeration_inr_val (j : σ) :
    (blockEnumeration (κ := κ) (Sum.inr j)).val =
      Fintype.card κ + (Fintype.equivFin σ j).val := rfl

/-- The permutation from block coordinates to the original spectral labels.
The last equivalence is exactly the one used by `IsHermitian.eigenvalues`. -/
def sortedSpectrumPermutation : Equiv.Perm (κ ⊕ σ) :=
  blockEnumeration.trans (Fintype.equivOfCardEq (Fintype.card_fin _))

/-- The reordered actual spectrum is decreasing across the two blocks. -/
theorem sortedSpectrum_tail_le_head (τ : Density (κ ⊕ σ)) (i : κ) (j : σ) :
    τ.spectrum (sortedSpectrumPermutation (Sum.inr j)) ≤
      τ.spectrum (sortedSpectrumPermutation (Sum.inl i)) := by
  unfold Density.spectrum Matrix.IsHermitian.eigenvalues sortedSpectrumPermutation
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  apply τ.hermitian.eigenvalues₀_antitone
  change (blockEnumeration (Sum.inl i)).val ≤ (blockEnumeration (Sum.inr j)).val
  rw [blockEnumeration_inl_val, blockEnumeration_inr_val]
  have hi := (Fintype.equivFin κ i).isLt
  omega

/-- Complete ordered positive-output data for the prescribed sum split. -/
structure OrderedDecomposition (τ : Density (κ ⊕ σ)) where
  unitary : Matrix.unitaryGroup (κ ⊕ σ) ℂ
  head : κ → ℝ
  tail : σ → ℝ
  head_pos : ∀ i, 0 < head i
  tail_pos : ∀ j, 0 < tail j
  sum_one : (∑ i, head i) + (∑ j, tail j) = 1
  tail_le_head : ∀ i j, tail j ≤ head i
  reconstruction : τ.matrix = conjugate (unitary : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ)
    (diagonalMatrix (Sum.elim head tail))

/-- Every positive definite actual density has an ordered decomposition.
The unitary is the original eigenbasis with its columns explicitly permuted. -/
def orderedDecomposition (τ : Density (κ ⊕ σ)) (hτ : τ.matrix.PosDef) :
    OrderedDecomposition τ := by
  let e : Equiv.Perm (κ ⊕ σ) := sortedSpectrumPermutation
  let P : Matrix.unitaryGroup (κ ⊕ σ) ℂ :=
    ⟨e.permMatrix ℂ, Matrix.mem_unitaryGroup_iff.mpr
      (by simpa only [Matrix.star_eq_conjTranspose] using
        (VolumeSymmetry.permMatrix_unitary e).2)⟩
  let U : Matrix.unitaryGroup (κ ⊕ σ) ℂ := τ.eigenbasis * star P
  let p : (κ ⊕ σ) → ℝ := τ.spectrum ∘ e
  have hp : ∀ k, 0 < p k := fun k => τ.spectrum_pos hτ (e k)
  have hpsum : ∑ k, p k = 1 := by
    change (∑ k, τ.spectrum (e k)) = 1
    rw [Equiv.sum_comp e]
    exact τ.spectrum_sum
  have hdiag : diagonalMatrix p = conjugate (e.permMatrix ℂ)
      (diagonalMatrix τ.spectrum) :=
    (VolumeSymmetry.permMatrix_diagonal_conjugate e τ.spectrum).symm
  have hrec : τ.matrix = conjugate (U : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ)
      (diagonalMatrix p) := by
    rw [hdiag, density_spectral_reconstruction τ]
    change conjugate (τ.eigenbasis : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ)
        (diagonalMatrix τ.spectrum) =
      conjugate ((τ.eigenbasis : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) *
        (e.permMatrix ℂ)ᴴ) (conjugate (e.permMatrix ℂ) (diagonalMatrix τ.spectrum))
    simp only [conjugate, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    have hP := (VolumeSymmetry.permMatrix_unitary e).1
    simp only [Matrix.mul_assoc] at *
    rw [← Matrix.mul_assoc (e.permMatrix ℂ)ᴴ (e.permMatrix ℂ), hP,
      Matrix.one_mul]
    rw [← Matrix.mul_assoc (e.permMatrix ℂ)ᴴ (e.permMatrix ℂ), hP,
      Matrix.one_mul]
  refine ⟨U, (fun i => p (Sum.inl i)), (fun j => p (Sum.inr j)),
    (fun i => hp _), (fun j => hp _), ?_, ?_, ?_⟩
  · simpa only [Fintype.sum_sum_type] using hpsum
  · exact fun i j => sortedSpectrum_tail_le_head τ i j
  · have hpFun : Sum.elim (fun i => p (Sum.inl i)) (fun j => p (Sum.inr j)) = p := by
      funext k
      cases k <;> rfl
    rw [hpFun]
    exact hrec

private theorem density_ext {ι : Type*} [Fintype ι] {ρ η : Density ι}
    (h : ρ.matrix = η.matrix) : ρ = η := by
  cases ρ
  cases η
  cases h
  rfl

namespace OrderedDecomposition

variable {τ : Density (κ ⊕ σ)} (D : OrderedDecomposition τ)

/-- The ordinary diagonal state determined by the two positive spectral blocks. -/
def diagonalDensity : Density (κ ⊕ σ) :=
  Density.diagonal (Sum.elim D.head D.tail)
    (by intro k; cases k with
        | inl i => exact (D.head_pos i).le
        | inr j => exact (D.tail_pos j).le)
    (by simpa only [Fintype.sum_sum_type] using D.sum_one)

@[simp] theorem diagonalDensity_matrix :
    D.diagonalDensity.matrix = diagonalMatrix (Sum.elim D.head D.tail) := rfl

/-- Inverse-unitary coordinates are exactly the actual diagonal density matrix. -/
theorem coordinates_matrix :
    coordinates (D.unitary : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ) τ.matrix =
      D.diagonalDensity.matrix := by
  rw [D.reconstruction, coordinates_conjugate _ _ (unitary_left D.unitary)]
  rfl

/-- Equality of actual density objects, with all positivity and trace data. -/
theorem conjugateDensity_eq_diagonalDensity :
    conjugateDensity (star D.unitary) τ = D.diagonalDensity := by
  have h : (conjugateDensity (star D.unitary) τ).matrix = D.diagonalDensity.matrix := by
    simpa only [conjugateDensity_matrix, unitary.coe_star,
      Matrix.star_eq_conjTranspose, conjugate, Matrix.conjTranspose_conjTranspose,
      coordinates] using D.coordinates_matrix
  exact density_ext h

end OrderedDecomposition

end Paper26.PositiveOutputDecomposition
