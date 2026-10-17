import Paper26.MultiscaleUpdate

/-!
# Compression and Frobenius bridges for the actual multiscale algorithm

All estimates below are actual matrices on the current finite active subset.
The bridge identifies their ordinary Frobenius errors with the local errors
used by deterministic shell accounting after the selected block eigenbasis
is extended to the ambient space.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder
open MeasureTheory

namespace Paper26.MultiscaleMatrixBridge
open QuantumModel Normalization ShellAccounting MultiscaleUpdate

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))
local instance matrixBorelSpace (m n : Type*) [Fintype m] [Fintype n] : BorelSpace (Matrix m n ℂ) :=
  inferInstanceAs (BorelSpace (m → n → ℂ))

def compressedBlock (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) :
    Matrix (BlockIndex S) (BlockIndex S) ℂ :=
  (coordinates (U : Matrix ι ι ℂ) ρ.matrix).submatrix Subtype.val Subtype.val

theorem compressedBlock_posSemidef (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) :
    (compressedBlock S U ρ).PosSemidef := by
  apply Matrix.PosSemidef.submatrix
  simpa only [coordinates, Matrix.conjTranspose_conjTranspose] using
    ρ.positive.mul_mul_conjTranspose_same (U : Matrix ι ι ℂ)ᴴ

theorem compressedBlock_rank_le (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) :
    (compressedBlock S U ρ).rank ≤ ρ.matrix.rank := by
  have hs : (compressedBlock S U ρ).rank ≤ (coordinates (U : Matrix ι ι ℂ) ρ.matrix).rank := by
    have h := Cardinal.toNat_le_toNat
      (Matrix.cRank_submatrix_le (coordinates (U : Matrix ι ι ℂ) ρ.matrix)
        (fun i : BlockIndex S => i.val) (fun i : BlockIndex S => i.val))
      ((Matrix.cRank_le_card_width _).trans_lt (Cardinal.nat_lt_aleph0 _))
    simpa only [Matrix.cRank_toNat_eq_rank] using h
  exact hs.trans ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _))

omit [Fintype ι] in
theorem embedBlock_mask (S : Finset ι) (X : Matrix ι ι ℂ) :
    embedBlock S (X.submatrix Subtype.val Subtype.val) =
      MultiscaleRefinement.mask (fun i => i ∈ S) X := by
  ext i k
  by_cases hi : i ∈ S <;> by_cases hk : k ∈ S
  · rw [embedBlock_inside S _ ⟨i, hi⟩ ⟨k, hk⟩]
    simp [MultiscaleRefinement.mask, hi, hk]
  · rw [embedBlock_outside S _ i k (Or.inr hk)]
    simp [MultiscaleRefinement.mask, hk]
  · rw [embedBlock_outside S _ i k (Or.inl hi)]
    simp [MultiscaleRefinement.mask, hi]
  · rw [embedBlock_outside S _ i k (Or.inl hi)]
    simp [MultiscaleRefinement.mask, hi]

omit [Fintype ι] in
theorem embedBlock_sub (S : Finset ι) (A C : Matrix (BlockIndex S) (BlockIndex S) ℂ) :
    embedBlock S (A - C) = embedBlock S A - embedBlock S C := by
  ext i k
  by_cases hi : i ∈ S <;> by_cases hk : k ∈ S
  · rw [embedBlock_inside S (A-C) ⟨i, hi⟩ ⟨k, hk⟩]
    simp only [Matrix.sub_apply]
    rw [embedBlock_inside S A ⟨i, hi⟩ ⟨k, hk⟩, embedBlock_inside S C ⟨i, hi⟩ ⟨k, hk⟩]
  · simp [Matrix.sub_apply, embedBlock_outside S _ i k (Or.inr hk)]
  · simp [Matrix.sub_apply, embedBlock_outside S _ i k (Or.inl hi)]
  · simp [Matrix.sub_apply, embedBlock_outside S _ i k (Or.inl hi)]

theorem frobeniusSq_embedBlock (S : Finset ι) (C : Matrix (BlockIndex S) (BlockIndex S) ℂ) :
    frobeniusSq (embedBlock S C) = frobeniusSq C := by
  let e := Equiv.sumCompl (fun i : ι => i ∈ S)
  let X : Matrix (BlockIndex S ⊕ {i // i ∉ S}) (BlockIndex S ⊕ {i // i ∉ S}) ℂ :=
    Matrix.fromBlocks C 0 0 0
  change (∑ i, ∑ k, ‖X (e.symm i) (e.symm k)‖ ^ 2) = _
  calc
    _ = ∑ i, ∑ k, ‖X (e.symm i) k‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact e.symm.sum_comp (fun k => ‖X (e.symm i) k‖ ^ 2)
    _ = ∑ i, ∑ k, ‖X i k‖ ^ 2 := e.symm.sum_comp (fun i => ∑ k, ‖X i k‖ ^ 2)
    _ = _ := by simp [X, frobeniusSq, Fintype.sum_sum_type, Matrix.fromBlocks]

theorem selectedUpdate_cross_zero (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (S : Finset ι) (C : PositiveBlock S) (i k : ι) (h : (i ∈ S) ≠ (k ∈ S)) :
    (selectedUpdate B S C : Matrix ι ι ℂ) i k = 0 := by
  have hik : i ≠ k := by intro he; subst k; exact h rfl
  have hout : i ∉ S ∨ k ∉ S := by
    by_cases hi : i ∈ S
    · right
      intro hk
      exact h (propext ⟨fun _ => hk, fun _ => hi⟩)
    · exact Or.inl hi
  rw [selectedUpdate, extendUnitary_outside S _ i k hout, Matrix.one_apply_ne hik]

theorem selectedUpdate_coordinates (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (S : Finset ι) (C : PositiveBlock S) :
    coordinates (selectedUpdate B S C : Matrix ι ι ℂ) (embedBlock S C.val) =
      diagonalMatrix (blockValues S C) := by
  rw [selectedUpdate_diagonalizes B S C, coordinates_conjugate _ _
    (PositiveLossBridge.unitary_left (selectedUpdate B S C))]

omit [Fintype ι] in
theorem mask_blockValues (S : Finset ι) (C : PositiveBlock S) :
    MultiscaleRefinement.mask (fun i => i ∈ S) (diagonalMatrix (blockValues S C)) =
      diagonalMatrix (blockValues S C) := by
  ext i k
  by_cases hi : i ∈ S <;> by_cases hk : k ∈ S
  · simp [MultiscaleRefinement.mask, hi, hk]
  · have hik : i ≠ k := by intro he; subst k; exact hk hi
    simp [MultiscaleRefinement.mask, hk, diagonalMatrix, hik]
  · have hik : i ≠ k := by intro he; subst k; exact hi hk
    simp [MultiscaleRefinement.mask, hi, diagonalMatrix, hik]
  · by_cases hik : i = k
    · subst k
      simp [MultiscaleRefinement.mask, hi, diagonalMatrix, blockValues]
    · simp [MultiscaleRefinement.mask, hi, diagonalMatrix, hik]

/-- The actual compressed-matrix error becomes precisely the shell-accounting
error after the real selected block basis change. -/
theorem localError_frobeniusSq
    (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) (C : PositiveBlock S) :
    frobeniusSq (MultiscaleRefinement.mask (fun i => i ∈ S)
      (coordinates ((U * selectedUpdate B S C : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) ρ.matrix -
        diagonalMatrix (blockValues S C))) = frobeniusSq (compressedBlock S U ρ - C.val) := by
  let V := selectedUpdate B S C
  have hc : coordinates (V : Matrix ι ι ℂ) (coordinates (U : Matrix ι ι ℂ) ρ.matrix) =
      coordinates ((U * V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) ρ.matrix := by
    simp only [coordinates, Matrix.UnitaryGroup.mul_val, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hmat : coordinates (V : Matrix ι ι ℂ) (embedBlock S (compressedBlock S U ρ - C.val)) =
      MultiscaleRefinement.mask (fun i => i ∈ S)
        (coordinates ((U * V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) ρ.matrix -
          diagonalMatrix (blockValues S C)) := by
    rw [embedBlock_sub, coordinates_sub]
    change coordinates (V : Matrix ι ι ℂ)
      (embedBlock S ((coordinates (U : Matrix ι ι ℂ) ρ.matrix).submatrix Subtype.val Subtype.val)) -
        coordinates (V : Matrix ι ι ℂ) (embedBlock S C.val) = _
    rw [embedBlock_mask, MultiscaleRefinement.coordinates_mask _ V _ (selectedUpdate_cross_zero B S C),
      hc, selectedUpdate_coordinates B S C, MultiscaleRefinement.mask_sub, mask_blockValues S C]
  rw [← hmat, MultiscaleRefinement.frobeniusSq_coordinates, frobeniusSq_embedBlock]

/-- Entry measurability of the real compression, jointly through its unitary. -/
theorem measurable_compressedBlock (S : Finset ι) (ρ : Density ι) :
    Measurable (fun U : Matrix.unitaryGroup ι ℂ => compressedBlock S U ρ) := by
  have hc : Continuous (fun U : Matrix.unitaryGroup ι ℂ => coordinates (U : Matrix ι ι ℂ) ρ.matrix) := by
    exact (continuous_subtype_val.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_subtype_val
  have hm := hc.measurable
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro k
  exact (measurable_pi_apply k.val).comp ((measurable_pi_apply i.val).comp hm)

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_frobeniusSq {m n : Type*} [Fintype m] [Fintype n] :
    Continuous (fun C : Matrix m n ℂ => frobeniusSq C) := by
  exact continuous_finset_sum Finset.univ fun i _ => continuous_finset_sum Finset.univ fun k _ =>
    ((continuous_apply k).comp (continuous_apply i)).norm.pow 2

def blockError (ρ : Density ι) (S : Finset ι)
    (p : Matrix.unitaryGroup ι ℂ × PositiveBlock S) : ℝ :=
  frobeniusSq (compressedBlock S p.1 ρ - p.2.val)

theorem measurable_blockError (ρ : Density ι) (S : Finset ι) : Measurable (blockError ρ S) := by
  have hr := (measurable_compressedBlock S ρ).comp
    (measurable_fst : Measurable (fun p : Matrix.unitaryGroup ι ℂ × PositiveBlock S => p.1))
  have hc : Measurable (fun p : Matrix.unitaryGroup ι ℂ × PositiveBlock S => p.2.val) :=
    measurable_subtype_coe.comp measurable_snd
  have hd : Measurable (fun p : Matrix.unitaryGroup ι ℂ × PositiveBlock S =>
      compressedBlock S p.1 ρ - p.2.val) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro k
    exact ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hr)).sub
      ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hc))
  have hm := continuous_frobeniusSq.measurable.comp hd
  exact hm

def stateErrorFiber (ρ : Density ι) (S : Finset ι) (q : Payload (ι := ι)) : ℝ :=
  blockError ρ S (q.1.1, q.2 S)

theorem measurable_stateErrorFiber (ρ : Density ι) (S : Finset ι) : Measurable (stateErrorFiber ρ S) := by
  have hU : Measurable (fun q : Payload (ι := ι) => q.1.1) := measurable_fst.comp measurable_fst
  have hc : Measurable (fun q : Payload (ι := ι) => q.2 S) :=
    (measurable_pi_apply S).comp measurable_snd
  have hm := (measurable_blockError ρ S).comp (hU.prodMk hc)
  exact hm

/-- One actual stage's error, before choosing its next eigenbasis. -/
def stateError (ρ : Density ι) (p : State (ι := ι) × EstimateFamily (ι := ι)) : ℝ :=
  stateErrorFiber ρ p.1.1 (p.1.2, p.2)

theorem measurable_stateError (ρ : Density ι) : Measurable (stateError ρ) := by
  have hf : Measurable (fun p : Finset ι × Payload (ι := ι) => stateErrorFiber ρ p.1 p.2) :=
    measurable_from_prod_countable_right (measurable_stateErrorFiber ρ)
  have hm := hf.comp ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact hm

end Paper26.MultiscaleMatrixBridge


