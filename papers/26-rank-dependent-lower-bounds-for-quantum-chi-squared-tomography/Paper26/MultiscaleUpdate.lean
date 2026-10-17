import Paper26.MultiscaleRefinement
import Paper26.MeasurableSpectralSelection
import Paper26.CoordinateTransport
import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Sum

/-!
# Actual measurable block updates for multiscale refinement

An active block is indexed by a finite subset of the fixed ambient labels.
A selected block eigenbasis is extended by the identity on its complement.
This avoids moving the previously frozen labels.  The threshold convention
is exactly `lambda <= eigenvalue` for freezing, including equality.

No learning guarantee or probability of a successful execution is assumed
by these definitions.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder
open MeasureTheory

namespace Paper26.MultiscaleUpdate
open Normalization MeasurableSpectralSelection QuantumModel

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))
local instance matrixBorelSpace (m n : Type*) [Fintype m] [Fintype n] : BorelSpace (Matrix m n ℂ) :=
  inferInstanceAs (BorelSpace (m → n → ℂ))

abbrev BlockIndex (S : Finset ι) := {i // i ∈ S}

/-- A genuine block diagonal unitary before relabeling back to the ambient space. -/
def sumUnitary (S : Finset ι) (Q : Matrix.unitaryGroup (BlockIndex S) ℂ) :
    Matrix.unitaryGroup (BlockIndex S ⊕ {i // i ∉ S}) ℂ := by
  let D : Matrix (BlockIndex S ⊕ {i // i ∉ S}) (BlockIndex S ⊕ {i // i ∉ S}) ℂ :=
    Matrix.fromBlocks (Q : Matrix _ _ ℂ) 0 0 1
  refine ⟨D, Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  change D * Dᴴ = 1
  dsimp [D]
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    PositiveLossBridge.unitary_right Q, Matrix.fromBlocks_one]

/-- The actual ambient basis update, equal to the identity off the active block. -/
def extendUnitary (S : Finset ι) (Q : Matrix.unitaryGroup (BlockIndex S) ℂ) :
    Matrix.unitaryGroup ι ℂ := by
  let e := Equiv.sumCompl (fun i : ι => i ∈ S)
  refine ⟨CoordinateTransport.matrix e (sumUnitary S Q), Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  change CoordinateTransport.matrix e (sumUnitary S Q) *
    (CoordinateTransport.matrix e (sumUnitary S Q))ᴴ = 1
  have hc : (CoordinateTransport.matrix e (sumUnitary S Q))ᴴ =
      CoordinateTransport.matrix e ((sumUnitary S Q : Matrix _ _ ℂ)ᴴ) := rfl
  rw [hc, ← CoordinateTransport.matrix_mul, PositiveLossBridge.unitary_right,
    CoordinateTransport.matrix_one]

@[simp] theorem extendUnitary_inside (S : Finset ι)
    (Q : Matrix.unitaryGroup (BlockIndex S) ℂ) (i k : BlockIndex S) :
    (extendUnitary S Q : Matrix ι ι ℂ) i k = Q i k := by
  simp [extendUnitary, CoordinateTransport.matrix, sumUnitary,
    Equiv.sumCompl_apply_symm_of_pos, i.property, k.property]

/-- Every frozen row or column is fixed by this actual unitary. -/
theorem extendUnitary_outside (S : Finset ι) (Q : Matrix.unitaryGroup (BlockIndex S) ℂ)
    (i k : ι) (h : i ∉ S ∨ k ∉ S) :
    (extendUnitary S Q : Matrix ι ι ℂ) i k = (1 : Matrix ι ι ℂ) i k := by
  by_cases hi : i ∈ S <;> by_cases hk : k ∈ S
  · exact False.elim (h.elim (fun hn => hn hi) (fun hn => hn hk))
  · have hik : i ≠ k := by intro he; subst k; exact hk hi
    simp [extendUnitary, CoordinateTransport.matrix, sumUnitary,
      Equiv.sumCompl_apply_symm_of_pos, Equiv.sumCompl_apply_symm_of_neg,
      hi, hk, Matrix.one_apply_ne hik]
  · have hik : i ≠ k := by intro he; subst k; exact hi hk
    simp [extendUnitary, CoordinateTransport.matrix, sumUnitary,
      Equiv.sumCompl_apply_symm_of_pos, Equiv.sumCompl_apply_symm_of_neg,
      hi, hk, Matrix.one_apply_ne hik]
  · simp [extendUnitary, CoordinateTransport.matrix, sumUnitary,
      Equiv.sumCompl_apply_symm_of_neg, hi, hk, Matrix.one_apply, Subtype.ext_iff]

/-- Joint Borel measurability of the extension; only finitely many actual
matrix entries are selected or filled by constant identity entries. -/
theorem measurable_extendUnitary (S : Finset ι) : Measurable (extendUnitary S) := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro k
  change Measurable (fun Q : Matrix.unitaryGroup (BlockIndex S) ℂ =>
    (extendUnitary S Q : Matrix ι ι ℂ) i k)
  by_cases hi : i ∈ S <;> by_cases hk : k ∈ S
  · have he (Q : Matrix.unitaryGroup (BlockIndex S) ℂ) :
        (extendUnitary S Q : Matrix ι ι ℂ) i k = Q ⟨i, hi⟩ ⟨k, hk⟩ := extendUnitary_inside S Q ⟨i, hi⟩ ⟨k, hk⟩
    simp_rw [he]
    exact (measurable_pi_apply (⟨k, hk⟩ : BlockIndex S)).comp
      ((measurable_pi_apply (⟨i, hi⟩ : BlockIndex S)).comp measurable_subtype_coe)
  · have he (Q : Matrix.unitaryGroup (BlockIndex S) ℂ) := extendUnitary_outside S Q i k (Or.inr hk)
    simp_rw [he]
    exact measurable_const
  · have he (Q : Matrix.unitaryGroup (BlockIndex S) ℂ) := extendUnitary_outside S Q i k (Or.inl hi)
    simp_rw [he]
    exact measurable_const
  · have he (Q : Matrix.unitaryGroup (BlockIndex S) ℂ) := extendUnitary_outside S Q i k (Or.inl hi)
    simp_rw [he]
    exact measurable_const

/-- A PSD block estimate is an actual matrix, with its inherited entry sigma-algebra. -/
abbrev PositiveBlock (S : Finset ι) := {C : Matrix (BlockIndex S) (BlockIndex S) ℂ // C.PosSemidef}

def positiveToHermitian (S : Finset ι) (C : PositiveBlock S) : HermitianMatrix (BlockIndex S) :=
  ⟨C.val, C.property.isHermitian⟩

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_positiveToHermitian (S : Finset ι) : Measurable (positiveToHermitian S) :=
  measurable_subtype_coe.subtype_mk

/-- The ordered eigenvalues of the estimate, filled by zero off the active block. -/
def blockValues (S : Finset ι) (C : PositiveBlock S) (i : ι) : ℝ :=
  if hi : i ∈ S then C.property.isHermitian.eigenvalues ⟨i, hi⟩ else 0

def selectedUpdate (B : CompactFiberSelectionInput.{u,u}) (S : Finset ι) (C : PositiveBlock S) :
    Matrix.unitaryGroup ι ℂ := extendUnitary S (basis B (positiveToHermitian S C))

/-- The active set after this stage uses the strict complementary branch;
values exactly equal to the threshold are frozen. -/
def remaining (S : Finset ι) (C : PositiveBlock S) (lam : ℝ) : Finset ι :=
  S.filter (fun i => blockValues S C i < lam)

def retained (S : Finset ι) (C : PositiveBlock S) (a : ι → ℝ) (lam : ℝ) (i : ι) : ℝ :=
  if i ∈ S then if lam ≤ blockValues S C i then blockValues S C i else 0 else a i

omit [Fintype ι] in
@[simp] theorem mem_remaining (S : Finset ι) (C : PositiveBlock S) (lam : ℝ) (i : ι) :
    i ∈ remaining S C lam ↔ i ∈ S ∧ blockValues S C i < lam := by simp [remaining]

omit [Fintype ι] in
theorem remaining_subset (S : Finset ι) (C : PositiveBlock S) (lam : ℝ) : remaining S C lam ⊆ S :=
  Finset.filter_subset _ _

omit [Fintype ι] in
theorem frozen_iff (S : Finset ι) (C : PositiveBlock S) (lam : ℝ) (i : ι) (hi : i ∈ S) :
    i ∉ remaining S C lam ↔ lam ≤ blockValues S C i := by simp [mem_remaining, hi]

omit [Fintype ι] in
theorem blockValues_nonneg (S : Finset ι) (C : PositiveBlock S) (i : ι) :
    0 ≤ blockValues S C i := by
  unfold blockValues
  split_ifs
  · exact C.property.eigenvalues_nonneg _
  · rfl

instance finiteSubsetMeasurableSpace : MeasurableSpace (Finset ι) := ⊤

omit [Fintype ι] in
theorem measurable_blockValues (B : CompactFiberSelectionInput.{u,u}) (S : Finset ι) (i : ι) :
    Measurable (fun C : PositiveBlock S => blockValues S C i) := by
  by_cases hi : i ∈ S
  · simp only [blockValues, dif_pos hi]
    change Measurable (fun C : PositiveBlock S =>
      (positiveToHermitian S C).property.eigenvalues (⟨i, hi⟩ : BlockIndex S))
    have hm : Measurable (fun A : HermitianMatrix (BlockIndex S) =>
        A.property.eigenvalues (⟨i, hi⟩ : BlockIndex S)) :=
      measurable_eigenvalue (ι := BlockIndex S) B _
    exact hm.comp (measurable_positiveToHermitian S)
  · simp only [blockValues, dif_neg hi]
    exact measurable_const

theorem measurable_selectedUpdate (B : CompactFiberSelectionInput.{u,u}) (S : Finset ι) :
    Measurable (selectedUpdate B S) :=
  (measurable_extendUnitary S).comp ((measurable_basis B).comp (measurable_positiveToHermitian S))

/-- This includes a variable threshold and the exact strict remaining branch. -/
theorem measurable_remaining (B : CompactFiberSelectionInput.{u,u}) (S : Finset ι) :
    Measurable (fun p : PositiveBlock S × ℝ => remaining S p.1 p.2) := by
  classical
  let f : PositiveBlock S × ℝ → Set ι := fun p => {i | i ∈ S ∧ blockValues S p.1 i < p.2}
  have hf : Measurable f := by
    apply measurable_pi_lambda
    intro i
    exact measurable_const.and
      (measurableSet_lt ((measurable_blockValues B S i).comp measurable_fst) measurable_snd).mem
  have ht : Measurable (fun T : Set ι => T.toFinite.toFinset) := measurable_of_finite _
  have he : (fun p : PositiveBlock S × ℝ => remaining S p.1 p.2) =
      (fun p => (f p).toFinite.toFinset) := by
    funext p
    ext i
    simp [f, mem_remaining]
  rw [he]
  exact ht.comp hf

omit [Fintype ι] in
theorem measurable_retained (B : CompactFiberSelectionInput.{u,u}) (S : Finset ι) :
    Measurable (fun p : PositiveBlock S × ((ι → ℝ) × ℝ) => retained S p.1 p.2.1 p.2.2) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ∈ S
  · simp only [retained, if_pos hi]
    exact Measurable.ite
      (measurableSet_le (measurable_snd.comp measurable_snd)
        ((measurable_blockValues B S i).comp measurable_fst))
      ((measurable_blockValues B S i).comp measurable_fst) measurable_const
  · simp only [retained, if_neg hi]
    exact (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)

/-- Actual embedding of a block matrix in the fixed ambient coordinates. -/
def embedBlock (S : Finset ι) (C : Matrix (BlockIndex S) (BlockIndex S) ℂ) : Matrix ι ι ℂ :=
  CoordinateTransport.matrix (Equiv.sumCompl (fun i : ι => i ∈ S)) (Matrix.fromBlocks C 0 0 0)

omit [Fintype ι] in
@[simp] theorem embedBlock_inside (S : Finset ι) (C : Matrix (BlockIndex S) (BlockIndex S) ℂ)
    (i k : BlockIndex S) : embedBlock S C i k = C i k := by
  simp [embedBlock, CoordinateTransport.matrix, Equiv.sumCompl_apply_symm_of_pos, i.property, k.property]

omit [Fintype ι] in
theorem embedBlock_outside (S : Finset ι) (C : Matrix (BlockIndex S) (BlockIndex S) ℂ)
    (i k : ι) (h : i ∉ S ∨ k ∉ S) : embedBlock S C i k = 0 := by
  by_cases hi : i ∈ S <;> by_cases hk : k ∈ S
  · exact False.elim (h.elim (fun hn => hn hi) (fun hn => hn hk))
  · simp [embedBlock, CoordinateTransport.matrix, Equiv.sumCompl_apply_symm_of_pos,
      Equiv.sumCompl_apply_symm_of_neg, hi, hk]
  · simp [embedBlock, CoordinateTransport.matrix, Equiv.sumCompl_apply_symm_of_pos,
      Equiv.sumCompl_apply_symm_of_neg, hi, hk]
  · simp [embedBlock, CoordinateTransport.matrix, Equiv.sumCompl_apply_symm_of_neg, hi, hk]

theorem embedBlock_conjugate (S : Finset ι) (Q : Matrix.unitaryGroup (BlockIndex S) ℂ)
    (C : Matrix (BlockIndex S) (BlockIndex S) ℂ) :
    embedBlock S (conjugate (Q : Matrix _ _ ℂ) C) =
      conjugate (extendUnitary S Q : Matrix ι ι ℂ) (embedBlock S C) := by
  let e := Equiv.sumCompl (fun i : ι => i ∈ S)
  have hc : (extendUnitary S Q : Matrix ι ι ℂ)ᴴ =
      CoordinateTransport.matrix e ((sumUnitary S Q : Matrix _ _ ℂ)ᴴ) := rfl
  simp only [conjugate, hc]
  change CoordinateTransport.matrix e (Matrix.fromBlocks ((Q : Matrix _ _ ℂ) * C * (Q : Matrix _ _ ℂ)ᴴ) 0 0 0) =
    CoordinateTransport.matrix e (sumUnitary S Q) *
      CoordinateTransport.matrix e (Matrix.fromBlocks C 0 0 0) *
        CoordinateTransport.matrix e ((sumUnitary S Q : Matrix _ _ ℂ)ᴴ)
  rw [← CoordinateTransport.matrix_mul, ← CoordinateTransport.matrix_mul]
  congr 1
  simp [sumUnitary, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

omit [Fintype ι] in
theorem embedBlock_diagonal (S : Finset ι) (a : BlockIndex S → ℝ) :
    embedBlock S (diagonalMatrix a) = diagonalMatrix
      (fun i => if hi : i ∈ S then a ⟨i, hi⟩ else 0) := by
  ext i k
  by_cases hik : i = k
  · subst k
    by_cases hi : i ∈ S
    · rw [embedBlock_inside S _ ⟨i, hi⟩ ⟨i, hi⟩]
      simp [diagonalMatrix, hi]
    · rw [embedBlock_outside S _ i i (Or.inl hi)]
      simp [diagonalMatrix, hi]
  · by_cases hi : i ∈ S <;> by_cases hk : k ∈ S
    · rw [embedBlock_inside S _ ⟨i, hi⟩ ⟨k, hk⟩]
      have hne : (⟨i, hi⟩ : BlockIndex S) ≠ ⟨k, hk⟩ := fun h => hik (congrArg Subtype.val h)
      simp [diagonalMatrix, hik]
    · rw [embedBlock_outside S _ i k (Or.inr hk)]
      simp [diagonalMatrix, hik]
    · rw [embedBlock_outside S _ i k (Or.inl hi)]
      simp [diagonalMatrix, hik]
    · rw [embedBlock_outside S _ i k (Or.inl hi)]
      simp [diagonalMatrix, hik]

/-- The chosen within-block eigenbasis gives a genuine full-matrix spectral
identity while fixing all frozen coordinates. -/
theorem selectedUpdate_diagonalizes (B : CompactFiberSelectionInput.{u,u})
    (S : Finset ι) (C : PositiveBlock S) :
    embedBlock S C.val = conjugate (selectedUpdate B S C : Matrix ι ι ℂ)
      (diagonalMatrix (blockValues S C)) := by
  have hc := basis_reconstruct B (positiveToHermitian S C)
  change C.val = conjugate (basis B (positiveToHermitian S C) : Matrix _ _ ℂ)
    (diagonalMatrix C.property.isHermitian.eigenvalues) at hc
  conv_lhs => rw [hc]
  rw [embedBlock_conjugate, embedBlock_diagonal]
  rfl

/-- All possible block estimates at one stage. Only the estimate belonging
to the current active subset is read by the actual update. -/
abbrev EstimateFamily := ∀ S : Finset ι, PositiveBlock S

/-- Active labels, accumulated unitary, frozen output, and first freeze time.
The clock is initialized to the terminal value and changed only on freezing. -/
abbrev State := Finset ι × (Matrix.unitaryGroup ι ℂ × ((ι → ℝ) × (ι → ℕ)))

abbrev Payload := (Matrix.unitaryGroup ι ℂ × ((ι → ℝ) × (ι → ℕ))) × EstimateFamily (ι := ι)

def initial (L : ℕ) : State (ι := ι) := (Finset.univ, (1, (0, fun _ => L)))

def stepFiber (B : CompactFiberSelectionInput.{u,u}) (j : ℕ) (lam : ℝ)
    (S : Finset ι) (q : Payload (ι := ι)) : State (ι := ι) :=
  (remaining S (q.2 S) lam,
    (q.1.1 * selectedUpdate B S (q.2 S),
      (retained S (q.2 S) q.1.2.1 lam,
        fun i => if i ∈ S ∧ lam ≤ blockValues S (q.2 S) i then j else q.1.2.2 i)))

def step (B : CompactFiberSelectionInput.{u,u}) (j : ℕ) (lam : ℝ)
    (st : State (ι := ι)) (F : EstimateFamily (ι := ι)) : State (ι := ι) :=
  stepFiber B j lam st.1 (st.2, F)

theorem measurable_unitary_mul : Measurable
    (fun p : Matrix.unitaryGroup ι ℂ × Matrix.unitaryGroup ι ℂ => p.1 * p.2) := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro k
  change Measurable (fun p : Matrix.unitaryGroup ι ℂ × Matrix.unitaryGroup ι ℂ =>
    ∑ q, (p.1 : Matrix ι ι ℂ) i q * (p.2 : Matrix ι ι ℂ) q k)
  have h1 : Measurable (fun p : Matrix.unitaryGroup ι ℂ × Matrix.unitaryGroup ι ℂ =>
      (p.1 : Matrix ι ι ℂ)) := measurable_subtype_coe.comp measurable_fst
  have h2 : Measurable (fun p : Matrix.unitaryGroup ι ℂ × Matrix.unitaryGroup ι ℂ =>
      (p.2 : Matrix ι ι ℂ)) := measurable_subtype_coe.comp measurable_snd
  exact Finset.measurable_sum Finset.univ fun q _ =>
    ((measurable_pi_apply q).comp ((measurable_pi_apply i).comp h1)).mul
      ((measurable_pi_apply k).comp ((measurable_pi_apply q).comp h2))

theorem measurable_stepFiber (B : CompactFiberSelectionInput.{u,u}) (j : ℕ) (lam : ℝ)
    (S : Finset ι) : Measurable (stepFiber B j lam S) := by
  have hc : Measurable (fun q : Payload (ι := ι) => q.2 S) :=
    (measurable_pi_apply S).comp measurable_snd
  have hU : Measurable (fun q : Payload (ι := ι) => q.1.1) := measurable_fst.comp measurable_fst
  have ha : Measurable (fun q : Payload (ι := ι) => q.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have ht : Measurable (fun q : Payload (ι := ι) => q.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hl : Measurable (fun _q : Payload (ι := ι) => lam) := measurable_const
  have hs := (measurable_remaining B S).comp (hc.prodMk hl)
  have hu := measurable_unitary_mul.comp (hU.prodMk ((measurable_selectedUpdate B S).comp hc))
  have hav := (measurable_retained B S).comp (hc.prodMk (ha.prodMk hl))
  have htv : Measurable (fun q : Payload (ι := ι) =>
      fun i => if i ∈ S ∧ lam ≤ blockValues S (q.2 S) i then j else q.1.2.2 i) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, true_and]
      exact Measurable.ite (measurableSet_le measurable_const ((measurable_blockValues B S i).comp hc))
        measurable_const ((measurable_pi_apply i).comp ht)
    · simp only [hi, false_and, if_false]
      exact (measurable_pi_apply i).comp ht
  unfold stepFiber
  exact hs.prodMk (hu.prodMk (hav.prodMk htv))

/-- The finite active-subset case distinction is a Borel map. -/
theorem measurable_step (B : CompactFiberSelectionInput.{u,u}) (j : ℕ) (lam : ℝ) :
    Measurable (fun p : State (ι := ι) × EstimateFamily (ι := ι) => step B j lam p.1 p.2) := by
  have hf : Measurable (fun p : Finset ι × Payload (ι := ι) => stepFiber B j lam p.1 p.2) :=
    measurable_from_prod_countable_right (measurable_stepFiber B j lam)
  exact hf.comp ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

/-- Actual deterministic recursion driven by the full recorded estimate data.
After the last stage it stays at its final state. -/
def execute (B : CompactFiberSelectionInput.{u,u}) (L : ℕ) (lower : Fin L → ℝ)
    (F : Fin L → EstimateFamily (ι := ι)) : ℕ → State (ι := ι)
  | 0 => initial L
  | t + 1 => if ht : t < L then step B t (lower ⟨t, ht⟩) (execute B L lower F t) (F ⟨t, ht⟩)
      else execute B L lower F t

theorem measurable_execute (B : CompactFiberSelectionInput.{u,u}) (L : ℕ) (lower : Fin L → ℝ)
    (t : ℕ) : Measurable (fun F : Fin L → EstimateFamily (ι := ι) => execute B L lower F t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    by_cases ht : t < L
    · simp only [execute, dif_pos ht]
      exact (measurable_step B t (lower ⟨t, ht⟩)).comp
        (ih.prodMk (measurable_pi_apply (⟨t, ht⟩ : Fin L)))
    · simpa only [execute, dif_neg ht] using ih

/-- Fill every final remaining coordinate by the last positive threshold. -/
def finalSpectrum (B : CompactFiberSelectionInput.{u,u}) (L : ℕ) [NeZero L]
    (lower : Fin L → ℝ) (F : Fin L → EstimateFamily (ι := ι)) (i : ι) : ℝ :=
  if i ∈ (execute B L lower F L).1 then lower (MultiscaleRefinement.lastStage L)
  else (execute B L lower F L).2.2.1 i

def finalMatrix (B : CompactFiberSelectionInput.{u,u}) (L : ℕ) [NeZero L]
    (lower : Fin L → ℝ) (F : Fin L → EstimateFamily (ι := ι)) : Matrix ι ι ℂ :=
  conjugate ((execute B L lower F L).2.1 : Matrix ι ι ℂ) (diagonalMatrix (finalSpectrum B L lower F))

theorem measurable_finalSpectrum (B : CompactFiberSelectionInput.{u,u}) (L : ℕ) [NeZero L]
    (lower : Fin L → ℝ) : Measurable (fun F : Fin L → EstimateFamily (ι := ι) => finalSpectrum B L lower F) := by
  apply measurable_pi_lambda
  intro i
  have hst := measurable_execute (ι := ι) B L lower L
  have hS : Measurable (fun F : Fin L → EstimateFamily (ι := ι) => i ∈ (execute B L lower F L).1) :=
    (measurable_of_finite (fun S : Finset ι => i ∈ S)).comp (measurable_fst.comp hst)
  have ha : Measurable (fun F : Fin L → EstimateFamily (ι := ι) => (execute B L lower F L).2.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hst)))
  exact Measurable.ite hS.setOf measurable_const ha

theorem measurable_finalMatrix (B : CompactFiberSelectionInput.{u,u}) (L : ℕ) [NeZero L]
    (lower : Fin L → ℝ) : Measurable (finalMatrix (ι := ι) B L lower) := by
  have hst := measurable_execute (ι := ι) B L lower L
  have hco : Measurable (fun U : Matrix.unitaryGroup ι ℂ => (U : Matrix ι ι ℂ)) := measurable_subtype_coe
  have hU := hco.comp (measurable_fst.comp (measurable_snd.comp hst))
  have hc : Measurable (fun p : Matrix ι ι ℂ × (ι → ℝ) => conjugate p.1 (diagonalMatrix p.2)) :=
    continuous_spectralConjugate.measurable
  have hm := hc.comp (hU.prodMk (measurable_finalSpectrum B L lower))
  exact hm

end Paper26.MultiscaleUpdate



