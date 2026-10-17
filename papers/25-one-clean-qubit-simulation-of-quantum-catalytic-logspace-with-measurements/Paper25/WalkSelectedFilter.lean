import Paper25.SelectedPreparation
import Paper25.GlobalFilterError

/-!
# Actual coherent walk filter to the physical signed-bias readout

The circuit is the actual controlled-power PE/rotation/uncompute matrix.
Its zero phase, rotation and original block-ancilla coordinates are specified
explicitly. The published unitary spectral theorem is exposed only through
`UnitaryEigenbasis` for the walk; no approximation assertion is assumed.
-/

noncomputable section
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
open Matrix

namespace Paper25.SelectedFilter

section BlockCircuit
variable {ι a : Type*} [Fintype ι] [DecidableEq ι] [Fintype a] [DecidableEq a]

abbrev DilationIndex (ι : Type*) [Fintype ι] :=
  Fin (Fintype.card ι) ⊕ Fin (Fintype.card ι)
abbrev BlockDilation (a ι : Type*) [Fintype ι] :=
  (a × Fin (Fintype.card ι)) ⊕ (a × Fin (Fintype.card ι))

/-- The actual original block-ancilla coordinate, in both h sectors. -/
def blockEmbedding (q : a) : DilationIndex ι → BlockDilation a ι :=
  Sum.map (fun i => (q, i)) (fun i => (q, i))

lemma blockEmbedding_injective (q : a) :
    Function.Injective (blockEmbedding (ι := ι) q) := by
  intro x y h
  cases x <;> cases y <;> simp_all [blockEmbedding]

/-- The original block-ancilla zero column used by the compression walk. -/
def blockColumn (q : a) : Matrix (BlockDilation a ι) (DilationIndex ι) ℂ :=
  basisColumn (blockEmbedding q)

lemma blockColumn_isometry (q : a) :
    (blockColumn (ι := ι) q).conjTranspose * blockColumn (ι := ι) q = 1 :=
  basisColumn_isometry _ (blockEmbedding_injective q)

/-- The actual compression walk of the Hermitian dilation of UA. -/
def blockWalk (UA : Matrix (a × Fin (Fintype.card ι)) (a × Fin (Fintype.card ι)) ℂ)
    (q : a) : Matrix (BlockDilation a ι) (BlockDilation a ι) ℂ :=
  compressionWalk (isometryProjector (blockColumn q)) (hermitianDilation UA)

/-- Actual controlled-power PE, filter rotations, and inverse PE. -/
def actualWalkFilter
    (UA : Matrix (a × Fin (Fintype.card ι)) (a × Fin (Fintype.card ι)) ℂ)
    (q : a) (M : ℕ) (lam : ℝ) :
    Matrix ((Fin M × BlockDilation a ι) ⊕ (Fin M × BlockDilation a ι))
      ((Fin M × BlockDilation a ι) ⊕ (Fin M × BlockDilation a ι)) ℂ :=
  coherentWalkFilter (blockWalk UA q) M (lam / 3)

/-- The effective block is extracted from the actual circuit by specified
zero rotation, zero phase and original block-ancilla coordinates. -/
def actualFilterBlock
    (UA : Matrix (a × Fin (Fintype.card ι)) (a × Fin (Fintype.card ι)) ℂ)
    (q : a) (M : ℕ) (hM : 0 < M) (lam : ℝ) :
    Matrix (DilationIndex ι) (DilationIndex ι) ℂ :=
  (actualWalkFilter UA q M lam).submatrix
    (fun i => Sum.inl ((⟨0, hM⟩ : Fin M), blockEmbedding q i))
    (fun i => Sum.inl ((⟨0, hM⟩ : Fin M), blockEmbedding q i))

lemma actualFilterBlock_eq_compression
    (UA : Matrix (a × Fin (Fintype.card ι)) (a × Fin (Fintype.card ι)) ℂ)
    (q : a) (M : ℕ) (hM : 0 < M) (lam : ℝ) :
    actualFilterBlock UA q M hM lam =
      (blockColumn q).conjTranspose *
        (actualWalkFilter UA q M lam).submatrix
          (fun i => Sum.inl ((⟨0, hM⟩ : Fin M), i))
          (fun i => Sum.inl ((⟨0, hM⟩ : Fin M), i)) * blockColumn q := by
  rw [blockColumn, basisColumn_cross]
  rfl

/-- Equation (13) for the actual block-encoding isometry, rather than an
assumed compressed Hermitian matrix. -/
lemma blockColumn_compression
    (A : Matrix ι ι ℂ)
    (UA : Matrix (a × Fin (Fintype.card ι)) (a × Fin (Fintype.card ι)) ℂ)
    (q : a)
    (hA : UA.submatrix (fun i => (q, i)) (fun i => (q, i)) =
      (1 / 3 : ℂ) • Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) A) :
    isometryCompression (blockColumn q) (hermitianDilation UA) =
      ((1 / 3 : ℝ) : ℂ) • dilation
        (Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) A) := by
  unfold isometryCompression blockColumn
  rw [basisColumn_cross]
  exact history_dilation_block q UA _ hA

/-- The full-space error input in the selected-history theorem is discharged
by the actual coherent PE circuit. Its only external mathematical input is
the published unitary eigenbasis theorem for this walk. -/
theorem actualFilterBlock_error
    (A : Matrix ι ι ℂ)
    (UA : Matrix (a × Fin (Fintype.card ι)) (a × Fin (Fintype.card ι)) ℂ)
    (q : a)
    (hA : UA.submatrix (fun i => (q, i)) (fun i => (q, i)) =
      (1 / 3 : ℂ) • Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) A)
    (D : UnitaryEigenbasis (blockWalk UA q))
    (M : ℕ) (hM : 0 < M) (lam eps : ℝ)
    (hlam : 0 < lam) (hlamle : lam / 3 ≤ 1)
    (heps : 0 < eps) (hepsle : eps ≤ 1)
    (hMdef : 4096 / ((lam / 3) * eps ^ 2) ≤ (M : ℝ)) :
    ‖actualFilterBlock UA q M hM lam - idealFilter A lam‖ ≤ eps / 8 := by
  have h := coherentWalkFilter_compression_error (hermitianDilation UA) (blockColumn q)
    (hermitianDilation_hermitian UA) (blockColumn_isometry q) D M hM (lam / 3) eps
    (by positivity) hlamle heps hepsle hMdef
  rw [blockColumn_compression A UA q hA] at h
  rw [actualFilterBlock_eq_compression, idealFilter,
    filterMat_eq_filterRat _ _ _ (by positivity)]
  exact h

/-- The same concrete PE circuit is unitary when its actual block encoder
is unitary. -/
theorem actualWalkFilter_unitary
    (UA : Matrix (a × Fin (Fintype.card ι)) (a × Fin (Fintype.card ι)) ℂ)
    (hUA : UA ∈ Matrix.unitaryGroup (a × Fin (Fintype.card ι)) ℂ)
    (q : a) (M : ℕ) (hM : 0 < M) (lam : ℝ) (hlam : 0 < lam) :
    actualWalkFilter UA q M lam ∈ Matrix.unitaryGroup
      ((Fin M × BlockDilation a ι) ⊕ (Fin M × BlockDilation a ι)) ℂ := by
  exact coherentWalkFilter_compression_unitary (hermitianDilation UA) (blockColumn q)
    (hermitianDilation_hermitian UA) (hermitianDilation_unitary UA hUA)
    (blockColumn_isometry q) M hM (lam / 3) (by positivity)

/-- Rotation, phase and the original block ancilla are all actual auxiliary
registers of the concrete unitary filter. -/
abbrev CoherentAux (a : Type*) (M : ℕ) := (Fin 2 × Fin M) × a

/-- Reorder the actual circuit's two sum selectors into auxiliary registers
and the h/data dilation registers. -/
def circuitAuxiliaryIndex (M : ℕ) :
    (CoherentAux a M × DilationIndex ι) ≃
      ((Fin M × BlockDilation a ι) ⊕ (Fin M × BlockDilation a ι)) where
  toFun p := if p.1.1.1 = 0 then Sum.inl (p.1.1.2, blockEmbedding p.1.2 p.2)
    else Sum.inr (p.1.1.2, blockEmbedding p.1.2 p.2)
  invFun p := match p with
    | Sum.inl (j, Sum.inl (q, i)) => (((0, j), q), Sum.inl i)
    | Sum.inl (j, Sum.inr (q, i)) => (((0, j), q), Sum.inr i)
    | Sum.inr (j, Sum.inl (q, i)) => (((1, j), q), Sum.inl i)
    | Sum.inr (j, Sum.inr (q, i)) => (((1, j), q), Sum.inr i)
  left_inv := by
    rintro ⟨⟨⟨b,j⟩,q⟩,i⟩
    fin_cases b <;> cases i <;> rfl
  right_inv := by
    intro p
    rcases p with ⟨j,i⟩ | ⟨j,i⟩ <;> cases i <;> rfl

/-- The actual unitary PE filter, with all its ancillas grouped into one
register for one-clean-qubit readout. -/
def actualAuxFilter
    (UA : Matrix (a × Fin (Fintype.card ι)) (a × Fin (Fintype.card ι)) ℂ)
    (q : a) (M : ℕ) (lam : ℝ) :
    Matrix (CoherentAux a M × DilationIndex ι) (CoherentAux a M × DilationIndex ι) ℂ :=
  (actualWalkFilter UA q M lam).submatrix (circuitAuxiliaryIndex M) (circuitAuxiliaryIndex M)

/-- The effective block is literally the zero-auxiliary block of that actual
unitary, with no approximation or implementation certificate assumed. -/
lemma actualAuxFilter_zero_block
    (UA : Matrix (a × Fin (Fintype.card ι)) (a × Fin (Fintype.card ι)) ℂ)
    (q : a) (M : ℕ) (hM : 0 < M) (lam : ℝ) :
    (actualAuxFilter UA q M lam).submatrix
      (fun i => ((((0, (⟨0, hM⟩ : Fin M)), q) : CoherentAux a M), i))
      (fun i => ((((0, (⟨0, hM⟩ : Fin M)), q) : CoherentAux a M), i)) =
      actualFilterBlock UA q M hM lam := rfl

/-- The reordered auxiliary/data representation is still an actual unitary. -/
theorem actualAuxFilter_unitary
    (UA : Matrix (a × Fin (Fintype.card ι)) (a × Fin (Fintype.card ι)) ℂ)
    (hUA : UA ∈ Matrix.unitaryGroup (a × Fin (Fintype.card ι)) ℂ)
    (q : a) (M : ℕ) (hM : 0 < M) (lam : ℝ) (hlam : 0 < lam) :
    OneCleanQubit.Unitary (actualAuxFilter UA q M lam) := by
  have h := actualWalkFilter_unitary UA hUA q M hM lam hlam
  apply StatePreparation.unitary_reindex (circuitAuxiliaryIndex M)
  exact ⟨h.1, h.2⟩

end BlockCircuit

section SourceReadout
variable {a : Type*} [Fintype a] [DecidableEq a]

/-- The actual PE unitary and the physical F readout obey equation (19) for
the source's signed acceptance bias. The full filter error, ideal selected
trace and selected-block error are all derived in this theorem. The only
spectral input is the explicitly disclosed unitary eigenbasis theorem. -/
theorem eq19_actual_coherent_filter (ell s T D : ℕ)
    (S : ℕ → Matrix
      (Fin ((Fintype.card (StatePreparation.WorkSpace s)) ^ 2) × Fin (D ^ 2))
      (Fin ((Fintype.card (StatePreparation.WorkSpace s)) ^ 2) × Fin (D ^ 2)) ℂ)
    (hJ : T + 1 ≤ Fintype.card (StatePreparation.Bits ell)) (hD : 0 < D)
    (hchannels : CPTPFrobBound S T (Fintype.card (StatePreparation.WorkSpace s) * D))
    (η : Matrix (StatePreparation.WorkSpace s) (StatePreparation.WorkSpace s) ℂ)
    (hη : η.IsHermitian) (ht : η.trace = 1)
    (hrestore : ExactRestoration (chainProd S 0 T)
      (SourceBias.historyOmega (StatePreparation.zeroWork s)) (SourceBias.historyEta η))
    (UA : Matrix (a × Fin (Fintype.card (PhysicalHistory ell s (D ^ 2))))
      (a × Fin (Fintype.card (PhysicalHistory ell s (D ^ 2)))) ℂ)
    (hUA : UA ∈ Matrix.unitaryGroup (a × Fin (Fintype.card (PhysicalHistory ell s (D ^ 2)))) ℂ)
    (q : a)
    (hA : UA.submatrix (fun i => (q, i)) (fun i => (q, i)) = (1 / 3 : ℂ) •
      Matrix.reindex (Fintype.equivFin (PhysicalHistory ell s (D ^ 2)))
        (Fintype.equivFin (PhysicalHistory ell s (D ^ 2)))
          (1 - historyShift T (Fintype.card (StatePreparation.Bits ell)) S))
    (Dspec : UnitaryEigenbasis (blockWalk UA q))
    (M : ℕ) (hM : 0 < M) (lam eps : ℝ)
    (hlam : 0 < lam) (hlamle : lam / 3 ≤ 1)
    (heps : 0 < eps) (hepsle : eps ≤ 1)
    (hMdef : 4096 / ((lam / 3) * eps ^ 2) ≤ (M : ℝ)) :
    OneCleanQubit.Unitary (actualAuxFilter UA q M lam) ∧
    |normalizedReTrace (physicalReadout ell s (D ^ 2)
        ((clockIndex ell).symm (⟨T, by omega⟩ : Fin (Fintype.card (StatePreparation.Bits ell))))
          (actualFilterBlock UA q M hM lam)) -
      lam * (2 * SourceBias.accept η - 1) /
        Real.sqrt (Fintype.card (StatePreparation.WorkSpace s))| ≤
      (lam ^ 2 / 2) * (Fintype.card (StatePreparation.Bits ell) : ℝ) ^ 2 *
        (Fintype.card (StatePreparation.WorkSpace s) : ℝ) ^ 2 + eps / 8 := by
  refine ⟨actualAuxFilter_unitary UA hUA q M hM lam hlam, ?_⟩
  apply eq19_physical_readout ell s T D S hJ hD hchannels η hη ht hrestore
    lam hlam (eps / 8) (actualFilterBlock UA q M hM lam)
  exact actualFilterBlock_error _ UA q hA Dspec M hM lam eps hlam hlamle heps hepsle hMdef

end SourceReadout

end Paper25.SelectedFilter
