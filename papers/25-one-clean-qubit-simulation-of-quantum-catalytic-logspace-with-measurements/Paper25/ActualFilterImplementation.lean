import Paper25.WalkSelectedFilter
import Paper25.SourceSimulation
import Paper25.Resources
import Paper25.CircuitModel
import Paper25.HistoryEncoding

/-!
# Instantiating the physical filter implementation with the actual PE circuit

All auxiliary registers are explicitly enumerated as physical qubits. The
implementation record is constructed from the actual coherent walk filter;
its full-space approximation field is proved, rather than postulated.
-/

noncomputable section
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
open Matrix
namespace Paper25.SelectedFilter
open StatePreparation SourceSimulation

abbrev PhysicalEncoderIndex (ell s c : ℕ) :=
  Fin (Fintype.card (PhysicalHistory ell s ((Fintype.card (Bits c)) ^ 2)))
abbrev PhysicalEncoder (a : Type*) (ell s c : ℕ) :=
  Matrix (a × PhysicalEncoderIndex ell s c) (a × PhysicalEncoderIndex ell s c) ℂ

section AuxiliaryCoordinates
variable {a : Type*} [Fintype a] [DecidableEq a]

/-- Binary coordinates for rotation, phase, and the original block ancillas. -/
def coherentAuxBits (m rA : ℕ) (ea : Bits rA ≃ a) :
    Bits (m + rA + 1) ≃ CoherentAux a (2 ^ m) :=
  (splitBits (m + rA)).trans
    (((Equiv.refl Bit).prodCongr
      ((OperationalModel.registerBasis m rA).trans
        ((bitsBinaryIndex m).prodCongr ea))).trans
      (Equiv.prodAssoc Bit (Fin (2 ^ m)) a).symm)

lemma coherentAuxBits_zero (m rA : ℕ) (ea : Bits rA ≃ a) (q : a)
    (he : ea (zeroBits rA) = q) :
    coherentAuxBits m rA ea (zeroBits (m + rA + 1)) =
      (((0, (0 : Fin (2 ^ m))), q) : CoherentAux a (2 ^ m)) := by
  change ((0, bitsBinaryIndex m (zeroBits m)), ea (zeroBits rA)) = _
  rw [bitsBinaryIndex_zero, he]

/-- Exact physical register permutation for the actual filter matrix. -/
def implementationIndex (ell s c m rA : ℕ) (ea : Bits rA ≃ a) :
    FilterSpace ell s c (m + rA + 1) ≃
      CoherentAux a (2 ^ m) × PhysicalDilation ell s ((Fintype.card (Bits c)) ^ 2) :=
  (Equiv.prodAssoc (Bits (m + rA + 1)) (Small ell s 0) (CatalystData c)).trans
    ((coherentAuxBits m rA ea).prodCongr
      (physicalDilationIndex ell s ((Fintype.card (Bits c)) ^ 2)))

/-- The concrete PE filter on the qubit registers used by the operational
one-clean-qubit theorem. -/
def physicalCoherentFilter (ell s c m rA : ℕ) (ea : Bits rA ≃ a)
    (UA : PhysicalEncoder a ell s c)
    (q : a) (lam : ℝ) : Matrix (FilterSpace ell s c (m + rA + 1))
      (FilterSpace ell s c (m + rA + 1)) ℂ :=
  (actualAuxFilter UA q (2 ^ m) lam).submatrix (implementationIndex ell s c m rA ea)
    (implementationIndex ell s c m rA ea)

lemma physicalCoherentFilter_unitary (ell s c m rA : ℕ) (ea : Bits rA ≃ a)
    (UA : PhysicalEncoder a ell s c)
    (hUA : UA ∈ Matrix.unitaryGroup (a × PhysicalEncoderIndex ell s c) ℂ)
    (q : a) (lam : ℝ) (hlam : 0 < lam) :
    OneCleanQubit.Unitary (physicalCoherentFilter ell s c m rA ea UA q lam) := by
  exact StatePreparation.unitary_reindex _ _
    (actualAuxFilter_unitary UA hUA q (2 ^ m) (by positivity) lam hlam)

/-- After zeroing exactly the physical auxiliary qubits, the implementation
block is the actual PE zero block proved correct in `WalkSelectedFilter`. -/
lemma physicalCoherentFilter_block (ell s c m rA : ℕ) (ea : Bits rA ≃ a)
    (UA : PhysicalEncoder a ell s c)
    (q : a) (he : ea (zeroBits rA) = q) (lam : ℝ) :
    implementedFilterBlock (physicalCoherentFilter ell s c m rA ea UA q lam) =
      actualFilterBlock UA q (2 ^ m) (by positivity) lam := by
  rw [← actualAuxFilter_zero_block UA q (2 ^ m) (by positivity) lam]
  ext i j
  simp [implementedFilterBlock, auxiliaryBlock, physicalCoherentFilter,
    implementationIndex, coherentAuxBits_zero m rA ea q he]

end AuxiliaryCoordinates

/-- The original four block ancillas, identified with actual physical bits. -/
def fourBlockAncillas : Bits 4 ≃ Fin 2 × Selector3 :=
  (splitBits 3).trans ((Equiv.refl Bit).prodCongr
    ((splitBits 2).trans ((Equiv.refl Bit).prodCongr
      ((splitBits 1).trans ((Equiv.refl Bit).prodCongr OperationalModel.oneBit)))))

lemma fourBlockAncillas_zero : fourBlockAncillas (zeroBits 4) = (0, zeroSelector3) := rfl

/-- The phase register size used by the actual source filter. -/
def sourcePhaseBits (ell s : ℕ) : ℕ :=
  phaseBits (Fintype.card (Bits ell)) (Fintype.card (WorkSpace s))

lemma bias_parameters_range (J K : ℝ) (hJ : 1 ≤ J) (hK : 1 ≤ K) :
    0 < biasLam J K ∧ biasLam J K / 3 ≤ 1 ∧
      0 < biasEps J K ∧ biasEps J K ≤ 1 := by
  have hj : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have hk : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hlam := biasLam_pos hj hk
  have hj2 : 1 ≤ J ^ 2 := one_le_pow₀ hJ
  have hk3 : 1 ≤ K ^ 3 := one_le_pow₀ hK
  have hprod : 1 ≤ J ^ 2 * K ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hk3 (sq_nonneg J)
    nlinarith
  have hl1 : biasLam J K ≤ 1 := by
    unfold biasLam
    apply (div_le_one₀ (by positivity : 0 < 100 * J ^ 2 * K ^ 3)).mpr
    nlinarith
  have heps : 0 < biasEps J K := by unfold biasEps; positivity
  refine ⟨hlam, by linarith, heps, ?_⟩
  unfold biasEps
  apply (div_le_one₀ (by positivity : 0 < 200 * K)).mpr
  linarith

/-- The actual encoder is the paper's coherent history LCU construction,
including the inactive clock labels and the four original block ancillas. -/
def sourceAEncoding (ell s c T : ℕ)
    (K : ℕ → Fin 8 → Matrix
      (Fin ((Fintype.card (WorkSpace s)) ^ 2) × CatalystData c)
      (Fin ((Fintype.card (WorkSpace s)) ^ 2) × CatalystData c) ℂ) :
    PhysicalEncoder HistoryEncoding.BlockAncilla ell s c :=
  HistoryEncoding.enumeratedAEncoding T (Fintype.card (Bits ell)) K

/-- Construct the full-filter implementation record from the actual source
LCU and coherent PE circuit. No whole-filter-error or implementation record
is assumed. The source-step eight-unitary witnesses are discharged by the
primitive source expansion; the eigenbasis is the disclosed external theorem. -/
def coherentSourceImplementation (ell s c T : ℕ)
    (C : ℕ → KrausChannel (WorkSpace s × Bits c))
    (hJ : T + 1 ≤ Fintype.card (Bits ell))
    (K : ℕ → Fin 8 → Matrix
      (Fin ((Fintype.card (WorkSpace s)) ^ 2) × CatalystData c)
      (Fin ((Fintype.card (WorkSpace s)) ^ 2) × CatalystData c) ℂ)
    (hK : ∀ t < T, ∀ j, K t j ∈ Matrix.unitaryGroup
      (Fin ((Fintype.card (WorkSpace s)) ^ 2) × CatalystData c) ℂ)
    (havg : ∀ t < T, (1 / 8 : ℂ) • ∑ j, K t j =
      (1 / 2 : ℂ) • SourceReduction.coordinates C t)
    (Dspec : UnitaryEigenbasis (blockWalk (sourceAEncoding ell s c T K) (0, zeroSelector3))) :
    GenericFullFilterImplementation ell s c (sourcePhaseBits ell s + 4 + 1) T C := by
  let J := Fintype.card (Bits ell)
  let W := Fintype.card (WorkSpace s)
  let lam := biasLam J W
  let eps := biasEps J W
  let m := sourcePhaseBits ell s
  let UA := sourceAEncoding ell s c T K
  have hj : (1 : ℝ) ≤ J := by exact_mod_cast (show 1 ≤ J by dsimp [J]; omega)
  have hw : (1 : ℝ) ≤ W := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨zeroWork s⟩)
  have hrange := bias_parameters_range J W hj hw
  have hUA : UA ∈ Matrix.unitaryGroup
      (HistoryEncoding.BlockAncilla × PhysicalEncoderIndex ell s c) ℂ :=
    HistoryEncoding.enumeratedAEncoding_unitary K hK
  have hA : UA.submatrix (fun i => ((0, zeroSelector3), i))
      (fun i => ((0, zeroSelector3), i)) =
      (1 / 3 : ℂ) • Matrix.reindex (Fintype.equivFin (PhysicalHistory ell s ((Fintype.card (Bits c)) ^ 2)))
        (Fintype.equivFin (PhysicalHistory ell s ((Fintype.card (Bits c)) ^ 2)))
          (sourceHistoryMatrix C T J) :=
    HistoryEncoding.enumeratedAEncoding_block K (SourceReduction.coordinates C) hJ havg
  have hM : 0 < 2 ^ m := by positivity
  have hprecision : 4096 / ((lam / 3) * eps ^ 2) ≤ (2 ^ m : ℕ) := by
    have h := (phaseLabels_spec
      (show 0 < J by exact_mod_cast (lt_of_lt_of_le zero_lt_one hj))
      (show 0 < W by exact_mod_cast (lt_of_lt_of_le zero_lt_one hw))).1
    exact h
  refine {
    matrix := physicalCoherentFilter ell s c m 4 fourBlockAncillas UA (0, zeroSelector3) lam
    unitary := physicalCoherentFilter_unitary ell s c m 4 fourBlockAncillas UA hUA _ lam hrange.1
    full_filter_error := ?_ }
  rw [physicalCoherentFilter_block _ _ _ _ _ _ _ _ fourBlockAncillas_zero]
  have herr := actualFilterBlock_error (sourceHistoryMatrix C T J) UA (0, zeroSelector3) hA
    Dspec (2 ^ m) hM lam eps hrange.1 hrange.2.1 hrange.2.2.1 hrange.2.2.2 hprecision
  exact herr.trans (by dsimp [eps]; linarith [hrange.2.2.1])

/-- Actual one-clean-qubit Born gap for the concrete source LCU/PE/filter/F
circuit, with no implementation certificate or final trace-error premise. -/
theorem source_probability_gap_actual_filter (ell s c T : ℕ)
    (C : ℕ → KrausChannel (WorkSpace s × Bits c))
    (hJ : T + 1 ≤ Fintype.card (Bits ell))
    (hrestore : ∀ ρ, IsDensity ρ →
      workPartialTrace ((KrausChannel.sequence C 0 T).act
        (Matrix.kronecker (Matrix.single (zeroWork s) (zeroWork s) 1) ρ)) = ρ)
    (K : ℕ → Fin 8 → Matrix
      (Fin ((Fintype.card (WorkSpace s)) ^ 2) × CatalystData c)
      (Fin ((Fintype.card (WorkSpace s)) ^ 2) × CatalystData c) ℂ)
    (hK : ∀ t < T, ∀ j, K t j ∈ Matrix.unitaryGroup
      (Fin ((Fintype.card (WorkSpace s)) ^ 2) × CatalystData c) ℂ)
    (havg : ∀ t < T, (1 / 8 : ℂ) • ∑ j, K t j =
      (1 / 2 : ℂ) • SourceReduction.coordinates C t)
    (Dspec : UnitaryEigenbasis (blockWalk (sourceAEncoding ell s c T K) (0, zeroSelector3))) :
    let I := coherentSourceImplementation ell s c T C hJ K hK havg Dspec
    0 < targetGap ell s (sourcePhaseBits ell s + 4 + 1) ∧
      OneCleanQubit.Unitary (OneCleanQubit.circuit (targetTraceUnitary I hJ)) ∧
      (0 ≤ targetProbability I hJ ∧ targetProbability I hJ ≤ 1) ∧
      (2 / 3 ≤ sourceProbability C T →
        1 / 2 + targetGap ell s (sourcePhaseBits ell s + 4 + 1) ≤ targetProbability I hJ) ∧
      (sourceProbability C T ≤ 1 / 3 →
        targetProbability I hJ ≤ 1 / 2 - targetGap ell s (sourcePhaseBits ell s + 4 + 1)) := by
  exact source_probability_gap_relative_to_full_filter C hJ hrestore
    (coherentSourceImplementation ell s c T C hJ K hK havg Dspec)

end Paper25.SelectedFilter
