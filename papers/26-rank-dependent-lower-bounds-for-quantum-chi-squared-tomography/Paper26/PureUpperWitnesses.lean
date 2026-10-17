import Paper26.PureUpperBounds
import Paper26.UpperBoundWitnesses

/-!
# Integer-copy witnesses for the pure-state upper bounds

The existing covariant learner is used at a specified ceiling of the proved
copy threshold.  The experiment is fixed before all rank-at-most-one inputs,
and is transported to the original operator-POVM model.  Only the original
Haar tensor moment and symmetric-projector inputs are used.
-/
noncomputable section
open scoped ENNReal ComplexOrder
open MeasureTheory

namespace Paper26.PureUpperWitnesses

open QuantumModel HaarFrames PureCovariant CollectiveModel ContinuousPOVM

/-- The actual natural number of copies for the pure Bures clause. -/
def buresCopies (d : ℕ) (ε : ℝ) : ℕ :=
  ⌈48 * ((d - 1 : ℕ) : ℝ) * Real.sqrt ((d - 1 : ℕ) : ℝ) / ε⌉₊

/-- The actual natural number of copies for the pure right-inverse clause. -/
def rightCopies (d : ℕ) (ε : ℝ) : ℕ :=
  ⌈24 * ((d - 1 : ℕ) : ℝ) ^ 2 / ε ^ 2⌉₊

theorem buresCopies_le {d : ℕ} (hd : 2 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (buresCopies d ε : ℝ) ≤ 49 * (d : ℝ) * Real.sqrt d / ε := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hm : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
  have hs : Real.sqrt ((d - 1 : ℕ) : ℝ) ≤ Real.sqrt d := Real.sqrt_le_sqrt hm
  have hbase : 48 * ((d - 1 : ℕ) : ℝ) * Real.sqrt ((d - 1 : ℕ) : ℝ) / ε ≤
      48 * (d : ℝ) * Real.sqrt d / ε := by gcongr
  have hone : 1 ≤ (d : ℝ) * Real.sqrt d / ε := by
    apply (le_div_iff₀ hε).mpr
    simpa only [one_mul] using hε1.trans
      (one_le_mul_of_one_le_of_one_le hd1 (Real.one_le_sqrt.mpr hd1))
  calc
    _ ≤ 48 * ((d - 1 : ℕ) : ℝ) * Real.sqrt ((d - 1 : ℕ) : ℝ) / ε + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    _ ≤ 48 * (d : ℝ) * Real.sqrt d / ε + 1 := add_le_add_right hbase 1
    _ ≤ 48 * (d : ℝ) * Real.sqrt d / ε + (d : ℝ) * Real.sqrt d / ε :=
      add_le_add_left hone _
    _ = _ := by ring

theorem rightCopies_le {d : ℕ} (hd : 2 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (rightCopies d ε : ℝ) ≤ 25 * (d : ℝ) ^ 2 / ε ^ 2 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hm : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
  have hbase : 24 * ((d - 1 : ℕ) : ℝ) ^ 2 / ε ^ 2 ≤
      24 * (d : ℝ) ^ 2 / ε ^ 2 := by gcongr
  have hone : 1 ≤ (d : ℝ) ^ 2 / ε ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    nlinarith
  calc
    _ ≤ 24 * ((d - 1 : ℕ) : ℝ) ^ 2 / ε ^ 2 + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    _ ≤ 24 * (d : ℝ) ^ 2 / ε ^ 2 + 1 := add_le_add_right hbase 1
    _ ≤ 24 * (d : ℝ) ^ 2 / ε ^ 2 + (d : ℝ) ^ 2 / ε ^ 2 :=
      add_le_add_left hone _
    _ = _ := by ring

variable {d : ℕ} (hd : 2 ≤ d)
  (μ : Measure (Frame (Fin d) (Fin 1))) [IsProbabilityMeasure μ]
  (H : HaarTensorMomentInput μ)
  (P : ∀ n, SymmetricSupport.SymmetricProjectorInput (Fin d) n)

include hd μ H P

/-- One concrete ceiling-copy learner, chosen uniformly before all pure inputs. -/
theorem exists_bures_learner {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A : Learner (Fin d) (Frame (Fin d) (Fin 1)) (buresCopies d ε),
      A.BuresSuccess 1 (ENNReal.ofReal ε) := by
  letI : NeZero d := ⟨by omega⟩
  have hm : 0 < d - 1 := by omega
  have hcard : Fintype.card (Fin d) = (d - 1) + 1 := by simp; omega
  let A := PureUpperBounds.learner μ H (P (buresCopies d ε)) (d - 1) hm hcard
    (ε / 16) (by positivity) (by linarith)
  refine ⟨A, ?_⟩
  exact PureUpperBounds.bures_learns μ H (P (buresCopies d ε))
    (P (buresCopies d ε + 1)) (d - 1) hm hcard ε hε hε1 (Nat.le_ceil _)

/-- One concrete ceiling-copy right-inverse learner with the same uniform promise. -/
theorem exists_right_learner {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A : Learner (Fin d) (Frame (Fin d) (Fin 1)) (rightCopies d ε),
      A.RightSuccess 1 (ENNReal.ofReal ε) := by
  letI : NeZero d := ⟨by omega⟩
  have hm : 0 < d - 1 := by omega
  have hcard : Fintype.card (Fin d) = (d - 1) + 1 := by simp; omega
  let A := PureUpperBounds.learner μ H (P (rightCopies d ε)) (d - 1) hm hcard
    (ε / 4) (by positivity) (by linarith)
  refine ⟨A, ?_⟩
  exact PureUpperBounds.right_learns μ H (P (rightCopies d ε))
    (P (rightCopies d ε + 1)) (d - 1) hm hcard ε hε hε1 (Nat.le_ceil _)

/-- The source pure Bures upper clause as an actual raw collective witness. -/
theorem bures_collective {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    UpperBoundWitnesses.Collective (ι := Fin d) chiB 1 (ENNReal.ofReal ε)
      ((2 : ℝ≥0∞) / 3) (49 * (d : ℝ) * Real.sqrt d / ε) := by
  obtain ⟨A, hA⟩ := exists_bures_learner hd μ H P hε hε1
  exact UpperBoundWitnesses.collective_of_learner A chiB 1 _ _
    (buresCopies_le hd hε hε1) hA

/-- The source pure right-inverse clause as an actual raw collective witness. -/
theorem right_collective {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    UpperBoundWitnesses.Collective (ι := Fin d) chiR 1 (ENNReal.ofReal ε)
      ((2 : ℝ≥0∞) / 3) (25 * (d : ℝ) ^ 2 / ε ^ 2) := by
  obtain ⟨A, hA⟩ := exists_right_learner hd μ H P hε hε1
  exact UpperBoundWitnesses.collective_of_learner A chiR 1 _ _
    (rightCopies_le hd hε hε1) hA

theorem Ncoll_bures_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    CopyComplexity.Ncoll (ι := Fin d) chiB 1 (ENNReal.ofReal ε) ≤
      ENNReal.ofReal (49 * (d : ℝ) * Real.sqrt d / ε) :=
  UpperBoundWitnesses.Ncoll_le (bures_collective hd μ H P hε hε1)

theorem Ncoll_right_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    CopyComplexity.Ncoll (ι := Fin d) chiR 1 (ENNReal.ofReal ε) ≤
      ENNReal.ofReal (25 * (d : ℝ) ^ 2 / ε ^ 2) :=
  UpperBoundWitnesses.Ncoll_le (right_collective hd μ H P hε hε1)

section DimensionOne

omit hd μ H P

/-- The actual density type in dimension one has exactly one element. -/
theorem density_one_eq (ρ σ : Density (Fin 1)) : ρ = σ := by
  apply CommonCenter.density_eq_of_matrix
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  have hρ : ρ.matrix 0 0 = 1 := by simpa [Matrix.trace] using ρ.trace_one
  have hσ : σ.matrix 0 0 = 1 := by simpa [Matrix.trace] using σ.trace_one
  exact hρ.trans hσ.symm

/-- No quantum copy is consumed: the empty tensor has the identity effect,
and the sole possible density is returned at the single observed outcome. -/
def dimensionOneLearner : Learner (Fin 1) PUnit 0 where
  measurement :=
    { reference := Measure.dirac PUnit.unit
      reference_finite := inferInstance
      effect _ := 1
      entry_measurable _ _ := measurable_const
      positive_ae := ae_of_all _ fun _ => Matrix.PosSemidef.one
      entry_integrable _ _ := integrable_const _
      total _ _ := by simp }
  estimator := ⟨fun _ => AdaptiveCollectiveEmbedding.uniformState (Fin 1), measurable_const⟩

private theorem dimensionOne_learns
    (loss : Density (Fin 1) → Density (Fin 1) → ℝ≥0∞)
    (hself : ∀ ρ, loss ρ ρ = 0) (ε : ℝ≥0∞) :
    dimensionOneLearner.LearnsRank loss 1 ε ((2 : ℝ≥0∞) / 3) := by
  intro ρ _
  have heq := density_one_eq ρ (AdaptiveCollectiveEmbedding.uniformState (Fin 1))
  have hs : dimensionOneLearner.successSet loss ρ ε = Set.univ := by
    ext y
    simp only [Learner.successSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    change loss ρ (AdaptiveCollectiveEmbedding.uniformState (Fin 1)) ≤ ε
    rw [← heq, hself]
    exact zero_le _
  constructor
  · rw [hs]
    exact MeasurableSet.univ
  · change (2 : ℝ≥0∞) / 3 ≤ dimensionOneLearner.outcomeMeasure ρ
      (dimensionOneLearner.successSet loss ρ ε)
    rw [hs, measure_univ]
    exact (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by norm_num)

theorem bures_collective_one (ε : ℝ≥0∞) :
    UpperBoundWitnesses.Collective (ι := Fin 1) chiB 1 ε ((2 : ℝ≥0∞) / 3) 0 :=
  UpperBoundWitnesses.collective_of_learner dimensionOneLearner chiB 1 ε _
    (by norm_num) (dimensionOne_learns chiB chiB_self ε)

theorem right_collective_one (ε : ℝ≥0∞) :
    UpperBoundWitnesses.Collective (ι := Fin 1) chiR 1 ε ((2 : ℝ≥0∞) / 3) 0 :=
  UpperBoundWitnesses.collective_of_learner dimensionOneLearner chiR 1 ε _
    (by norm_num) (dimensionOne_learns chiR chiR_self ε)

theorem Ncoll_bures_one (ε : ℝ≥0∞) :
    CopyComplexity.Ncoll (ι := Fin 1) chiB 1 ε = 0 := by
  apply le_antisymm _ (zero_le _)
  simpa only [ENNReal.ofReal_zero] using UpperBoundWitnesses.Ncoll_le (bures_collective_one ε)

theorem Ncoll_right_one (ε : ℝ≥0∞) :
    CopyComplexity.Ncoll (ι := Fin 1) chiR 1 ε = 0 := by
  apply le_antisymm _ (zero_le _)
  simpa only [ENNReal.ofReal_zero] using UpperBoundWitnesses.Ncoll_le (right_collective_one ε)

end DimensionOne

end Paper26.PureUpperWitnesses
