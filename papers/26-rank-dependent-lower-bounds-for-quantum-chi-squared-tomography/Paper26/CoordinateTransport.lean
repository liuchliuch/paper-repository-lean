import Paper26.CollectiveMainLowerBounds

/-!
# Exact coordinate transport for finite quantum experiments

An equivalence of finite indices reindexes actual complex matrix entries.
This module proves preservation of positivity, trace, rank, generalized
inverses, both chi-squared losses (including their infinite branch), tensor
copies and the Born laws of dominated learners. No invariance assertion is
an external field.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.CoordinateTransport

open QuantumModel ContinuousPOVM CollectiveModel SupportCompression
open JordanLossMeasurability SymmetricSupport

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def matrix (e : ι ≃ κ) (A : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  A.submatrix e.symm e.symm

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem matrix_apply (e : ι ≃ κ) (A : Matrix ι ι ℂ) (i j : κ) :
    matrix e A i j = A (e.symm i) (e.symm j) := rfl

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem matrix_symm (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    matrix e.symm (matrix e A) = A := by ext i j; simp

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrix_mul (e : ι ≃ κ) (A B : Matrix ι ι ℂ) :
    matrix e (A * B) = matrix e A * matrix e B :=
  (Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm).symm

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem matrix_add (e : ι ≃ κ) (A B : Matrix ι ι ℂ) :
    matrix e (A + B) = matrix e A + matrix e B := rfl

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem matrix_sub (e : ι ≃ κ) (A B : Matrix ι ι ℂ) :
    matrix e (A - B) = matrix e A - matrix e B := rfl

omit [Fintype ι] [Fintype κ] in
@[simp] theorem matrix_one (e : ι ≃ κ) : matrix e (1 : Matrix ι ι ℂ) = 1 := by
  ext i j
  simp [Matrix.one_apply, e.symm.injective.eq_iff]

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem matrix_trace (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    Matrix.trace (matrix e A) = Matrix.trace A := e.symm.sum_comp (fun i => A i i)

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem matrix_rank (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    (matrix e A).rank = A.rank := Matrix.rank_reindex e e A

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrix_posSemidef (e : ι ≃ κ) {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    (matrix e A).PosSemidef := hA.submatrix e.symm

def density (e : ι ≃ κ) (ρ : Density ι) : Density κ where
  matrix := matrix e ρ.matrix
  positive := matrix_posSemidef e ρ.positive
  trace_one := (matrix_trace e ρ.matrix).trans ρ.trace_one

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem density_matrix (e : ι ≃ κ) (ρ : Density ι) :
    (density e ρ).matrix = matrix e ρ.matrix := rfl

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem density_symm (e : ι ≃ κ) (ρ : Density ι) :
    density e.symm (density e ρ) = ρ := by
  apply CommonCenter.density_eq_of_matrix
  exact matrix_symm e ρ.matrix

omit [DecidableEq ι] [DecidableEq κ] in
theorem measurable_density (e : ι ≃ κ) : Measurable (density e : Density ι → Density κ) := by
  have hm : Measurable (fun ρ : Density ι => ((density e ρ).matrix : κ → κ → ℂ)) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      (measurable_pi_apply (e.symm j)).comp
        ((measurable_pi_apply (e.symm i)).comp measurable_density_matrix)
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  exact hm ht

def densityEquiv (e : ι ≃ κ) : Density ι ≃ᵐ Density κ where
  toEquiv :=
    { toFun := density e
      invFun := density e.symm
      left_inv := density_symm e
      right_inv := density_symm e.symm }
  measurable_toFun := measurable_density e
  measurable_invFun := measurable_density e.symm

omit [DecidableEq ι] [DecidableEq κ] in
theorem hermitianInverse_matrix (e : ι ≃ κ) {A B : Matrix ι ι ℂ}
    (h : HermitianInverse A B) : HermitianInverse (matrix e A) (matrix e B) := by
  refine ⟨h.hermitian.submatrix e.symm, ?_, ?_, ?_⟩
  · rw [← matrix_mul, ← matrix_mul, h.commute]
  · rw [← matrix_mul, ← matrix_mul, h.outer]
  · rw [← matrix_mul, ← matrix_mul, h.inner]

theorem pinv_density (e : ι ≃ κ) (σ : Density ι) :
    pinv (density e σ) = matrix e (pinv σ) := by
  exact (pinv_properties (density e σ)).unique (density e σ).hermitian
    (hermitianInverse_matrix e (pinv_properties σ))

omit [DecidableEq ι] [DecidableEq κ] in
private theorem support_density_forward (e : ι ≃ κ) (ρ σ : Density ι)
    (h : SupportContained ρ σ) : SupportContained (density e ρ) (density e σ) := by
  intro v hv
  have hs : σ.matrix *ᵥ (v ∘ e) = 0 := by
    have hh := congrArg (fun w : κ → ℂ => w ∘ e) hv
    simpa [density, matrix, Matrix.submatrix_mulVec_equiv, Function.comp_def] using hh
  have hr := h (v ∘ e) hs
  change (ρ.matrix.submatrix e.symm e.symm) *ᵥ v = 0
  rw [Matrix.submatrix_mulVec_equiv]
  simpa only [Equiv.symm_symm] using congrArg (fun w : ι → ℂ => w ∘ e.symm) hr

omit [DecidableEq ι] [DecidableEq κ] in
theorem support_density (e : ι ≃ κ) (ρ σ : Density ι) :
    SupportContained (density e ρ) (density e σ) ↔ SupportContained ρ σ := by
  constructor
  · intro h
    simpa using support_density_forward e.symm (density e ρ) (density e σ) h
  · exact support_density_forward e ρ σ

theorem rightEnergy_density (e : ι ≃ κ) (ρ σ : Density ι) :
    rightEnergy (density e ρ) (density e σ) = rightEnergy ρ σ := by
  unfold rightEnergy
  rw [density_matrix, density_matrix, ← matrix_sub, pinv_density,
    ← matrix_mul, ← matrix_mul, matrix_trace]

/-- Full actual right-inverse loss, including support failure, is invariant. -/
theorem chiR_density (e : ι ≃ κ) (ρ σ : Density ι) :
    chiR (density e ρ) (density e σ) = chiR ρ σ := by
  by_cases h : SupportContained ρ σ
  · rw [chiR_eq_pinv_trace _ _ ((support_density e ρ σ).mpr h),
      chiR_eq_pinv_trace ρ σ h, rightEnergy_density]
  · rw [chiR_eq_top_of_not_supportContained _ _ (mt (support_density e ρ σ).mp h),
      chiR_eq_top_of_not_supportContained _ _ h]

omit [Fintype ι] [Fintype κ] in
theorem jordanMatrix_matrix (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    jordanMatrix (matrix e A) = matrix (Equiv.prodCongr e e) (jordanMatrix A) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [jordanMatrix, matrix, Matrix.kroneckerMap_apply, Matrix.one_apply,
    e.symm.injective.eq_iff, mul_add, mul_ite]

omit [DecidableEq ι] [DecidableEq κ] in
theorem quadratic_matrix (e : ι ≃ κ) (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    star (v ∘ e.symm) ⬝ᵥ (matrix e A *ᵥ (v ∘ e.symm)) = star v ⬝ᵥ (A *ᵥ v) := by
  have hv : (v ∘ e.symm) ∘ e = v := by ext i; simp
  change (star v) ∘ e.symm ⬝ᵥ (A.submatrix e.symm e.symm *ᵥ (v ∘ e.symm)) = _
  rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, hv]
  exact comp_equiv_dotProduct_comp_equiv _ _ e.symm

section Nonempty
variable [Nonempty ι] [Nonempty κ]

theorem pseudoJordan_density (e : ι ≃ κ) (σ : Density ι) :
    pseudoJordan (density e σ) = matrix (Equiv.prodCongr e e) (pseudoJordan σ) := by
  apply (pseudoJordan_properties (density e σ)).unique
    (jordanMatrix_posSemidef (density e σ)).isHermitian
  rw [density_matrix, jordanMatrix_matrix]
  exact hermitianInverse_matrix (Equiv.prodCongr e e) (pseudoJordan_properties σ)

theorem buresEnergy_density (e : ι ≃ κ) (ρ σ : Density ι) :
    buresEnergy (density e ρ) (density e σ) = buresEnergy ρ σ := by
  unfold buresEnergy
  rw [pseudoJordan_density]
  change (star ((Matrix.vec (ρ.matrix - σ.matrix)) ∘ (Equiv.prodCongr e e).symm) ⬝ᵥ
    (matrix (Equiv.prodCongr e e) (pseudoJordan σ) *ᵥ
      ((Matrix.vec (ρ.matrix - σ.matrix)) ∘ (Equiv.prodCongr e e).symm))).re = _
  rw [quadratic_matrix]

end Nonempty

/-- Full actual Bures chi-squared loss, including support failure, is invariant. -/
theorem chiB_density (e : ι ≃ κ) (ρ σ : Density ι) :
    chiB (density e ρ) (density e σ) = chiB ρ σ := by
  haveI : Nonempty ι := by
    by_contra h
    haveI : IsEmpty ι := not_nonempty_iff.mp h
    simpa [Matrix.trace] using ρ.trace_one
  haveI : Nonempty κ := Nonempty.map e inferInstance
  by_cases h : SupportContained ρ σ
  · rw [chiB_eq_jordan_energy _ _ ((support_density e ρ σ).mpr h),
      chiB_eq_jordan_energy ρ σ h, buresEnergy_density]
  · rw [chiB_eq_top_of_not_supportContained _ _ (mt (support_density e ρ σ).mp h),
      chiB_eq_top_of_not_supportContained _ _ h]

/-- Coordinate relabeling of every actual tensor-copy basis vector. -/
def copyEquiv (e : ι ≃ κ) (n : ℕ) : (Fin n → ι) ≃ (Fin n → κ) :=
  Equiv.piCongrRight (fun _ => e)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem tensor_matrix (e : ι ≃ κ) (A : Matrix ι ι ℂ) (n : ℕ) :
    TensorCopies.matrix (matrix e A) n = matrix (copyEquiv e n) (TensorCopies.matrix A n) := rfl

theorem tensor_density (e : ι ≃ κ) (ρ : Density ι) (n : ℕ) :
    TensorCopies.density (density e ρ) n = density (copyEquiv e n) (TensorCopies.density ρ n) := by
  apply CommonCenter.density_eq_of_matrix
  exact tensor_matrix e ρ.matrix n

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A transported dominated POVM has the same reference measure and
reindexed effects; all positivity and normalization conditions are proved. -/
def povm (e : ι ≃ κ) (M : DominatedPOVM ι Ω) : DominatedPOVM κ Ω where
  reference := M.reference
  reference_finite := M.reference_finite
  effect y := matrix e (M.effect y)
  entry_measurable i j := M.entry_measurable (e.symm i) (e.symm j)
  positive_ae := M.positive_ae.mono (fun _ hy => matrix_posSemidef e hy)
  entry_integrable i j := M.entry_integrable (e.symm i) (e.symm j)
  total i j := by
    change (∫ y, M.effect y (e.symm i) (e.symm j) ∂M.reference) = _
    rw [M.total]
    exact congrArg (fun B : Matrix κ κ ℂ => B i j) (matrix_one e)

theorem povm_born (e : ι ≃ κ) (M : DominatedPOVM ι Ω) (ρ : Density ι) (y : Ω) :
    (povm e M).born (density e ρ) y = M.born ρ y := by
  change (Matrix.trace (matrix e ρ.matrix * matrix e (M.effect y))).re = _
  rw [← matrix_mul, matrix_trace]
  rfl

/-- Actual `n`-copy learner, with its estimator transported entrywise. -/
def learner {n : ℕ} (e : ι ≃ κ) (A : Learner ι Ω n) : Learner κ Ω n where
  measurement := povm (copyEquiv e n) A.measurement
  estimator :=
    { estimate := fun y => density e (A.estimator.estimate y)
      measurable_estimate := (measurable_density e).comp A.estimator.measurable_estimate }

theorem learner_born {n : ℕ} (e : ι ≃ κ) (A : Learner ι Ω n) (ρ : Density ι) (y : Ω) :
    (learner e A).born (density e ρ) y = A.born ρ y := by
  change (povm (copyEquiv e n) A.measurement).born (TensorCopies.density (density e ρ) n) y = _
  rw [tensor_density, povm_born]
  rfl

theorem learner_outcomeMeasure {n : ℕ} (e : ι ≃ κ) (A : Learner ι Ω n) (ρ : Density ι) :
    (learner e A).outcomeMeasure (density e ρ) = A.outcomeMeasure ρ := by
  change A.measurement.reference.withDensity
    (fun y => ENNReal.ofReal ((learner e A).born (density e ρ) y)) =
      A.measurement.reference.withDensity (fun y => ENNReal.ofReal (A.born ρ y))
  simp only [learner_born]

theorem learner_outputMeasure {n : ℕ} (e : ι ≃ κ) (A : Learner ι Ω n) (ρ : Density ι) :
    (learner e A).outputMeasure (density e ρ) = (A.outputMeasure ρ).map (density e) := by
  unfold Learner.outputMeasure
  rw [learner_outcomeMeasure, Measure.map_map (measurable_density e) A.estimator.measurable_estimate]
  rfl

section Loss
variable {n : ℕ} (e : ι ≃ κ) (A : Learner ι Ω n)
variable (Lι : Density ι → Density ι → ℝ≥0∞) (Lκ : Density κ → Density κ → ℝ≥0∞)
variable (hL : ∀ ρ σ, Lκ (density e ρ) (density e σ) = Lι ρ σ)
include hL

theorem learner_successSet (ρ : Density ι) (ε : ℝ≥0∞) :
    (learner e A).successSet Lκ (density e ρ) ε = A.successSet Lι ρ ε := by
  ext y
  change Lκ (density e ρ) (density e (A.estimator.estimate y)) ≤ ε ↔
    Lι ρ (A.estimator.estimate y) ≤ ε
  rw [hL]

theorem learner_successProbability (ρ : Density ι) (ε : ℝ≥0∞) :
    (learner e A).successProbability Lκ (density e ρ) ε = A.successProbability Lι ρ ε := by
  unfold Learner.successProbability
  rw [learner_successSet e A Lι Lκ hL, learner_outcomeMeasure]

/-- Coordinate transport preserves the actual measurable-event learning
promise, rather than an abstract scalar surrogate. -/
theorem learner_learnsRank_iff (r : ℕ) (ε q : ℝ≥0∞) :
    (learner e A).LearnsRank Lκ r ε q ↔ A.LearnsRank Lι r ε q := by
  constructor
  · intro h ρ hρ
    have hp := h (density e ρ) (by simpa using hρ)
    simpa only [learner_successSet e A Lι Lκ hL, learner_successProbability e A Lι Lκ hL] using hp
  · intro h ρ hρ
    obtain ⟨hm, hp⟩ := h (density e.symm ρ) (by simpa using hρ)
    have hs := learner_successSet e A Lι Lκ hL (density e.symm ρ) ε
    have hprob := learner_successProbability e A Lι Lκ hL (density e.symm ρ) ε
    have hback : density e (density e.symm ρ) = ρ := density_symm e.symm ρ
    rw [hback] at hs hprob
    exact ⟨hs.symm ▸ hm, hprob.symm ▸ hp⟩

end Loss

theorem buresSuccess_iff {n : ℕ} (e : ι ≃ κ) (A : Learner ι Ω n) (r : ℕ) (ε : ℝ≥0∞) :
    (learner e A).BuresSuccess r ε ↔ A.BuresSuccess r ε :=
  learner_learnsRank_iff e A chiB chiB (chiB_density e) r ε _

theorem rightSuccess_iff {n : ℕ} (e : ι ≃ κ) (A : Learner ι Ω n) (r : ℕ) (ε : ℝ≥0∞) :
    (learner e A).RightSuccess r ε ↔ A.RightSuccess r ε :=
  learner_learnsRank_iff e A chiR chiR (chiR_density e) r ε _

/-- A concrete equivalence to the split ambient used in the all-rank proof. -/
def ambientEquiv {d r : ℕ} (hcard : Fintype.card ι = d) :
    ι ≃ CollectiveMainLowerBounds.AmbientIndex d r :=
  Fintype.equivOfCardEq (hcard.trans (CollectiveMainLowerBounds.ambient_card d r).symm)

omit [Fintype κ] [DecidableEq κ] in
/-- The collective Bures lower bound on every finite ambient index of
cardinality `d`, with actual learner, input ranks and losses transported. -/
theorem bures_collective {d r n : ℕ} (hcard : Fintype.card ι = d)
    (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (V : CollectiveMainLowerBounds.RawVolumeInputs
      (RankReduction.reducedRank d r) (d - RankReduction.reducedRank d r))
    (An : 2 ≤ RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r) →
      CollectiveMainLowerBounds.AnalysisInputs
        (2 * RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r)))
    (P : SymmetricProjectorInput (CollectiveMainLowerBounds.AmbientIndex d r) n)
    (A : Learner ι Ω n) (G : GraphFisherBudget.GraphTangentInput)
    {C ε : ℝ} (hC : 0 < C) (N : GraphPrior.NZSmoothLocalPriorInput C)
    (hε : 0 < ε) (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : A.BuresSuccess r (ENNReal.ofReal ε)) :
    CollectiveMainLowerBounds.sampleConstant C *
      (Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε) ≤ (n : ℝ) := by
  let e : ι ≃ CollectiveMainLowerBounds.AmbientIndex d r := ambientEquiv hcard
  exact CollectiveMainLowerBounds.bures_collective hd hr hrd V An P (learner e A)
    G hC N hε hsmall ((buresSuccess_iff e A r _).mpr hA)

omit [Fintype κ] [DecidableEq κ] in
/-- The collective right-inverse lower bound on every finite ambient index. -/
theorem right_collective {d r n : ℕ} (hcard : Fintype.card ι = d)
    (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (V : CollectiveMainLowerBounds.RawVolumeInputs
      (RankReduction.reducedRank d r) (d - RankReduction.reducedRank d r))
    (An : 2 ≤ RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r) →
      CollectiveMainLowerBounds.AnalysisInputs
        (2 * RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r)))
    (P : SymmetricProjectorInput (CollectiveMainLowerBounds.AmbientIndex d r) n)
    (A : Learner ι Ω n) (G : GraphFisherBudget.GraphTangentInput)
    {C ε : ℝ} (hC : 0 < C) (N : GraphPrior.NZSmoothLocalPriorInput C)
    (hε : 0 < ε) (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : A.RightSuccess r (ENNReal.ofReal ε)) :
    CollectiveMainLowerBounds.sampleConstant C * ((d : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  let e : ι ≃ CollectiveMainLowerBounds.AmbientIndex d r := ambientEquiv hcard
  exact CollectiveMainLowerBounds.right_collective hd hr hrd V An P (learner e A)
    G hC N hε hsmall ((rightSuccess_iff e A r _).mpr hA)

end Paper26.CoordinateTransport
