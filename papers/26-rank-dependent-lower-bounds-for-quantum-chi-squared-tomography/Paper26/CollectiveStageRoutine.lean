import Paper26.ContinuousSubmatrixLearning
import Paper26.CoordinateTransport
import Paper26.AdaptiveModel
import Paper26.MatrixAmplification
import Paper26.CollectivePadding

/-!
# Physical collective block routines in a measurable moving basis

A stage acts on a fixed N-copy macro input. Its active set and ambient unitary
are classical controls. Coordinate changes and unitary conjugation transport
actual effects and preserve Born laws; no conditional risk is a model field.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
namespace Paper26.CollectiveStageRoutine
open MeasureTheory QuantumModel ContinuousPOVM PositiveLossBridge
open ContinuousSubmatrixLearning

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

section UnitaryTransport
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

lemma conjugate_entry_measurable (F : Ω → Matrix ι ι ℂ)
    (hF : ∀ i j, Measurable (fun y => F y i j)) (i j : ι) :
    Measurable (fun z : Matrix.unitaryGroup ι ℂ × Ω =>
      Normalization.conjugate (z.1 : Matrix ι ι ℂ) (F z.2) i j) := by
  change Measurable (fun z : Matrix.unitaryGroup ι ℂ × Ω =>
    ∑ b, (∑ a, (z.1 : Matrix ι ι ℂ) i a * F z.2 a b) * star ((z.1 : Matrix ι ι ℂ) j b))
  have hU : Measurable (fun z : Matrix.unitaryGroup ι ℂ × Ω =>
      (z.1 : Matrix ι ι ℂ)) := measurable_subtype_coe.comp measurable_fst
  apply Finset.measurable_sum Finset.univ
  intro b _
  apply Measurable.mul
  · apply Finset.measurable_sum Finset.univ
    intro a _
    exact ((measurable_pi_apply a).comp ((measurable_pi_apply i).comp hU)).mul
      ((hF a b).comp measurable_snd)
  · exact Complex.continuous_conj.measurable.comp
      ((measurable_pi_apply b).comp ((measurable_pi_apply j).comp hU))

lemma conjugate_entry_integrable (U : Matrix ι ι ℂ) (F : Ω → Matrix ι ι ℂ)
    (ν : Measure Ω) (hF : ∀ i j, Integrable (fun y => F y i j) ν) (i j : ι) :
    Integrable (fun y => Normalization.conjugate U (F y) i j) ν := by
  change Integrable (fun y => ∑ b, (∑ a, U i a * F y a b) * star (U j b)) ν
  apply integrable_finset_sum Finset.univ
  intro b _
  exact (integrable_finset_sum Finset.univ (fun a _ => (hF a b).const_mul _)).mul_const _

lemma conjugate_entry_integral (U : Matrix ι ι ℂ) (F : Ω → Matrix ι ι ℂ)
    (ν : Measure Ω) (hF : ∀ i j, Integrable (fun y => F y i j) ν) (i j : ι) :
    (∫ y, Normalization.conjugate U (F y) i j ∂ν) =
      Normalization.conjugate U (fun a b => ∫ y, F y a b ∂ν) i j := by
  simp only [Normalization.conjugate, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [integral_finset_sum Finset.univ (fun b _ =>
    (integrable_finset_sum Finset.univ (fun a _ => (hF a b).const_mul _)).mul_const _)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_mul_const, integral_finset_sum Finset.univ (fun a _ => (hF a b).const_mul _)]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_const_mul]

/-- Active physical conjugation of a POVM, with unchanged finite reference. -/
def rotateMeasurement (U : Matrix.unitaryGroup ι ℂ) (M : DominatedPOVM ι Ω) :
    DominatedPOVM ι Ω where
  reference := M.reference
  reference_finite := M.reference_finite
  effect y := Normalization.conjugate (U : Matrix ι ι ℂ) (M.effect y)
  entry_measurable i j := by
    change Measurable (fun y : Ω => ∑ b,
      (∑ a, (U : Matrix ι ι ℂ) i a * M.effect y a b) * star ((U : Matrix ι ι ℂ) j b))
    exact Finset.measurable_sum Finset.univ fun b _ =>
      (Finset.measurable_sum Finset.univ fun a _ =>
        (M.entry_measurable a b).const_mul _).mul_const _
  positive_ae := M.positive_ae.mono fun _ hy => hy.mul_mul_conjTranspose_same _
  entry_integrable := conjugate_entry_integrable _ _ _ M.entry_integrable
  total i j := by
    rw [conjugate_entry_integral _ _ _ M.entry_integrable]
    have ht : (fun a b => ∫ y, M.effect y a b ∂M.reference) = (1 : Matrix ι ι ℂ) := by ext a b; exact M.total a b
    rw [ht]
    simp only [Normalization.conjugate, Matrix.mul_one, unitary_right U]

lemma rotate_born (U : Matrix.unitaryGroup ι ℂ) (M : DominatedPOVM ι Ω)
    (ρ : Density ι) (y : Ω) :
    (rotateMeasurement U M).born ρ y = M.born (conjugateDensity (star U) ρ) y := by
  change (Matrix.trace (ρ.matrix * Normalization.conjugate (U : Matrix ι ι ℂ) (M.effect y))).re = _
  have he : Matrix.trace (ρ.matrix * Normalization.conjugate (U : Matrix ι ι ℂ) (M.effect y)) =
      Matrix.trace ((conjugateDensity (star U) ρ).matrix * M.effect y) := by
    simp only [conjugateDensity_matrix, unitary.coe_star, Matrix.star_eq_conjTranspose,
      Normalization.conjugate, Matrix.conjTranspose_conjTranspose]
    calc
      _ = Matrix.trace ((U : Matrix ι ι ℂ)ᴴ * (ρ.matrix * ((U : Matrix ι ι ℂ) * M.effect y))) := by
        rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = _ := by simp only [Matrix.mul_assoc]
  exact congrArg Complex.re he

lemma rotate_outcomeMeasure (U : Matrix.unitaryGroup ι ℂ) (M : DominatedPOVM ι Ω)
    (ρ : Density ι) :
    (rotateMeasurement U M).outcomeMeasure ρ = M.outcomeMeasure (conjugateDensity (star U) ρ) := by
  unfold DominatedPOVM.outcomeMeasure
  congr 1
  funext y
  rw [rotate_born]

end UnitaryTransport

section Copies
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def copyUnitary (U : Matrix.unitaryGroup ι ℂ) (N : ℕ) : Matrix.unitaryGroup (Fin N → ι) ℂ := by
  refine ⟨TensorCopies.matrix (U : Matrix ι ι ℂ) N, Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  change TensorCopies.matrix (U : Matrix ι ι ℂ) N *
    (TensorCopies.matrix (U : Matrix ι ι ℂ) N)ᴴ = 1
  rw [← TensorCopies.matrix_conjTranspose, ← TensorCopies.matrix_mul, unitary_right U]
  exact TensorSLD.tensor_one N

lemma tensor_conjugateDensity (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) (N : ℕ) :
    TensorCopies.density (conjugateDensity U ρ) N =
      conjugateDensity (copyUnitary U N) (TensorCopies.density ρ N) := by
  apply CommonCenter.density_eq_of_matrix
  change TensorCopies.matrix ((U : Matrix ι ι ℂ) * ρ.matrix * (U : Matrix ι ι ℂ)ᴴ) N = _
  rw [TensorCopies.matrix_mul, TensorCopies.matrix_mul, TensorCopies.matrix_conjTranspose]
  rfl

lemma copyUnitary_star (U : Matrix.unitaryGroup ι ℂ) (N : ℕ) :
    copyUnitary (star U) N = star (copyUnitary U N) := by
  apply Subtype.ext
  change TensorCopies.matrix ((U : Matrix ι ι ℂ)ᴴ) N =
    (TensorCopies.matrix (U : Matrix ι ι ℂ) N)ᴴ
  exact TensorCopies.matrix_conjTranspose _ _

lemma copyUnitary_entry_measurable (N : ℕ) (x y : Fin N → ι) :
    Measurable (fun U : Matrix.unitaryGroup ι ℂ => (copyUnitary U N : Matrix _ _ ℂ) x y) := by
  change Measurable (fun U : Matrix.unitaryGroup ι ℂ => ∏ k, (U : Matrix ι ι ℂ) (x k) (y k))
  apply Finset.measurable_prod Finset.univ
  intro k _
  exact (measurable_pi_apply (y k)).comp ((measurable_pi_apply (x k)).comp measurable_subtype_coe)

lemma measurable_copyUnitary (N : ℕ) : Measurable (fun U : Matrix.unitaryGroup ι ℂ => copyUnitary U N) := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro x
  apply measurable_pi_lambda
  intro y
  exact copyUnitary_entry_measurable N x y

end Copies

section SplitTransport
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {N : ℕ}

abbrev Active (S : Finset ι) := {i // i ∈ S}
abbrev Inactive (S : Finset ι) := {i // i ∉ S}
def splitEquiv (S : Finset ι) : (Active S ⊕ Inactive S) ≃ ι :=
  Equiv.sumCompl (fun i => i ∈ S)

/-- The actual input density expressed in the selected basis and split block
coordinates. No input block-diagonal hypothesis is made. -/
def splitState (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) :
    Density (Active S ⊕ Inactive S) :=
  CoordinateTransport.density (splitEquiv S).symm (conjugateDensity (star U) ρ)

/-- The true compressed active block, in the current ambient unitary basis. -/
def compressedBlock (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) :
    Matrix (Active S) (Active S) ℂ :=
  (Normalization.coordinates (U : Matrix ι ι ℂ) ρ.matrix).submatrix Subtype.val Subtype.val

lemma splitState_headBlock (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) :
    CollectiveFiltering.headBlock (splitState S U ρ).matrix = compressedBlock S U ρ := by
  ext i j
  simp only [CollectiveFiltering.headBlock, splitState, CoordinateTransport.density_matrix,
    CoordinateTransport.matrix_apply, Equiv.symm_symm, splitEquiv,
    Equiv.sumCompl_apply_inl, conjugateDensity_matrix, unitary.coe_star,
    Matrix.star_eq_conjTranspose, Normalization.conjugate, Normalization.coordinates,
    Matrix.conjTranspose_conjTranspose, compressedBlock, Matrix.submatrix_apply]

/-- Physical canonical block measurement transported to the ambient Ncopy
Hilbert space, with the exact original finite reference. -/
def ambientMeasurement (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ)
    (M : DominatedPOVM (Fin N → (Active S ⊕ Inactive S)) Ω) :
    DominatedPOVM (Fin N → ι) Ω :=
  rotateMeasurement (copyUnitary U N)
    (CoordinateTransport.povm (CoordinateTransport.copyEquiv (splitEquiv S) N) M)

lemma ambient_born (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ)
    (M : DominatedPOVM (Fin N → (Active S ⊕ Inactive S)) Ω)
    (ρ : Density ι) (y : Ω) :
    (ambientMeasurement S U M).born (TensorCopies.density ρ N) y =
      M.born (TensorCopies.density (splitState S U ρ) N) y := by
  unfold ambientMeasurement
  rw [rotate_born, ← copyUnitary_star, ← tensor_conjugateDensity]
  have he : TensorCopies.density (conjugateDensity (star U) ρ) N =
      CoordinateTransport.density (CoordinateTransport.copyEquiv (splitEquiv S) N)
        (TensorCopies.density (splitState S U ρ) N) := by
    rw [← CoordinateTransport.tensor_density]
    exact congrArg (fun σ => TensorCopies.density σ N)
      (CoordinateTransport.density_symm (splitEquiv S).symm (conjugateDensity (star U) ρ)).symm
  rw [he, CoordinateTransport.povm_born]

lemma ambient_outcomeMeasure (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ)
    (M : DominatedPOVM (Fin N → (Active S ⊕ Inactive S)) Ω) (ρ : Density ι) :
    (ambientMeasurement S U M).outcomeMeasure (TensorCopies.density ρ N) =
      M.outcomeMeasure (TensorCopies.density (splitState S U ρ) N) := by
  unfold DominatedPOVM.outcomeMeasure
  congr 1
  funext y
  rw [ambient_born]

lemma ambient_entry_joint_measurable (S : Finset ι)
    (M : DominatedPOVM (Fin N → (Active S ⊕ Inactive S)) Ω) (i j : Fin N → ι) :
    Measurable (fun z : Matrix.unitaryGroup ι ℂ × Ω => (ambientMeasurement S z.1 M).effect z.2 i j) := by
  let P := CoordinateTransport.povm (CoordinateTransport.copyEquiv (splitEquiv S) N) M
  change Measurable (fun z : Matrix.unitaryGroup ι ℂ × Ω => ∑ b,
    (∑ a, (copyUnitary z.1 N : Matrix _ _ ℂ) i a * P.effect z.2 a b) *
      star ((copyUnitary z.1 N : Matrix _ _ ℂ) j b))
  have hU (a b : Fin N → ι) : Measurable (fun z : Matrix.unitaryGroup ι ℂ × Ω =>
      (copyUnitary z.1 N : Matrix _ _ ℂ) a b) :=
    (copyUnitary_entry_measurable N a b).comp measurable_fst
  apply Finset.measurable_sum Finset.univ
  intro b _
  apply Measurable.mul
  · apply Finset.measurable_sum Finset.univ
    intro a _
    exact (hU i a).mul ((P.entry_measurable a b).comp measurable_snd)
  · exact Complex.continuous_conj.measurable.comp (hU j b)

end SplitTransport


/-- Physical block-experiment data at a fixed macro-copy budget. No risk,
Fisher, success or protocol-equivalence proposition is a field. -/
structure Branch (ι : Type*) [Fintype ι] [DecidableEq ι] (N : ℕ) (S : Finset ι) where
  Outcome : Type
  outcomeMeasurable : MeasurableSpace Outcome
  measurement : @DominatedPOVM (Fin N → (Active S ⊕ Inactive S)) Outcome _ _ outcomeMeasurable
  output : Outcome → Matrix (Active S) (Active S) ℂ
  measurable_output : Measurable output
  output_psd : ∀ y, (output y).PosSemidef
attribute [instance] Branch.outcomeMeasurable

section Family
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {N : ℕ}
local instance activeLabelMeasurableSpace : MeasurableSpace (Finset ι) := ⊤
local instance split_nonempty (S : Finset ι) : Nonempty (Active S ⊕ Inactive S) :=
  ⟨(splitEquiv S).symm (Classical.choice inferInstance)⟩
variable (B : ∀ S : Finset ι, Branch ι N S)
local instance branchOutcomeFamilyMeasurable : ∀ S : Finset ι, MeasurableSpace ((B S).Outcome) :=
  fun S => (B S).outcomeMeasurable

abbrev Control := Finset ι × Matrix.unitaryGroup ι ℂ
abbrev Outcome := ∀ S : Finset ι, (B S).Outcome

def branchProbability (S : Finset ι) := CollectiveFilterComposition.probabilityVersion (B S).measurement
instance branchProbability_isProbabilityMeasure (S : Finset ι) :
    IsProbabilityMeasure (branchProbability B S).reference :=
  CollectiveFilterComposition.probabilityVersion_reference_probability _

def reference : Measure (Outcome B) := Measure.pi (fun S => (branchProbability B S).reference)
instance reference_isProbabilityMeasure : IsProbabilityMeasure (reference B) := by unfold reference; infer_instance

def effect (h : Control (ι := ι)) (y : Outcome B) : Matrix (Fin N → ι) (Fin N → ι) ℂ :=
  (ambientMeasurement h.1 h.2 (branchProbability B h.1)).effect (y h.1)

lemma effect_entry_measurable (i j : Fin N → ι) :
    Measurable (fun z : Control (ι := ι) × Outcome B => effect B z.1 z.2 i j) := by
  have hm : Measurable (fun z : Finset ι × (Matrix.unitaryGroup ι ℂ × Outcome B) =>
      (ambientMeasurement z.1 z.2.1 (branchProbability B z.1)).effect (z.2.2 z.1) i j) := by
    apply measurable_from_prod_countable_right
    intro S
    let P := CoordinateTransport.povm (CoordinateTransport.copyEquiv (splitEquiv S) N) (branchProbability B S)
    change Measurable (fun z : Matrix.unitaryGroup ι ℂ × Outcome B => ∑ b,
      (∑ a, (copyUnitary z.1 N : Matrix _ _ ℂ) i a * P.effect (z.2 S) a b) *
        star ((copyUnitary z.1 N : Matrix _ _ ℂ) j b))
    have hU (a b : Fin N → ι) : Measurable (fun z : Matrix.unitaryGroup ι ℂ × Outcome B =>
        (copyUnitary z.1 N : Matrix _ _ ℂ) a b) :=
      (copyUnitary_entry_measurable N a b).comp measurable_fst
    apply Finset.measurable_sum Finset.univ
    intro b _
    apply Measurable.mul
    · apply Finset.measurable_sum Finset.univ
      intro a _
      exact (hU i a).mul ((P.entry_measurable a b).comp
        ((measurable_pi_apply S).comp measurable_snd))
    · exact Complex.continuous_conj.measurable.comp (hU j b)

  have hc : Measurable (fun z : Control (ι := ι) × Outcome B => (z.1.1,(z.1.2,z.2))) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have heq : (fun z : Control (ι := ι) × Outcome B => effect B z.1 z.2 i j) =
      ((fun z : Finset ι × (Matrix.unitaryGroup ι ℂ × Outcome B) =>
        (ambientMeasurement z.1 z.2.1 (branchProbability B z.1)).effect (z.2.2 z.1) i j) ∘
        (fun z : Control (ι := ι) × Outcome B => (z.1.1,(z.1.2,z.2)))) := rfl
  rw [heq]
  exact hm.comp hc

lemma effect_positive_ae (h : Control (ι := ι)) :
    ∀ᵐ y ∂reference B, (effect B h y).PosSemidef := by
  apply ae_of_ae_map (μ := reference B) (f := Function.eval h.1)
    (p := fun y : (B h.1).Outcome =>
      ((ambientMeasurement h.1 h.2 (branchProbability B h.1)).effect y).PosSemidef)
    (measurable_pi_apply h.1).aemeasurable
  unfold reference
  rw [(measurePreserving_eval (fun S => (branchProbability B S).reference) h.1).map_eq]
  exact (ambientMeasurement h.1 h.2 (branchProbability B h.1)).positive_ae

lemma effect_entry_integrable (h : Control (ι := ι)) (i j : Fin N → ι) :
    Integrable (fun y => effect B h y i j) (reference B) := by
  exact integrable_comp_eval (μ := fun S => (branchProbability B S).reference) (i := h.1)
    ((ambientMeasurement h.1 h.2 (branchProbability B h.1)).entry_integrable i j)

lemma effect_total (h : Control (ι := ι)) (i j : Fin N → ι) :
    (∫ y, effect B h y i j ∂reference B) = (1 : Matrix (Fin N → ι) (Fin N → ι) ℂ) i j := by
  change (∫ y, (fun u : (B h.1).Outcome =>
    (ambientMeasurement h.1 h.2 (branchProbability B h.1)).effect u i j) (y h.1)
      ∂Measure.pi (fun S => (branchProbability B S).reference)) = _
  rw [integral_comp_eval (μ := fun S => (branchProbability B S).reference) (i := h.1)
    ((ambientMeasurement h.1 h.2 (branchProbability B h.1)).entry_integrable i j).aestronglyMeasurable]
  exact (ambientMeasurement h.1 h.2 (branchProbability B h.1)).total i j

/-- The genuinely normalized measurement for each active-set/unitary control,
using a single parameter-free probability reference for every control. -/
def measurement (h : Control (ι := ι)) : DominatedPOVM (Fin N → ι) (Outcome B) where
  reference := reference B
  reference_finite := inferInstance
  effect := effect B h
  entry_measurable i j := by
    have hc : Measurable (fun y : Outcome B => (h,y)) := measurable_const.prodMk measurable_id
    have heq : (fun y : Outcome B => effect B h y i j) =
        ((fun z : Control (ι := ι) × Outcome B => effect B z.1 z.2 i j) ∘
          (fun y : Outcome B => (h,y))) := rfl
    rw [heq]
    exact (effect_entry_measurable B i j).comp hc
  positive_ae := effect_positive_ae B h
  entry_integrable := effect_entry_integrable B h
  total := effect_total B h

/-- One macro-step on an actual Ncopy input; joint control measurability and
Born Markov normalization follow from the actual effects. -/
def step : AdaptiveModel.OneCopyStep (Fin N → ι) (Control (ι := ι)) (Outcome B) where
  reference := ProbabilityTheory.Kernel.const _ (reference B)
  reference_sfinite := inferInstance
  effect := effect B
  entry_measurable := effect_entry_measurable B
  positive_ae := effect_positive_ae B
  entry_integrable := effect_entry_integrable B
  total := effect_total B

/-- Every returned block is an actual PSD matrix. The multiscale update reads
only the active block; other coordinates are harmless auxiliary randomness. -/
def estimateFamily (y : Outcome B) : ∀ S : Finset ι, {C : Matrix (Active S) (Active S) ℂ // C.PosSemidef} :=
  fun S => ⟨(B S).output (y S), (B S).output_psd _⟩

lemma measurable_estimateFamily : Measurable (estimateFamily B) := by
  apply measurable_pi_lambda
  intro S
  exact ((B S).measurable_output.comp (measurable_pi_apply S)).subtype_mk

/-- Exact conditional Born integration under the actual controlled macro
measurement. The right side is the original canonical branch law. -/
theorem lintegral_branch (h : Control (ι := ι)) (ρ : Density ι)
    (g : (B h.1).Outcome → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g (y h.1) ∂(measurement B h).outcomeMeasure (TensorCopies.density ρ N)) =
      ∫⁻ u, g u ∂(B h.1).measurement.outcomeMeasure
        (TensorCopies.density (splitState h.1 h.2 ρ) N) := by
  have hb := ((measurement B h).born_measurable (TensorCopies.density ρ N)).ennreal_ofReal
  rw [DominatedPOVM.outcomeMeasure, lintegral_withDensity_eq_lintegral_mul _ hb
    (show Measurable (fun y : Outcome B => g (y h.1)) from hg.comp (measurable_pi_apply h.1))]
  let P := branchProbability B h.1
  let σ := TensorCopies.density (splitState h.1 h.2 ρ) N
  let f : (B h.1).Outcome → ℝ≥0∞ := fun u => ENNReal.ofReal (P.born σ u) * g u
  have hf : Measurable f := (P.born_measurable σ).ennreal_ofReal.mul hg
  have he : ∀ y : Outcome B, (measurement B h).born (TensorCopies.density ρ N) y = P.born σ (y h.1) := by
    intro y
    exact ambient_born h.1 h.2 P ρ (y h.1)
  simp_rw [he]
  change (∫⁻ y, f (y h.1) ∂reference B) = _
  calc
    _ = ∫⁻ u, f u ∂P.reference := by
      rw [← lintegral_map hf (measurable_pi_apply h.1)]
      exact congrArg (fun ν : Measure ((B h.1).Outcome) => ∫⁻ u, f u ∂ν)
        (measurePreserving_eval (fun S => (branchProbability B S).reference) h.1).map_eq
    _ = ∫⁻ u, g u ∂P.outcomeMeasure σ := by
      rw [DominatedPOVM.outcomeMeasure,
        lintegral_withDensity_eq_lintegral_mul _ (P.born_measurable σ).ennreal_ofReal hg]
      rfl
    _ = _ := by
      change (∫⁻ u, g u ∂(CollectiveFilterComposition.probabilityVersion
        (B h.1).measurement).outcomeMeasure σ) = _
      rw [CollectiveFilterComposition.probabilityVersion_outcomeMeasure]


lemma step_bornKernel (h : Control (ι := ι)) (ρ : Density ι) :
    (step B).bornKernel (TensorCopies.density ρ N) h =
      (measurement B h).outcomeMeasure (TensorCopies.density ρ N) := by
  rw [AdaptiveModel.OneCopyStep.bornKernel_apply]
  rfl

/-- A control's observed branch has exactly its original continuous output
law. This is an actual Born-measure equality, not a protocol assumption. -/
theorem eval_outcomeMeasure (h : Control (ι := ι)) (ρ : Density ι) :
    ((measurement B h).outcomeMeasure (TensorCopies.density ρ N)).map (Function.eval h.1) =
      (B h.1).measurement.outcomeMeasure (TensorCopies.density (splitState h.1 h.2 ρ) N) := by
  apply Measure.ext
  intro T hT
  rw [Measure.map_apply (show Measurable (Function.eval h.1 : Outcome B → (B h.1).Outcome) from measurable_pi_apply h.1) hT]
  have hg : Measurable (T.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hT
  have he := lintegral_branch B h ρ (T.indicator (fun _ => (1 : ℝ≥0∞))) hg
  have hm : MeasurableSet (Function.eval h.1 ⁻¹' T) := (show Measurable (Function.eval h.1 : Outcome B → (B h.1).Outcome) from measurable_pi_apply h.1) hT
  have hi : (fun y : Outcome B => T.indicator (fun _ => (1 : ℝ≥0∞)) (y h.1)) =
      (Function.eval h.1 ⁻¹' T).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext y
    rfl
  rw [hi, lintegral_indicator hm, lintegral_indicator hT] at he
  simpa only [lintegral_const, Measure.restrict_apply_univ, one_mul] using he

/-- Any measurable branch success event is transported exactly to the
history-controlled native Born kernel. -/
theorem branch_event (h : Control (ι := ι)) (ρ : Density ι)
    (T : Set ((B h.1).Outcome)) (hT : MeasurableSet T) :
    (step B).bornKernel (TensorCopies.density ρ N) h (Function.eval h.1 ⁻¹' T) =
      (B h.1).measurement.outcomeMeasure (TensorCopies.density (splitState h.1 h.2 ρ) N) T := by
  rw [step_bornKernel]
  rw [← eval_outcomeMeasure B h ρ, Measure.map_apply (show Measurable (Function.eval h.1 : Outcome B → (B h.1).Outcome) from measurable_pi_apply h.1) hT]

end Family


end Paper26.CollectiveStageRoutine
