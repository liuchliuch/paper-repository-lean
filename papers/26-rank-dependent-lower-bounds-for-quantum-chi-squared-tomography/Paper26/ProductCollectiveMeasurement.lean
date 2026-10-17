import Paper26.CoordinateTransport
import Paper26.AdaptiveCollectiveEmbedding
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Actual independent batches of a collective measurement

The tensor effects, product reference, positivity, normalization and Born
product laws are constructed from a genuine dominated POVM. No independence
or product-Born assertion is an external field. Coordinate regrouping then
places independent `n`-copy batches on exactly `n*l` actual input copies.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.ProductCollectiveMeasurement
open QuantumModel ContinuousPOVM CollectiveModel CoordinateTransport

variable {Γ Ω : Type*} [Fintype Γ] [DecidableEq Γ] [MeasurableSpace Ω]

/-- A tensor product of possibly different actual density matrices. -/
def productDensity {l : ℕ} (ρ : Fin l → Density Γ) : Density (Fin l → Γ) where
  matrix := TensorSLD.tensor (fun j => (ρ j).matrix)
  positive := AdaptiveCollectiveEmbedding.tensor_posSemidef _ (fun j => (ρ j).positive)
  trace_one := by rw [TensorSLD.tensor_trace]; simp only [Density.trace_one, Finset.prod_const_one]

/-- The actual independent product measurement, with finite product reference. -/
def productPOVM (M : DominatedPOVM Γ Ω) (l : ℕ) :
    DominatedPOVM (Fin l → Γ) (Fin l → Ω) where
  reference := Measure.pi (fun _ : Fin l => M.reference)
  reference_finite := inferInstance
  effect y := TensorSLD.tensor (fun j => M.effect (y j))
  entry_measurable x z := Finset.measurable_prod Finset.univ (fun j _ =>
    (M.entry_measurable (x j) (z j)).comp (measurable_pi_apply j))
  positive_ae := by
    have he : ∀ j : Fin l, ∀ᵐ y ∂Measure.pi (fun _ : Fin l => M.reference),
        (M.effect (y j)).PosSemidef := fun j =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin l => M.reference) (i := j)).eventually M.positive_ae
    filter_upwards [Filter.eventually_all.mpr he] with y hy
    exact AdaptiveCollectiveEmbedding.tensor_posSemidef _ hy
  entry_integrable x z := Integrable.fin_nat_prod
    (fun j => M.entry_integrable (x j) (z j))
  total x z := by
    change (∫ y : Fin l → Ω, ∏ j, M.effect (y j) (x j) (z j)
      ∂Measure.pi (fun _ : Fin l => M.reference)) = _
    rw [integral_fin_nat_prod_eq_prod (μ := fun _ : Fin l => M.reference)
      (fun j y => M.effect y (x j) (z j))]
    simp_rw [M.total]
    exact congrArg (fun B : Matrix (Fin l → Γ) (Fin l → Γ) ℂ => B x z) (TensorSLD.tensor_one l)

/-- The complex trace product is an everywhere identity, even at exceptional
null outcomes where an original effect need not be Hermitian. -/
theorem product_complexBorn (M : DominatedPOVM Γ Ω) {l : ℕ}
    (ρ : Fin l → Density Γ) (y : Fin l → Ω) :
    (productPOVM M l).complexBorn (productDensity ρ) y =
      ∏ j, M.complexBorn (ρ j) (y j) := by
  change Matrix.trace (TensorSLD.tensor (fun j => (ρ j).matrix) *
    TensorSLD.tensor (fun j => M.effect (y j))) = _
  rw [← TensorSLD.tensor_mul, TensorSLD.tensor_trace]
  rfl

theorem product_born_of_positive (M : DominatedPOVM Γ Ω) {l : ℕ}
    (ρ : Fin l → Density Γ) (y : Fin l → Ω)
    (hy : ∀ j, (M.effect (y j)).PosSemidef) :
    (productPOVM M l).born (productDensity ρ) y = ∏ j, M.born (ρ j) (y j) := by
  have hc (j : Fin l) : M.complexBorn (ρ j) (y j) = (M.born (ρ j) (y j) : ℂ) := by
    apply Complex.ext
    · rfl
    · exact EnergyReality.trace_hermitian_product_im _ _ (ρ j).hermitian.eq (hy j).isHermitian.eq
  change ((productPOVM M l).complexBorn (productDensity ρ) y).re = _
  rw [product_complexBorn]
  simp_rw [hc]
  rw [← Complex.ofReal_prod]
  rfl

/-- For arbitrary dominated POVMs, the real Born product identity holds on
the full-measure set of positive effects, which is sufficient for exact laws. -/
theorem product_born_ae (M : DominatedPOVM Γ Ω) {l : ℕ} (ρ : Fin l → Density Γ) :
    (productPOVM M l).born (productDensity ρ) =ᵐ[Measure.pi (fun _ : Fin l => M.reference)]
      (fun y => ∏ j, M.born (ρ j) (y j)) := by
  have he : ∀ j : Fin l, ∀ᵐ y ∂Measure.pi (fun _ : Fin l => M.reference),
      (M.effect (y j)).PosSemidef := fun j =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin l => M.reference) (i := j)).eventually M.positive_ae
  filter_upwards [Filter.eventually_all.mpr he] with y hy
  exact product_born_of_positive M ρ y hy

theorem outcomeMeasure_eq_ofReal_integral (M : DominatedPOVM Γ Ω) (ρ : Density Γ)
    (S : Set Ω) (hS : MeasurableSet S) :
    M.outcomeMeasure ρ S = ENNReal.ofReal (∫ y in S, M.born ρ y ∂M.reference) := by
  rw [M.outcomeMeasure_apply ρ hS]
  exact (ofReal_integral_eq_lintegral_ofReal ((M.born_integrable ρ).restrict (s := S))
    (ae_restrict_of_ae (M.born_nonneg_ae ρ))).symm

/-- The outcome law of the actual tensor measurement is the actual product
of the individual Born laws, for arbitrary measurable outcome spaces. -/
theorem product_outcomeMeasure (M : DominatedPOVM Γ Ω) {l : ℕ} (ρ : Fin l → Density Γ) :
    (productPOVM M l).outcomeMeasure (productDensity ρ) =
      Measure.pi (fun j => M.outcomeMeasure (ρ j)) := by
  apply (Measure.pi_eq (μ := fun j => M.outcomeMeasure (ρ j)) ?_).symm
  intro S hS
  rw [outcomeMeasure_eq_ofReal_integral _ _ _ (MeasurableSet.univ_pi hS)]
  change ENNReal.ofReal (∫ y in Set.univ.pi S, (productPOVM M l).born (productDensity ρ) y
    ∂Measure.pi (fun _ : Fin l => M.reference)) = _
  have he := integral_congr_ae
    (ae_restrict_of_ae (s := Set.univ.pi S) (product_born_ae M ρ))
  rw [he, Measure.restrict_pi_pi]
  rw [integral_fin_nat_prod_eq_prod (μ := fun j => M.reference.restrict (S j))
    (fun j y => M.born (ρ j) y)]
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ =>
    integral_nonneg_of_ae (ae_restrict_of_ae (M.born_nonneg_ae (ρ j))))]
  apply Finset.prod_congr rfl
  intro j _
  exact (outcomeMeasure_eq_ofReal_integral M (ρ j) (S j) (hS j)).symm

/-- Batch and within-batch positions enumerate exactly `n*l` copies. -/
def batchIndex (n l : ℕ) : (Fin l × Fin n) ≃ Fin (n * l) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm l n))

/-- Regrouped tensor basis, with no extra tensor sites or padding. -/
def batchEquiv {ι : Type*} (n l : ℕ) :
    (Fin l → Fin n → ι) ≃ (Fin (n * l) → ι) where
  toFun x k := x ((batchIndex n l).symm k).1 ((batchIndex n l).symm k).2
  invFun x j k := x (batchIndex n l (j, k))
  left_inv x := by ext j k; simp
  right_inv x := by ext k; simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem batch_matrix (A : Matrix ι ι ℂ) (n l : ℕ) :
    CoordinateTransport.matrix (batchEquiv n l)
      (TensorCopies.matrix (TensorCopies.matrix A n) l) = TensorCopies.matrix A (n * l) := by
  ext x y
  change (∏ j : Fin l, ∏ k : Fin n, A (x (batchIndex n l (j, k)))
    (y (batchIndex n l (j, k)))) = ∏ k : Fin (n * l), A (x k) (y k)
  rw [← Fintype.prod_prod_type (fun p : Fin l × Fin n =>
    A (x (batchIndex n l p)) (y (batchIndex n l p)))]
  exact (batchIndex n l).prod_comp (fun k => A (x k) (y k))

theorem batch_density (ρ : Density ι) (n l : ℕ) :
    density (batchEquiv n l) (productDensity (fun _ : Fin l => TensorCopies.density ρ n)) =
      TensorCopies.density ρ (n * l) := by
  apply CommonCenter.density_eq_of_matrix
  exact batch_matrix ρ.matrix n l

theorem povm_outcomeMeasure (e : Γ ≃ (Fin l → ι)) (M : DominatedPOVM Γ Ω) (ρ : Density Γ) :
    (CoordinateTransport.povm e M).outcomeMeasure (density e ρ) = M.outcomeMeasure ρ := by
  change M.reference.withDensity (fun y => ENNReal.ofReal
    ((CoordinateTransport.povm e M).born (density e ρ) y)) = _
  simp only [CoordinateTransport.povm_born]
  rfl

variable {n : ℕ}

/-- The full independent-batch measurement is an actual `n*l`-copy POVM. -/
def batchedMeasurement (A : Learner ι Ω n) (l : ℕ) :
    DominatedPOVM (Fin (n * l) → ι) (Fin l → Ω) :=
  CoordinateTransport.povm (batchEquiv n l) (productPOVM A.measurement l)

@[simp] theorem batchedMeasurement_reference (A : Learner ι Ω n) (l : ℕ) :
    (batchedMeasurement A l).reference = Measure.pi (fun _ : Fin l => A.measurement.reference) := rfl

theorem batched_born_ae (A : Learner ι Ω n) (l : ℕ) (ρ : Density ι) :
    (batchedMeasurement A l).born (TensorCopies.density ρ (n * l))
      =ᵐ[Measure.pi (fun _ : Fin l => A.measurement.reference)]
        (fun y => ∏ j, A.born ρ (y j)) := by
  filter_upwards [product_born_ae A.measurement
    (fun _ : Fin l => TensorCopies.density ρ n)] with y hy
  change (CoordinateTransport.povm (batchEquiv n l) (productPOVM A.measurement l)).born
    (TensorCopies.density ρ (n * l)) y = _
  rw [← batch_density ρ n l, CoordinateTransport.povm_born]
  exact hy

theorem batched_outcomeMeasure (A : Learner ι Ω n) (l : ℕ) (ρ : Density ι) :
    (batchedMeasurement A l).outcomeMeasure (TensorCopies.density ρ (n * l)) =
      Measure.pi (fun _ : Fin l => A.outcomeMeasure ρ) := by
  rw [← batch_density ρ n l]
  unfold batchedMeasurement
  rw [povm_outcomeMeasure, product_outcomeMeasure]
  rfl

/-- The actual tuple of outputs reconstructed by the original estimator. -/
def outputs (A : Learner ι Ω n) (l : ℕ) (y : Fin l → Ω) : Fin l → Density ι :=
  fun j => A.estimator.estimate (y j)

theorem measurable_outputs (A : Learner ι Ω n) (l : ℕ) : Measurable (outputs A l) :=
  measurable_pi_lambda _ (fun j => A.estimator.measurable_estimate.comp (measurable_pi_apply j))

/-- The reconstructed densities themselves, not just abstract trial data,
have the independent product of the original learner's actual output laws. -/
theorem outputs_law (A : Learner ι Ω n) (l : ℕ) (ρ : Density ι) :
    ((batchedMeasurement A l).outcomeMeasure (TensorCopies.density ρ (n * l))).map (outputs A l) =
      Measure.pi (fun _ : Fin l => A.outputMeasure ρ) := by
  rw [batched_outcomeMeasure]
  exact Measure.pi_map_pi (fun _ => A.estimator.measurable_estimate.aemeasurable)

/-- Evaluation at a measurable finite selected index is measurable even
when the underlying outcome space is arbitrary. -/
theorem measurable_selected (l : ℕ) (select : (Fin l → Ω) → Fin l) (hs : Measurable select) :
    Measurable (fun y : Fin l → Ω => y (select y)) := by
  have he : Measurable (fun z : (Fin l → Ω) × Fin l => z.1 z.2) :=
    measurable_from_prod_countable_left (fun j => measurable_pi_apply j)
  exact he.comp (measurable_id.prodMk hs)

/-- Any measurable index selection of the batch outcomes yields a genuine
`n*l`-copy density estimator, ready for metric amplification. -/
def selectedLearner (A : Learner ι Ω n) (l : ℕ)
    (select : (Fin l → Ω) → Fin l) (hs : Measurable select) :
    Learner ι (Fin l → Ω) (n * l) where
  measurement := batchedMeasurement A l
  estimator :=
    { estimate y := A.estimator.estimate (y (select y))
      measurable_estimate := A.estimator.measurable_estimate.comp (measurable_selected l select hs) }

theorem selectedLearner_outcomeMeasure (A : Learner ι Ω n) (l : ℕ)
    (select : (Fin l → Ω) → Fin l) (hs : Measurable select) (ρ : Density ι) :
    (selectedLearner A l select hs).outcomeMeasure ρ =
      Measure.pi (fun _ : Fin l => A.outcomeMeasure ρ) := batched_outcomeMeasure A l ρ

theorem selectedLearner_outputMeasure (A : Learner ι Ω n) (l : ℕ)
    (select : (Fin l → Ω) → Fin l) (hs : Measurable select) (ρ : Density ι) :
    (selectedLearner A l select hs).outputMeasure ρ =
      (Measure.pi (fun _ : Fin l => A.outcomeMeasure ρ)).map
        (fun y => A.estimator.estimate (y (select y))) := by
  unfold Learner.outputMeasure
  rw [selectedLearner_outcomeMeasure]
  rfl

theorem selectedLearner_successProbability (A : Learner ι Ω n) (l : ℕ)
    (select : (Fin l → Ω) → Fin l) (hs : Measurable select)
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞) :
    (selectedLearner A l select hs).successProbability loss ρ ε =
      (Measure.pi (fun _ : Fin l => A.outcomeMeasure ρ))
        {y | loss ρ (A.estimator.estimate (y (select y))) ≤ ε} := by
  unfold Learner.successProbability
  rw [selectedLearner_outcomeMeasure]
  rfl

end Paper26.ProductCollectiveMeasurement
